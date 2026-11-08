;;; Typed hygienic macros, in FX-26: each typed macro's templates checked
;;; once, where it is defined (`macros.rs`'s `template_checks`;
;;; `typed-macros.md`, "Proposed: typed holes"), each template as a
;;; procedure over its holes, a hidden definition the checker checks as it
;;; checks any. On top of the expander (`macros.fx`), which it loads and
;;; gives on (`macros-module`), so that the parser's instance is one.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define macros-module ((proj (load-module "fx26:macros.fx") rs re rm rc rp)))
(define files-module (with macros-module files-module))
(define align-module (with files-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-symbol len nth mk-list mk-symbol
        (type syns-a) (effect parses))
(import types-module fail-at split (type fails))
(import align-module defined macro-of pvar-of atm-var lv-rib
        (type macro clause clauses pvars levels atms))
(import macros-module transcribe checking fresh-count list-at bound-of (type binds))

;;; ------------------------------------------------------------ checking templates

;; The checks of macro `n`'s templates, once, where it is defined
;; (`Macros::template_checks`; `typed-macros.md`, "Proposed: typed holes"):
;; for each clause whose parts are typed, a hidden definition of the
;; template as a procedure over its holes, each hole a parameter called
;; where the template places it, `(subr E (U …) T)`, given the template's
;; binders in its scope, of the `bvar`s' types; each part left out a binder
;; of the procedure's `plambda`. Checked as any definition is.
(define template-checks (->* (fails symbol) syns-a)
  (lambda (fail n)
    (let ((m (car (macro-of n (get defined))))) (checks-of fail n m (extract m 2)))))
(define checks-of (->* (fails symbol macro clauses) syns-a)
  (lambda (fail n m cs)
    (cond ((null? cs) nil)
          ((untyped? (extract (car cs) 4)) (checks-of fail n m (cdr cs)))
          (else (let ((c (template-check fail n m (car cs))))
                  (cons c (checks-of fail n m (cdr cs))))))))
(define untyped? (->* (pvars) bool)
  (lambda (ps) (or (null? ps) (and (null? (extract (extract (car ps) 2) 4)) (untyped? (cdr ps))))))
(define-type params (tupleof syns-a binds syns-a))
(define template-check (->* (fails symbol macro clause) syn)
  (lambda (fail n m c)
    (let* ((template (extract c 2)) (a (syn-start template)) (b (syn-end template))
           (binders (bvar-binds fail c (extract c 4) nil))
           (made (hole-params fail c (extract c 4) a b (tuple (the syns-a nil) binders
                                                              (extract m 3))))
           (body (begin (set checking #t)
                        (let ((x (transcribe c template nil (extract made 2) 0)))
                          (begin (set checking #f) x))))
           (params (extract made 1)) (poly (extract made 3))
           (lam (mk-list (list (mk-symbol "lambda" a b) (list-at a b 0 params nil) body) a b))
           (proc (if (null? poly)
                     lam
                     (mk-list (list (mk-symbol "plambda" a b) (mk-list poly a b) lam) a b)))
           (hidden (fresh-symbol (string-append "%template:" (symbol->string n) ":"))))
      (mk-list (list (mk-symbol "define" a b) (atom hidden a b 0) proc) a b))))
;; A name made fresh: `prefix` and the count.
(define fresh-symbol (->* (string) symbol)
  (lambda (prefix)
    (begin (set fresh-count (+ (get fresh-count) 1))
           (string->symbol (string-append prefix (int->string (get fresh-count)))))))
;; Where pattern variable `n` is in clause `c`'s pattern (else the pattern).
(define pattern-place (->* (clause symbol) syn)
  (lambda (c n)
    (let ((found (symbol-in (extract c 1) n))) (if (null? found) (extract c 1) (car found)))))
(define symbol-in (->* (syn symbol) syns-a)
  (lambda (s n)
    (cond ((syn-symbol? s) (if (symbol=? (syn-symbol s) n) (list s) nil))
          ((null? (split s)) nil)
          (else (let ((first (symbol-in (car (split s)) n)))
                  (if (null? first) (symbol-in (nth (split s) 1) n) first))))))
;; Each binder of the clause a fresh name, for the holes in its scope to be
;; given; any part but an `expr` or a `bvar`, refused.
(define bvar-binds (->* (fails clause pvars binds) binds)
  (lambda (fail c ps out)
    (if (null? ps)
        out
        (let* ((n (extract (car ps) 1))
               (k ((with types-module kind-of) (extract (extract (car ps) 2) 1))))
          (cond ((= k 0) (bvar-binds fail c (cdr ps) out))
                ((= k 1)
                 (let ((f (fresh-symbol (string-append "%" (symbol->string n) ":"))))
                   (bvar-binds fail c (cdr ps)
                               (append out (the binds (list (tuple n (mk-symbol (symbol->string f)
                                                                                0 0))))))))
                (else
                 (begin
                   (fail-at fail (string-append "`" (symbol->string n) "` is not an `expr` or a "
                                                "`bvar`: a macro whose parts are typed is checked "
                                                "once, of those alone, not yet")
                            (pattern-place c n))
                   out)))))))
;; Each hole's parameter, and its call bound to it, onto `acc`: its
;; parameters, the bindings, the `plambda`'s binders.
(define hole-params (->* (fails clause pvars int int params) params)
  (lambda (fail c ps a b acc)
    (if (null? ps)
        acc
        (let* ((n (extract (car ps) 1)) (info (extract (car ps) 2)) (h (extract info 4))
               (shown (symbol->string n)))
          (cond
            ((not (= ((with types-module kind-of) (extract info 1)) 0))
             (hole-params fail c (cdr ps) a b acc))
            ((null? h)
             (begin (fail-at fail (string-append "`" shown "` has no type or effect, and another "
                                                 "part of this macro does: a macro whose parts "
                                                 "are typed is checked once, each `expr` part "
                                                 "typed")
                             (pattern-place c n))
                    acc))
            (else
             (let* ((scope (hole-scope fail c n (reverse (extract info 2)) (extract c 4)))
                    (ty (hole-part (extract (car h) 1) "type" shown a b))
                    (eff (hole-part (extract (car h) 2) "effect" shown a b))
                    (hole (mk-symbol (symbol->string (fresh-symbol (string-append "%h:" shown ":")))
                                     a b))
                    (subr (mk-list (list (mk-symbol "subr" a b) (car eff)
                                         (list-at a b 0 (scope-types scope) nil) (car ty))
                                   a b))
                    (call (list-at a b 0 (cons hole (scope-calls scope (extract acc 2))) nil))
                    (acc2 (tuple (append (extract acc 1)
                                         (the syns-a (list (mk-list (list hole subr) a b))))
                                 (append (extract acc 2) (the binds (list (tuple n call))))
                                 (append (extract acc 3) (append (cdr ty) (cdr eff))))))
               (hole-params fail c (cdr ps) a b acc2))))))))
;; A hole's type or effect: as written, or a binder of `kind` named for the
;; hole `n` (`%type-of-e`), what a message about it says, in a list with
;; that binder.
(define hole-part (->* (syns-a string string int int) syns-a)
  (lambda (given kind n a b)
    (if (not (null? given))
        (list (car given))
        (let ((v (mk-symbol (string-append "%" kind "-of-" n) a b)))
          (list v (mk-list (list v (mk-symbol kind a b)) a b))))))
;; The binders in the scope of hole `n`, outermost first (`levels`), each a
;; typed `bvar`: its name and type.
(define-type scope-vars (listof (tupleof symbol syn) acyclic))
(define hole-scope (->* (fails clause symbol levels pvars) scope-vars)
  (lambda (fail c n levels ps)
    (if (null? levels)
        nil
        (tagcase (car levels)
          (lv-rib (as) (append (rib-scope fail c n as ps) (hole-scope fail c n (cdr levels) ps)))
          (else y
            (begin (fail-at fail (string-append "`" (symbol->string n) "` is in the scope of a "
                                                "part's ribcage: not yet where a macro's parts "
                                                "are typed")
                            (pattern-place c n))
                   (the scope-vars nil)))))))
(define rib-scope (->* (fails clause symbol atms pvars) scope-vars)
  (lambda (fail c n as ps)
    (if (null? as)
        nil
        (tagcase (car as)
          (atm-var (v)
            (let* ((info (pvar-of v ps)) (h (if (null? info) nil (extract (car info) 4))))
              (if (or (null? h) (null? (extract (car h) 1)))
                  (begin (fail-at fail (string-append "`" (symbol->string v)
                                                      "` binds a variable `" (symbol->string n)
                                                      "` is in the scope of: its type is written, "
                                                      "`(bvar #:type T)`, where a macro's parts "
                                                      "are typed")
                                  (pattern-place c v))
                         (the scope-vars nil))
                  (cons (tuple v (car (extract (car h) 1))) (rib-scope fail c n (cdr as) ps)))))
          (else y
            (begin (fail-at fail (string-append "`" (symbol->string n) "` is in the scope of the "
                                                "binders a part exports: not yet where a macro's "
                                                "parts are typed")
                            (pattern-place c n))
                   (the scope-vars nil)))))))
(define scope-types (->* (scope-vars) syns-a)
  (lambda (vs) (if (null? vs) nil (cons (extract (car vs) 2) (scope-types (cdr vs))))))
(define scope-calls (->* (scope-vars binds) syns-a)
  (lambda (vs bs)
    (if (null? vs) nil (append (bound-of (extract (car vs) 1) bs) (scope-calls (cdr vs) bs)))))
