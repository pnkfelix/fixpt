;;; Typed hygienic macros, in FX-26: syntax aligned with syntax types, as a
;;; tree of nodes, walked for what binds what (Herman's rules), and a
;;; macro's clause checked against its signature, as the Rust expander has
;;; them (`macros.rs`). Part of the expander (`macros.fx`, which loads it,
;;; and takes `types-module`, the one instance of `macros-types.fx`, from
;;; it, so that every part sees one table of `mu`s); the macros defined and
;;; the nodes are `macros-nodes.fx`'s, which this file gives on.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define nodes-module ((proj (load-module "fx26:macros-nodes.fx") rs re rm rc rp)))
(define types-module (with nodes-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom (type syn))
(import parser-module syn-start syn-end syn-symbol? syn-name syn-symbol len nth syn-string?
        (type syns-a names) (effect parses))
(import types-module fail-at split syn-nil? syn-keyword? show-syn reserved-syn? reserved? unfold
        fits? sub? kind-of simple-kind? lambda-shaped? proper? kernel-sigs kernel-definitions
        scope-sigs scope-definitions syn-number? s-item bind-shape ring-shape
        bind-rib bind-cage bind-direct bind-earlier
        ring-rib ring-at s-expr s-bvar s-id s-dvar s-kind
        s-data s-type s-label s-nil s-literal s-pair s-import s-export s-mu s-many s-union s-typed
        mu-body addr=? name-in? proper-items desc-word? atm-var atm-rib-of atm-lit sorted-strings
        seq-elem seq-cage? peel ellipsis? ellipsis-of name-fit-of name-kind?
        joined
        (type fails addr entries ring rings bind sty stys named hole atm atms strings))
(import nodes-module act-rename act-alias act-module-type
        act-standard-type act-macro-head defined macro-of macro? makes-defns? makes-top-defns?
        makes-desc? makes k-pair k-nil k-pvar k-binder k-ref k-form k-desc k-seq k-other atom-at
        nnodes node-syn node-path node-core node-kids node-many? node-hole
        with-core with-kids with-import with-export with-many with-hole node-new
        node-imports node-export
        nodes-reset! repeated repeated! seq-depths repeated? cage-seqs cage-seq? int-member?
        desc-roots binds-nothing?
        pvar-of pvar? pvar-shape lv-rib lv-cage lv-earlier lv-shape program-walk unplaced
        (type action actions contracts clause clauses macro macro-env scope scopes kids rooted holes
              node pinfo pvars level levels found def-env def-envs env namer looked))
(import nodes-module env-empty env-within env-lookup env-any-shape? env-levels binder-name)
(import nodes-module def-env-top)

;;; ------------------------------------------------------------ aligning

;; `s`, at `path`, aligned with type `t`, in `mode` (0 a pattern, 1 a
;; template, 2 a use); `root`, the node its addresses are from, if not
;; itself (-1): its node.
(define align (->* (fails int pvars sty syn int addr) int)
  (lambda (fail mode ps t s root path)
    (let ((at (node-new s path t)))
      (begin (fill fail mode ps at t s (if (< root 0) at root)) at))))
;; Node path `p` a step further: in a program's walk, kept innermost step
;; first, so that a step costs one pair however deep (a program's lists may
;; be long); a template's, in order. A signature's address, `addr+`.
(define path+ (->* (addr bool) addr)
  (lambda (p step) (if (get program-walk) (cons step p) (addr+ p step))))
(define addr+ (->* (addr bool) addr) (lambda (p step) (append p (the addr (list step)))))

(define fill (->* (fails int pvars int sty syn int) unit)
  (lambda (fail mode ps at t s root)
    (tagcase t
      (s-import (body b) (begin (with-import at b root) (fill fail mode ps at body s root)))
      (s-many (body) (begin (with-many at) (fill fail mode ps at body s root)))
      (s-typed (body h) (begin (with-hole at h) (fill fail mode ps at body s root)))
      (s-export (body b)
        (if (null? (node-export at))
            (begin (with-export at b root) (fill fail mode ps at body s root))
            (fail-at fail "two exports at one part" s)))
      (else y (fill-core fail mode ps at t s root)))))
(define fill-core (->* (fails int pvars int sty syn int) unit)
  (lambda (fail mode ps at t s root)
    (begin
      (with-core at t)
      ;; A pattern's variable, or one placed in a template: at any type.
      (cond ((and (syn-symbol? s)
                  (or (and (= mode 0) (not (= (kind-of (unfold t)) 7))
                           (not (string=? (syn-name s) "_")) (not (ellipsis? s)))
                      (and (= mode 1) (pvar? (syn-symbol s) ps))))
             ;; A pattern's variable where a name or a list may be: the
             ;; name's shape, if one member is a name's.
             (let ((one (if (= mode 0) (name-fit-of (unfold t)) (the stys nil))))
               (if (null? one)
                   (with-kids at (k-pvar (syn-symbol s)))
                   (fill fail mode ps at (car one) s root))))
            ((and (< mode 2) (not (null? (ellipsis-of s))))
             (fill-seq fail mode ps at t s (car (ellipsis-of s))))
            ((and (< mode 2) (ellipsis? s))
             (fail-at fail "`...` follows the part it repeats, last in a list" s))
            (else (fill-shape fail mode ps at t s root))))))
;; `(x ...)` at `at`, a pattern's or a template's: `x` aligned with the
;; element type of list type `t`, repeated; the list exports what each
;; element does.
(define fill-seq (->* (fails int pvars int sty syn syn) unit)
  (lambda (fail mode ps at t s x)
    (let ((elem (seq-elem t)))
      (if (null? elem)
          (fail-at fail (string-append "`" (show-syn s) "` repeats a part by `...` where the form "
                                       "takes no list of them")
                   s)
          (let ((e (align fail mode ps (car elem) x -1 (path+ (node-path at) #t))))
            (begin
              (repeated! e)
              (tagcase (node-kids e) (k-pvar (n) (seq-member ps e (car elem) x mode)) (else y #u))
              (with-kids at (k-seq e))
              (if (seq-cage? t) (set cage-seqs (cons at (get cage-seqs))) #u)
              (let ((ex (node-export e)))
                (if (or (not (null? (node-export at))) (null? ex))
                    #u
                    (with-export at (extract (car ex) 1) (extract (car ex) 2))))))))))
;; A pattern variable at `e` where elements of more than one shape may be:
;; the shape it fits, and what that exports.
(define seq-member (->* (pvars int sty syn int) unit)
  (lambda (ps e elem x mode)
    (tagcase elem
      (s-union (ms)
        (let ((fit (fitting ms x mode ps)))
          (if (and (not (null? fit)) (null? (cdr fit)))
              (begin (tagcase (car fit) (s-export (b bd) (with-export e bd e)) (else y #u))
                     (with-core e (peel (car fit))))
              #u)))
      (else y #u))))
(define fill-shape (->* (fails int pvars int sty syn int) unit)
  (lambda (fail mode ps at t s root)
    (let ((said (lambda ((why string)) (fail-at fail why s)))
          ;; Written only if refused: `s` may be large.
          (shown (lambda () (string-append "`" (show-syn s) "`"))))
      (tagcase t
        (s-mu (id) (fill fail mode ps at (mu-body id) s at))
        (s-union (ms)
          ;; A program's name that a form's word may be too, `else` or a
          ;; variable bound to `else`: the form's word, if a member writes it.
          (let* ((all (fitting ms s mode ps))
                 (fit (if (and (= mode 3) (not (null? all)) (not (null? (cdr all))))
                          (fitting all s 2 ps)
                          all)))
            (cond ((null? fit) (said (string-append (shown) " is of none of the shapes this part "
                                                    "may have")))
                  ((null? (cdr fit)) (fill fail mode ps at (car fit) s at))
                  (else (said (string-append (shown) " could be of more than one of this part's "
                                             "shapes"))))))
        (s-pair (a d)
          (let ((parts (split s)))
            (if (null? parts)
                (said (string-append (shown) " is not a list as this part must be"))
                (let* ((path (node-path at))
                       (x (align fail mode ps a (car parts) root (path+ path #t)))
                       (y (align fail mode ps d (nth parts 1) root (path+ path #f))))
                  (with-kids at (k-pair x y))))))
        (s-nil ()
          (if (syn-nil? s)
              (with-kids at (k-nil))
              (said (string-append (shown) " is more than this part may have"))))
        (s-literal (n)
          (if (and (syn-symbol? s) (symbol=? (syn-symbol s) n))
              #u
              (said (string-append (shown) " where `" (symbol->string n) "` is written"))))
        (s-bvar () (fill-binder fail mode at s #f))
        (s-dvar () (fill-binder fail mode at s #t))
        (s-kind () #u)
        (s-id ()
          (if (syn-symbol? s)
              (if (writes? mode) (with-kids at (k-ref (syn-symbol s) #f 0)) #u)
              (said (string-append (shown) " is not a variable"))))
        (s-label ()
          (cond ((syn-keyword? s) #u)
                ((and (syn-symbol? s) (>= mode 2)) #u)
                ;; A program's field by position.
                ((and (= mode 3) (syn-number? s)) #u)
                ((syn-symbol? s)
                 (said (string-append "a tag or label in a template is a keyword: `#:"
                                      (syn-name s) "`, not `" (syn-name s) "`")))
                (else (said (string-append (shown) " is not a tag or label")))))
        ;; A template writes a lambda (its form aligned as any of the kernel's);
        ;; a use gives one, of the shape the checkers take.
        (s-lambda ()
          (cond ((= mode 3) (fill fail mode ps at (s-expr) s root))
                ((and (= mode 1) (not (null? (split s))) (syn-symbol? (car (split s)))
                      (string=? (syn-name (car (split s))) "lambda") (proper? s))
                 (form fail ps at s #f))
                ((and (= mode 2) (lambda-shaped? s)) #u)
                (else (said (string-append (shown) " is not a lambda, as this part must be")))))
        (s-expr ()
          (cond ((= mode 3) (program-expr fail ps at s))
                ((reserved-syn? s)
                 (said (string-append "`" (syn-name s) "` is a form's name, not an expression")))
                ;; `#u`, unit: a literal, which the parsers read as a name.
                ((and (syn-symbol? s) (string=? (syn-name s) "#u")) #u)
                ((and (syn-symbol? s) (= mode 1)) (with-kids at (k-ref (syn-symbol s) #f 0)))
                ((and (not (syn-nil? s)) (not (null? (split s))) (= mode 1)) (form fail ps at s #f))
                ((syn-nil? s) (said "`()` is not an expression"))
                (else #u)))
        (s-defn ()
          (if (and (writes? mode) (not (syn-nil? s)) (not (null? (split s))))
              (form fail ps at s #t)
              (said (string-append (shown) " is not a definition"))))
        ;; A description a template writes, name by name; the binders of the
        ;; `poly`s at its top, what it exports (what a definition's type puts
        ;; in scope in what it is defined as).
        (s-type ()
          (if (writes? mode)
              (begin (set desc-roots (cons at (get desc-roots)))
                     (desc fail ps at s)
                     (if (null? (node-export at))
                         (with-export at (bind-direct (poly-binders at ps)) at)
                         #u))
              #u))
        ;; A module's item, as a program's walk takes one: a definition, a
        ;; string (a comment, binding nothing), or an expression.
        (s-item ()
          (cond ((defines? fail s) (form fail ps at s #t))
                ((syn-string? s) (with-export at (bind-rib nil) at))
                (else (fill fail mode ps at (s-expr) s root))))
        ;; `data`.
        (else z
          (let ((inside (pvar-inside s ps)))
            (if (and (= mode 1) (not (null? inside)))
                (said (string-append "pattern variable `" (symbol->string (car inside))
                                     "` inside a quoted datum: only a whole one is placed"))
                #u)))))))
;; A binder at `at`, of a description if `d`, else of a value.
(define fill-binder (->* (fails int int syn bool) unit)
  (lambda (fail mode at s d)
    (cond ((and (syn-symbol? s) (macro? (syn-symbol s)))
           (fail-at fail (string-append "`" (syn-name s) "` is a macro's name, which is not bound")
                    s))
          ;; A program's binder: any name the checkers let it bind, which they
          ;; decide.
          ((and (syn-symbol? s) (= mode 3)) (with-kids at (k-binder (syn-symbol s) d)))
          ;; A value's binder a use gives: as a program's, any name the
          ;; checkers let it bind, a keyword too (`fields`, Heist's), which a
          ;; template's form, read by its head, does not see bound.
          ((and (syn-symbol? s) (= mode 2) (not d)) #u)
          ((and (syn-symbol? s) (not (reserved-syn? s)) (not (and d (desc-word? (syn-name s) #f))))
           (if (= mode 1) (with-kids at (k-binder (syn-symbol s) d)) #u))
          (else (fail-at fail (string-append "`" (show-syn s) "` is not a name that may be bound")
                         s)))))
;; Those of `ms` that `s` fits.
(define fitting (->* (stys syn int pvars) stys)
  (lambda (ms s mode ps)
    (cond ((null? ms) nil)
          ((fits? (car ms) s mode (lambda ((n symbol)) (pvar-shape n ps)))
           (cons (car ms) (fitting (cdr ms) s mode ps)))
          (else (fitting (cdr ms) s mode ps)))))
;; A pattern variable written somewhere inside `s`, in a list of one.
(define pvar-inside (->* (syn pvars) (listof symbol acyclic))
  (lambda (s ps)
    (if (syn-symbol? s)
        (if (pvar? (syn-symbol s) ps) (list (syn-symbol s)) nil)
        (let ((parts (split s)))
          (if (null? parts)
              nil
              (let ((first (pvar-inside (car parts) ps)))
                (if (null? first) (pvar-inside (nth parts 1) ps) first)))))))

;; A form in a template, at node `at`: a kernel form, a macro's use, or an
;; application, aligned with its signature; a definition's, if `defn`,
;; where a template makes definitions, else an expression's.
(define form (->* (fails pvars int syn bool) unit)
  (lambda (fail ps at s defn)
    ;; A program's form, after expansion: its own binding structure.
    (if (get program-walk) (program-form fail ps at s defn) (template-form fail ps at s defn))))
(define template-form (->* (fails pvars int syn bool) unit)
  (lambda (fail ps at s defn)
    (let* ((parts (split s)) (hd (car parts))
           (head (if (and (syn-symbol? hd) (not (pvar? (syn-symbol hd) ps))) (syn-name hd) ""))
           (kernel (kernel-sigs fail)) (defs (kernel-definitions fail))
           (macro (and (not (string=? head "")) (macro? (syn-symbol hd)))))
      (cond
        ;; A procedural macro (`macros-procedural.fx`): no signature says
        ;; what it binds.
        ((and macro (= (makes (syn-symbol hd)) 3))
         (fail-at fail (string-append "`" head "` is a procedural macro, whose binding structure "
                                      "no signature says: not in a template")
                  s))
        (defn
         (cond ((and macro (makes-defns? (syn-symbol hd))) (macro-operands fail ps at hd parts))
               ((and macro (makes-desc? (syn-symbol hd)))
                (not-definition fail s (string-append "them by a macro that makes definitions, "
                                                      "not a description's")))
               (macro (not-definition fail s (string-append "them by a macro that makes "
                                                            "definitions, not an expression's")))
               ((and (not (string=? head "")) (not (null? (sig-of (string->symbol head) defs))))
                (operands fail ps at (car (sig-of (string->symbol head) defs)) (nth parts 1)))
               (else (not-definition fail s (string-append "`define`, `define*`, `define-rec`, a "
                                                           "`begin` of them, or a use of another "
                                                           "such")))))
        ;; A keyword at a list's head constructs, a tag written or placed.
        ((constructs? hd ps)
         (with-kids at (k-form (align fail 1 ps (car (sig-of '%construct kernel)) s -1
                                      (node-path at)))))
        ((and macro (makes-defns? (syn-symbol hd)))
         (fail-at fail (string-append "`" head "` makes definitions, which are made at the top "
                                      "level, not where an expression is")
                  s))
        ((and macro (makes-desc? (syn-symbol hd)))
         (fail-at fail (string-append "`" head "` makes a description, not an expression") s))
        ((and (not (string=? head "")) (not (null? (sig-of (string->symbol head) defs)))
              (null? (sig-of (string->symbol head) kernel)))
         (fail-at fail (string-append "`" head "` makes a definition, made at the top level by a "
                                      "macro that makes definitions, not where an expression is")
                  s))
        ((string=? head "with")
         (cond ((standard-with? s) #u)
               ;; `(with m name)`: the value `name` of module `m`, a
               ;; template's binder or a use's, the name as written; `m`'s
               ;; or refused, where it is checked (`macros.fx`'s
               ;; `projections`).
               ((and (= (len (proper-items s)) 3) (syn-symbol? (nth (proper-items s) 1))
                     (syn-symbol? (nth (proper-items s) 2)))
                (let ((x (align fail 1 ps (s-pair (s-id) (s-pair (s-data) (s-nil))) (nth parts 1)
                                -1 (path+ (node-path at) #f))))
                  (begin
                    (tagcase (node-kids x)
                      (k-pair (m y)
                        (tagcase (node-kids m)
                          (k-ref (n d f) (with-kids m (k-ref n d 3)))
                          (else z #u)))
                      (else y #u))
                    (with-kids at (k-form x)))))
               (else
                (fail-at fail (string-append "a template's `with` is `(with module name)`, the "
                                             "value `name` of the module, or `(with #%fx name)` or "
                                             "`(with #%toplevel name)` (one opening a module over "
                                             "a body waits for scopes of a module's names)")
                         s))))
        (macro (macro-operands fail ps at hd parts))
        ((and (not (string=? head "")) (not (string=? (substring head 0 1) "%"))
              (not (null? (sig-of (string->symbol head) kernel))))
         (operands fail ps at (car (sig-of (string->symbol head) kernel)) (nth parts 1)))
        ;; A form the kernel has not, but `scope-forms`, that binds
        ;; nothing (`bloblet-ref`, `TODO.md` §247).
        ((and (not (string=? head ""))
              (let ((sig (sig-of (string->symbol head) (scope-sigs fail))))
                (and (not (null? sig)) (binds-nothing? (car sig) nil))))
         (operands fail ps at (car (sig-of (string->symbol head) (scope-sigs fail))) (nth parts 1)))
        ((and (not (string=? head "")) (reserved? head))
         (fail-at fail (string-append "the prototype does not know `" head "`'s binding "
                                      "structure: not yet in a template")
                  s))
        (else
         (with-kids at (k-form (align fail 1 ps (car (sig-of '%app kernel)) s -1
                                      (node-path at)))))))))
;; Whether nodes of `mode` are written, their binders and references found:
;; a template's, a program's.
(define writes? (->* (int) bool) (lambda (mode) (or (= mode 1) (= mode 3))))

;;; ------------------------------------------------------------ programs

;; A program's expression `s` at `at`, after expansion: a name referred to
;; (but the literals the parsers read as names), or a form.
(define program-expr (->* (fails pvars int syn) unit)
  (lambda (fail ps at s)
    (cond ((syn-symbol? s)
           (if (let ((n (syn-symbol s)))
                 (or (symbol=? n '|#t|) (symbol=? n '|#f|) (symbol=? n '|#u|)))
               #u
               (with-kids at (k-ref (syn-symbol s) #f 0))))
          ((syn-nil? s) (fail-at fail "`()` is not an expression" s))
          ((not (null? (split s))) (form fail ps at s #f))
          (else #u))))
;; Whether `s` is a definition, by its head: a `begin` one if all it holds
;; are (`macros.rs`'s `defines`).
(define defines? (->* (fails syn) bool)
  (lambda (fail s)
    (let* ((items (proper-items s))
           (head (if (and (not (null? items)) (syn-symbol? (car items))) (syn-name (car items))
                   "")))
      (cond ((string=? head "") #f)
            ((string=? head "begin") (and (not (null? (cdr items))) (all-define? fail (cdr items))))
            (else (let ((n (syn-symbol (car items))))
                    (or (not (null? (sig-of n (kernel-definitions fail))))
                        (not (null? (sig-of n (scope-definitions fail)))))))))))
(define all-define? (->* (fails syns-a) bool)
  (lambda (fail xs) (or (null? xs) (and (defines? fail (car xs)) (all-define? fail (cdr xs))))))
;; A program's form at `at`: its binding structure, the kernel's or
;; `scope-forms`'; a reserved word at its head with none, an application,
;; as the checkers take it (`macros.rs`'s `Aligner::form`, `Mode::Program`).
(define program-form (->* (fails pvars int syn bool) unit)
  (lambda (fail ps at s defn)
    (let* ((parts (split s)) (hd (car parts))
           (n (if (syn-symbol? hd) (syn-symbol hd) (string->symbol "")))
           (kernel (kernel-sigs fail)) (sforms (scope-sigs fail))
           (defs (kernel-definitions fail)) (sdefs (scope-definitions fail)))
      (cond
        (defn
         (cond ((and (symbol=? n 'module-parameters) (= (len (proper-items s)) 2))
                (operands-as fail 3 ps at (parameters-sig (nth (proper-items s) 1)) (nth parts 1)))
               ((not (null? (sig-of n defs))) (operands-as fail 3 ps at (car (sig-of n defs))
                                                (nth parts 1)))
               ((not (null? (sig-of n sdefs)))
                (operands-as fail 3 ps at (car (sig-of n sdefs)) (nth parts 1)))
               (else (not-definition fail s "a definition of the kernel's"))))
        ((syn-keyword? hd)
         (with-kids at (k-form (align fail 3 ps (car (sig-of '%construct kernel)) s -1
                                      (node-path at)))))
        ((and (symbol=? n 'quasiquote) (= (len (proper-items s)) 2))
         (with-kids at (k-desc (unquoted fail ps (nth (proper-items s) 1)
                                         (path+ (path+ (node-path at) #f) #t) 1 nil))))
        ((and (symbol=? n 'with) (standard-with? s)) #u)
        ((not (null? (sig-of n sforms)))
         (operands-as fail 3 ps at (car (sig-of n sforms)) (nth parts 1)))
        ;; Of the kernel's, not one the expander writes, `%app` or
        ;; `%construct`, named so.
        ((and (not (null? (sig-of n kernel))) (not (name-in? n (percent-named kernel))))
         (operands-as fail 3 ps at (car (sig-of n kernel)) (nth parts 1)))
        (else (with-kids at (k-form (align fail 3 ps (car (sig-of '%app kernel)) s -1
                                            (node-path at)))))))))
;; The names of `kernel`'s forms that start with `%`, found once.
(define percent-named (->* (named) names)
  (lambda (kernel)
    (begin
      (if (get percent-found) #u
          (begin (set percent-names (percent-of kernel)) (set percent-found #t)))
      (get percent-names))))
(define percent-found (ref bool rs) (new #f))
(define percent-names (ref names rs) (new nil))
(define percent-of (->* (named) names)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((let ((h (symbol->string (extract (car ns) 1))))
             (and (> (string-length h) 0) (string=? (substring h 0 1) "%")))
           (cons (extract (car ns) 1) (percent-of (cdr ns))))
          (else (percent-of (cdr ns))))))
;; The operands `rest` of the form at `at`, aligned with its signature, in
;; `mode`.
(define operands-as (->* (fails int pvars int sty syn) unit)
  (lambda (fail mode ps at sig rest)
    (with-kids at (k-form (align fail mode ps sig rest -1 (path+ (node-path at) #f))))))
;; The expressions a quasiquote's datum `s`, at `path`, unquotes at `depth`
;; 1, each aligned, onto `kids` (the last first, given back first first):
;; a nested `quasiquote` deepens, an `unquote` or `unquote-splicing`
;; shallows, as R7RS counts (`macros.rs`'s `unquoted`).
(define unquoted (->* (fails pvars syn addr int (listof int acyclic)) (listof int acyclic))
  (lambda (fail ps s path depth kids)
    (the (listof int acyclic) (reverse (unquoted-onto fail ps s path depth kids)))))
(define unquoted-onto (->* (fails pvars syn addr int (listof int acyclic)) (listof int acyclic))
  (lambda (fail ps s path depth kids)
    (tagcase s
      (lst (items d a b x)
        (let ((head (if (and (not (null? items)) (syn-symbol? (car items)))
                        (syn-name (car items))
                        ""))
              (inner (path+ (path+ path #f) #t)))
          (cond ((and (= (len items) 2) (= depth 1)
                      (or (string=? head "unquote") (string=? head "unquote-splicing")))
                 (cons (align fail 3 ps (s-expr) (nth items 1) -1 inner) kids))
                ((and (= (len items) 2) (or (string=? head "unquote") (string=? head
                                                                        "unquote-splicing")))
                 (unquoted-onto fail ps (nth items 1) inner (- depth 1) kids))
                ((and (= (len items) 2) (string=? head "quasiquote"))
                 (unquoted-onto fail ps (nth items 1) inner (+ depth 1) kids))
                (else (unquoted-items fail ps items path depth kids)))))
      (dotted (items tail d a b x)
        (unquoted-onto fail ps tail (falses path (len items)) depth
                       (unquoted-items fail ps items path depth kids)))
      (vec (items d a b x)
        (begin (if (any-unquotes? items) (set unplaced (symbols-onto items (get unplaced))) #u)
          kids))
      (else y kids))))
(define unquoted-items (->* (fails pvars syns-a addr int (listof int acyclic)) (listof int acyclic))
  (lambda (fail ps items path depth kids)
    (if (null? items)
        kids
        (unquoted-items fail ps (cdr items) (path+ path #f) depth
                        (unquoted-onto fail ps (car items) (path+ path #t) depth kids)))))
(define falses (->* (addr int) addr)
  (lambda (path k) (if (= k 0) path (falses (path+ path #f) (- k 1)))))
(define addr-falses (->* (addr int) addr)
  (lambda (a k) (if (= k 0) a (addr-falses (addr+ a #f) (- k 1)))))
;; Whether one of `xs` has an `unquote` or `unquote-splicing` in it.
(define any-unquotes? (->* (syns-a) bool)
  (lambda (xs) (and (not (null? xs)) (or (unquotes? (car xs)) (any-unquotes? (cdr xs))))))
(define unquotes? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (any-unquotes? items))
      (dotted (items tail d a b x) (or (any-unquotes? items) (unquotes? tail)))
      (vec (items d a b x) (any-unquotes? items))
      (else y (and (syn-symbol? s) (or (string=? (syn-name s) "unquote")
                                       (string=? (syn-name s) "unquote-splicing")))))))
;; Each name in `xs`, onto `out`: names a walk leaves unplaced.
(define symbols-onto (->* (syns-a names) names)
  (lambda (xs out)
    (if (null? xs)
        out
        (symbols-onto (cdr xs)
                      (tagcase (car xs)
                        (lst (items d a b x) (symbols-onto items out))
                        (dotted (items tail d a b x) (symbols-onto (cons tail items) out))
                        (vec (items d a b x) (symbols-onto items out))
                        (else y (if (syn-symbol? (car xs)) (cons (syn-symbol (car xs)) out)
                                  out)))))))
;; The binding structure of a program's `module-parameters`' list `bs`:
;; each a value's binder, its type in the scope of those before it, or a
;; description's; each module not `qualified` included in the items, as the
;; checkers make the file (`macros.rs`'s `parameters_sig`).
(define parameters-sig (->* (syn) sty)
  (lambda (bs)
    (let ((ps (proper-items bs)))
      (s-export (s-pair (parameters-list ps) (s-nil))
                (bind-cage (cons (ring-rib (parameter-entries ps 0)) (parameter-shapes ps 0)))))))
(define parameters-list (->* (syns-a) sty)
  (lambda (ps)
    (if (null? ps)
        (s-nil)
        (s-pair (s-union (list (if (binder-is-kind? (car ps))
                                   (s-export (s-pair (s-dvar) (s-data))
                                             (bind-rib (list (tuple (list #t) 4))))
                                   (s-export (s-pair (s-bvar) (s-pair (s-type) (s-data)))
                                             (bind-rib (list (tuple (list #t) 1)))))))
                (parameters-list (cdr ps))))))
(define parameter-entries (->* (syns-a int) entries)
  (lambda (ps k)
    (if (null? ps)
        nil
        (cons (tuple (cons #t (addr+ (addr-falses nil k) #t)) 2)
              (parameter-entries (cdr ps) (+ k 1))))))
(define parameter-shapes (->* (syns-a int) rings)
  (lambda (ps k)
    (cond ((null? ps) nil)
          ((or (binder-is-kind? (car ps)) (not (= (len (proper-items (car ps))) 2)))
           (parameter-shapes (cdr ps) (+ k 1)))
          (else (cons (ring-shape (cons #t (addr+ (addr+ (addr-falses nil k) #t) #t)))
                      (parameter-shapes (cdr ps) (+ k 1)))))))
;; Whether module parameter `b` binds a description, `(name kind)` or `(r
;; region p)`; else it is `(m T)` or `(m T qualified)`, a module
;; (`parse::binder_is_kind`).
(define binder-is-kind? (->* (syn) bool)
  (lambda (b)
    (let ((parts (proper-items b)))
      (cond ((= (len parts) 2) (kind-form? (nth parts 1)))
            ((= (len parts) 3)
             (or (kind-form? (nth parts 1))
                 (not (and (syn-symbol? (nth parts 2)) (string=? (syn-name (nth parts 2))
                                                         "qualified")))))
            (else #t)))))
(define kind-form? (->* (syn) bool)
  (lambda (k)
    (let ((parts (proper-items k)))
      (if (not (null? parts))
          (and (syn-symbol? (car parts)) (string=? (syn-name (car parts)) "=>"))
          (and (syn-symbol? k)
               (name-in? (syn-symbol k)
                         (list 'region 'place 'effect 'type 'data 'sendable 'flat 'size 'conv)))))))

;; Whether a list headed by `hd` constructs: a keyword, or a pattern
;; variable of a `label`.
(define constructs? (->* (syn pvars) bool)
  (lambda (hd ps)
    (or (syn-keyword? hd)
        (and (syn-symbol? hd) (pvar? (syn-symbol hd) ps)
             (= (kind-of (extract (car (pvar-of (syn-symbol hd) ps)) 1)) 5)))))
;; The operands of the use of macro `hd` at `at`, aligned with its signature.
(define macro-operands (->* (fails pvars int syn syns-a) unit)
  (lambda (fail ps at hd parts)
    (operands fail ps at (extract (car (macro-of (syn-symbol hd) (get defined))) 1)
              (nth parts 1))))
(define not-definition (->* (fails syn string) unit)
  (lambda (fail s what)
    (fail-at fail (string-append "`" (show-syn s) "` is not a definition: a macro that makes "
                                 "definitions makes " what)
             s)))
;; The operands `rest` of the form at `at`, aligned with its signature.
(define operands (->* (fails pvars int sty syn) unit)
  (lambda (fail ps at sig rest)
    (with-kids at (k-form (align fail 1 ps sig rest -1 (path+ (node-path at) #f))))))
(define sig-of (->* (symbol named) stys)
  (lambda (n named)
    (cond ((null? named) nil)
          ((symbol=? n (extract (car named) 1)) (list (extract (car named) 2)))
          (else (sig-of n (cdr named))))))
;; Whether `s` is `(with #%fx name)` or `(with #%toplevel name)`.
(define standard-with? (->* (syn) bool)
  (lambda (s)
    (tagcase s
      (lst (items d a b x)
        (and (= (len items) 3) (syn-symbol? (nth items 1)) (syn-symbol? (nth items 2))
             (or (string=? (syn-name (nth items 1)) "#%fx")
                 (string=? (syn-name (nth items 1)) "#%toplevel"))))
      (else y #f))))

;;; ------------------------------------------------------------ descriptions

;; The `i`th of nodes `ks`.
(define kid (->* ((listof int acyclic) int) int)
  (lambda (ks i) (if (= i 0) (car ks) (kid (cdr ks) (- i 1)))))
;; Description `s`, which a template writes, at node `at`, aligned name by
;; name (`macros.rs`'s `Aligner::desc`): each name referred to in the
;; description namespace, the top level's if the template does not bind it;
;; but a word of descriptions written as it is, a pattern variable placed,
;; and what `poly`, `dlambda`, `mu` and `dletrec` bind in scope in what
;; follows. Labels, a `restrict`'s names and an `io` effect's kind are
;; written as they are; `(globals g …)`'s names and `(select m n)`'s module
;; are values.
(define desc (->* (fails pvars int syn) unit)
  (lambda (fail ps at s)
    (tagcase s
      (lst (items d a b x) (if (null? items) #u (desc-list fail ps at s items)))
      (dotted (items tail d a b x) (fail-at fail "a description is a list, not a dotted one" s))
      (else y
        (if (syn-symbol? s)
            (let ((n (syn-symbol s)))
              (with-kids at (cond ((pvar? n ps) (k-pvar n))
                                  ((desc-word? (syn-name s) #f) (k-other))
                                  (else (k-ref n #t 1)))))
            #u)))))
(define desc-list (->* (fails pvars int syn syns-a) unit)
  (lambda (fail ps at s items)
    (if (and (syn-symbol? (car items)) (not (pvar? (syn-symbol (car items)) ps))
             (macro? (syn-symbol (car items))))
        (desc-use fail ps at s (syn-symbol (car items)))
        (desc-items fail ps at s items))))
;; A macro's use where a description is: its operands aligned with its
;; signature, if it makes a description.
(define desc-use (->* (fails pvars int syn symbol) unit)
  (lambda (fail ps at s n)
    (if (makes-desc? n)
        (with-kids at (k-form (align fail 1 ps (extract (car (macro-of n (get defined))) 1)
                                     (nth (split s) 1) -1 (path+ (node-path at) #f))))
        (fail-at fail (string-append "`" (symbol->string n) "` makes "
                                     (if (makes-defns? n) "definitions" "an expression")
                                     ", not a description")
                 s))))
(define desc-items (->* (fails pvars int syn syns-a) unit)
  (lambda (fail ps at s items)
    (let* ((kids (desc-kids at items)) (h (car items))
           (head (if (and (syn-symbol? h) (not (pvar? (syn-symbol h) ps))) (syn-name h) ""))
           (not-yet (lambda ((what string))
                      (fail-at fail (string-append what " in a template's description: not yet")
                               s))))
      (cond
        ;; A program's `poly` of several descriptions after its binders.
        ((and (or (string=? head "poly") (string=? head "dlambda")) (get program-walk)
              (> (len items) 3))
         (desc-each-scoped fail ps (cdr (cdr kids)) (cdr (cdr items))
                           (desc-binders fail ps (kid kids 1) (nth items 1))))
        ((or (string=? head "poly") (string=? head "dlambda"))
         (if (= (len items) 3)
             (desc-scoped fail ps (kid kids 2) (nth items 2)
                          (desc-binders fail ps (kid kids 1) (nth items 1)))
             (fail-at fail (string-append "`(" head " ((name kind) …) description)`") s)))
        ((string=? head "mu")
         (if (= (len items) 3)
             (desc-scoped fail ps (kid kids 2) (nth items 2)
                          (list (desc-binder fail ps (kid kids 1) (nth items 1))))
             (fail-at fail "`(mu name type)`" s)))
        ((string=? head "dletrec")
         (if (= (len items) 3)
             (desc-dletrec fail ps kids items)
             (fail-at fail "`(dletrec ((name description) …) description)`" s)))
        ((or (string=? head "productof") (string=? head "sumof"))
         (desc-fields fail ps (cdr kids) (cdr items)))
        ((and (string=? head "restrict") (>= (len items) 2))
         (desc fail ps (kid kids 1) (nth items 1)))
        ((string=? head "io") #u)
        ;; Values: a global's name, written as it is, since no local can
        ;; shadow it; a module's, the top level's.
        ((string=? head "globals") (desc-values fail ps (cdr kids) 2))
        ((string=? head "select")
         (desc-values fail ps (if (null? (cdr kids)) nil (list (kid kids 1))) 1))
        ;; A file's module type, given descriptions and module values, which
        ;; a name alone does not tell apart: the checker decides by what
        ;; binds it, so a program's walk leaves the names unplaced.
        ((and (get program-walk)
              (or (string=? head "load-moduleof") (string=? head "load-input-moduleof")))
         (set unplaced (symbols-onto (cdr (cdr items)) (get unplaced))))
        ;; A program's: each member's type in the scope of the abstract and
        ;; transparent types before it, a value's name a label.
        ((and (get program-walk) (string=? head "moduleof"))
         (desc-members fail ps (cdr kids) (cdr items) nil))
        ((string=? head "moduleof") (not-yet "a `moduleof`"))
        ((or (string=? head "subr") (string=? head "->") (string=? head "->*"))
         (desc-subr fail ps s items kids))
        ((and (not (string=? head "")) (desc-word? head #t))
         (desc-each fail ps (cdr kids) (cdr items)))
        ;; A description function applied, its name the head.
        (else (desc-each fail ps kids items))))))
(define desc-each (->* (fails pvars (listof int acyclic) syns-a) unit)
  (lambda (fail ps ks xs)
    (if (or (null? xs) (null? ks))
        #u
        (begin (desc fail ps (car ks) (car xs)) (desc-each fail ps (cdr ks) (cdr xs))))))
;; A node for each of `items`, the parts of the list at node `at`, at their
;; paths in it: `at`'s kids.
(define desc-kids (->* (int syns-a) (listof int acyclic))
  (lambda (at items)
    ;; `p ...` last: `p` repeated, the `...` no part of its own.
    (let* ((n (len items)) (again (and (>= n 2) (ellipsis? (nth items (- n 1)))))
           (kids (desc-kids-from (if again (the syns-a (reverse (cdr (reverse items)))) items)
                                 (node-path at) nil)))
      (begin
        (if (and again (not (null? kids)))
            (repeated! (car (the (listof int acyclic) (reverse kids))))
            #u)
        (with-kids at (k-desc kids))
        kids))))
(define desc-kids-from (->* (syns-a addr (listof int acyclic)) (listof int acyclic))
  (lambda (items path out)
    (if (null? items)
        (the (listof int acyclic) (reverse out))
        (let ((k (node-new (car items) (path+ path #t) (s-type))))
          (desc-kids-from (cdr items) (path+ path #f) (cons k out))))))
;; Description `s` at node `at`, in the scope of `as`.
(define desc-scoped (->* (fails pvars int syn atms) unit)
  (lambda (fail ps at s as) (begin (with-import at (bind-direct as) at) (desc fail ps at s))))
;; A description's binder `n`, at node `at`: a pattern variable (a `dvar`
;; the use gives), or a name the template binds; what it binds.
(define desc-binder (->* (fails pvars int syn) atm)
  (lambda (fail ps at n) (begin (with-core at (s-dvar)) (name-binder fail ps at n #t))))
;; A value's binder `n` a description writes (a procedure type's parameter
;; named, its result's name), at node `at`: a pattern variable (a `bvar` the
;; use gives), or a name the template binds; what it binds.
(define value-binder (->* (fails pvars int syn) atm)
  (lambda (fail ps at n) (begin (with-core at (s-bvar)) (name-binder fail ps at n #f))))
;; Binder `n` at node `at`, a description's if `d`, else a value's.
(define name-binder (->* (fails pvars int syn bool) atm)
  (lambda (fail ps at n d)
    (begin
      (cond ((and (syn-symbol? n) (pvar? (syn-symbol n) ps))
             (begin (with-kids at (k-pvar (syn-symbol n))) (atm-var (syn-symbol n) d 0)))
            ((and (syn-symbol? n)
                  (or (get program-walk)
                      (and (not (reserved-syn? n)) (not (desc-word? (syn-name n) #f)))))
             (begin (with-kids at (k-binder (syn-symbol n) d)) (atm-lit at d)))
            (else (begin (fail-at fail (string-append "`" (show-syn n) "` is not a name that may "
                                                      "be bound")
                                  n)
                         (atm-lit at d)))))))
;; `((name kind) …)` at node `at`, a binder's place or `distinct` third if
;; any, each in the scope of those before it: what they bind.
(define desc-binders (->* (fails pvars int syn) atms)
  (lambda (fail ps at bs)
    (let ((entries (proper-items bs)))
      (desc-binders-from fail ps (desc-kids at entries) entries nil))))
(define desc-binders-from (->* (fails pvars (listof int acyclic) syns-a atms) atms)
  (lambda (fail ps ks es out)
    (if (or (null? es) (null? ks))
        out
        (let* ((parts (proper-items (car es))) (n (len parts)))
          (if (or (= n 2) (= n 3))
              (let* ((p (desc-kids (car ks) parts))
                     (a (desc-binder fail ps (car p) (car parts))))
                (begin
                  (if (= n 3) (desc-scoped fail ps (kid p 2) (nth parts 2) out) #u)
                  (desc-binders-from fail ps (cdr ks) (cdr es) (append out (the atms (list a))))))
              (begin (fail-at fail "a binder is `(name kind)`" (car es)) out))))))
;; `(dletrec ((name description) …) body)`'s parts: each name in scope in
;; each description and the body.
(define-type dparts (listof (tupleof atm int syn) acyclic))
(define desc-dletrec (->* (fails pvars (listof int acyclic) syns-a) unit)
  (lambda (fail ps kids items)
    (let* ((entries (proper-items (nth items 1)))
           (parts (dletrec-parts fail ps (desc-kids (kid kids 1) entries) entries))
           (as (dparts-atms parts)))
      (begin (dparts-each fail ps parts as) (desc-scoped fail ps (kid kids 2) (nth items 2) as)))))
(define dletrec-parts (->* (fails pvars (listof int acyclic) syns-a) dparts)
  (lambda (fail ps ks es)
    (if (or (null? es) (null? ks))
        nil
        (let ((parts (proper-items (car es))))
          (if (= (len parts) 2)
              (let* ((p (desc-kids (car ks) parts)) (a (desc-binder fail ps (car p) (car parts))))
                (cons (tuple a (kid p 1) (nth parts 1)) (dletrec-parts fail ps (cdr ks) (cdr es))))
              (begin (fail-at fail "`(name description)`" (car es)) (the dparts nil)))))))
(define dparts-atms (->* (dparts) atms)
  (lambda (ds) (if (null? ds) nil (cons (extract (car ds) 1) (dparts-atms (cdr ds))))))
(define dparts-each (->* (fails pvars dparts atms) unit)
  (lambda (fail ps ds as)
    (if (null? ds)
        #u
        (begin (desc-scoped fail ps (extract (car ds) 2) (extract (car ds) 3) as)
               (dparts-each fail ps (cdr ds) as)))))
;; `(label type)`s at nodes `ks`.
(define desc-fields (->* (fails pvars (listof int acyclic) syns-a) unit)
  (lambda (fail ps ks fs)
    (if (or (null? fs) (null? ks))
        #u
        (let ((parts (proper-items (car fs))))
          (if (= (len parts) 2)
              (let ((p (desc-kids (car ks) parts)))
                (begin
                  ;; A label a use gives, placed.
                  (if (and (syn-symbol? (car parts)) (pvar? (syn-symbol (car parts)) ps))
                      (begin (with-core (car p) (s-label))
                             (with-kids (car p) (k-pvar (syn-symbol (car parts)))))
                      #u)
                  (desc fail ps (kid p 1) (nth parts 1))
                  (desc-fields fail ps (cdr ks) (cdr fs))))
              ;; A program's flat sum's tag type, `(sumof u8 …)`.
              (if (get program-walk)
                  (begin (desc fail ps (car ks) (car fs)) (desc-fields fail ps (cdr ks) (cdr fs)))
                  (fail-at fail "`(label type)`" (car fs))))))))
;; Descriptions `xs` at nodes `ks`, each in the scope of `as`.
(define desc-each-scoped (->* (fails pvars (listof int acyclic) syns-a atms) unit)
  (lambda (fail ps ks xs as)
    (if (or (null? xs) (null? ks))
        #u
        (begin (desc-scoped fail ps (car ks) (car xs) as)
               (desc-each-scoped fail ps (cdr ks) (cdr xs) as)))))
;; A program's `moduleof`'s members `ms` at nodes `ks`: each's type in the
;; scope of `as`, the abstract and transparent types before it.
(define desc-members (->* (fails pvars (listof int acyclic) syns-a atms) unit)
  (lambda (fail ps ks ms as)
    (if (or (null? ms) (null? ks))
        #u
        (let* ((parts (proper-items (car ms)))
               (word (if (and (not (null? parts)) (syn-symbol? (car parts)))
                         (syn-name (car parts))
                         "")))
          (if (< (len parts) 2)
              (begin (desc fail ps (car ks) (car ms)) (desc-members fail ps (cdr ks) (cdr ms) as))
              (let ((p (desc-kids (car ks) parts)))
                (begin
                  (desc-each-scoped fail ps (cdr (cdr p)) (cdr (cdr parts)) as)
                  (desc-members fail ps (cdr ks) (cdr ms)
                                (if (and (or (string=? word "abs") (string=? word "desc"))
                                         (syn-symbol? (nth parts 1)))
                                    (append as (the atms (list (desc-binder fail ps (kid p 1)
                                                                 (nth parts 1)))))
                                    as)))))))))
;; A procedure type, `(subr …)`, `(-> …)` or `(->* …)`, its parts `items`
;; at nodes `kids` (`macros.rs`'s `desc_subr`): each parameter named, `(x :
;; T)`, a value's binder in scope in the types after it, the result and the
;; specification's clauses, and a repeated one's in its own type only as
;; the repetitions before it bound it, which a name cannot say; `(ensures r
;; Q)`'s `r` in scope in `Q`. A `(bool …)` result's propositions are written
;; as they are.
(define desc-subr (->* (fails pvars syn syns-a (listof int acyclic)) unit)
  (lambda (fail ps s items kids)
    (let ((plain (- (len items) (clauses-at-end (reverse items)))))
      (if (or (< plain 3) (not (= (len-kids kids) (len items))))
          (fail-at fail (string-append "`(subr effect (param …) result)` or `(-> (param …) "
                                       "result)`, then a specification's clauses")
                   s)
          (desc-subr-parts fail ps kids items 0 (- plain 2) nil)))))
(define len-kids (->* ((listof int acyclic)) int)
  (lambda (ks) (if (null? ks) 0 (+ 1 (len-kids (cdr ks))))))
(define spec-clause? (->* (syn) bool)
  (lambda (c)
    (let ((parts (proper-items c)))
      (and (not (null? parts)) (syn-symbol? (car parts))
           (or (string=? (syn-name (car parts)) "requires")
               (string=? (syn-name (car parts)) "ensures"))))))
(define clauses-at-end (->* (syns-a) int)
  (lambda (rs)
    (if (and (not (null? rs)) (spec-clause? (car rs))) (+ 1 (clauses-at-end (cdr rs))) 0)))
;; The `i`th part on, the parameters the `pi`th; `as`, what the parameters
;; before bind.
(define desc-subr-parts (->* (fails pvars (listof int acyclic) syns-a int int atms) unit)
  (lambda (fail ps ks xs i pi as)
    (cond ((or (null? ks) (null? xs)) #u)
          ((= i pi)
           (desc-subr-parts fail ps (cdr ks) (cdr xs) (+ i 1) pi
                            (desc-params fail ps (car ks) (car xs))))
          (else
           (begin
             (cond ((= i 0) #u)
                   ((< i pi) (desc fail ps (car ks) (car xs)))
                   ((= i (+ pi 1)) (desc-result fail ps (car ks) (car xs) as))
                   (else (desc-clause fail ps (car ks) (car xs) as)))
             (desc-subr-parts fail ps (cdr ks) (cdr xs) (+ i 1) pi as))))))
(define desc-params (->* (fails pvars int syn) atms)
  (lambda (fail ps at s)
    (cond ((syn-nil? s) nil)
          ((null? (proper-items s))
           (begin (fail-at fail "a procedure type's parameters are a list" s) nil))
          (else (desc-params-from fail ps (desc-kids at (proper-items s)) (proper-items s) nil)))))
(define desc-params-from (->* (fails pvars (listof int acyclic) syns-a atms) atms)
  (lambda (fail ps ks xs as)
    (if (or (null? ks) (null? xs))
        as
        (let ((parts (proper-items (car xs))))
          (if (and (= (len parts) 3) (syn-symbol? (nth parts 1))
                   (string=? (syn-name (nth parts 1)) ":"))
              (let* ((q (desc-kids (car ks) parts)) (a (value-binder fail ps (car q) (car parts))))
                (begin
                  (with-import (kid q 2) (bind-direct as) (kid q 2))
                  (if (repeated? (car ks))
                      (with-import (kid q 2) (bind-earlier (list a)) (kid q 2))
                      #u)
                  (desc fail ps (kid q 2) (nth parts 2))
                  (desc-params-from fail ps (cdr ks) (cdr xs) (append as (the atms (list a))))))
              (begin (desc-scoped fail ps (car ks) (car xs) as)
                     (desc-params-from fail ps (cdr ks) (cdr xs) as)))))))
(define desc-result (->* (fails pvars int syn atms) unit)
  (lambda (fail ps at r as)
    (let ((parts (proper-items r)))
      (if (and (not (null? parts)) (syn-symbol? (car parts))
               (string=? (syn-name (car parts)) "bool")
               (not (pvar? (syn-symbol (car parts)) ps)))
          (let ((inside (pvar-inside r ps)))
            (if (null? inside)
                #u
                (fail-at fail (string-append "pattern variable `" (symbol->string (car inside))
                                             "` in a `(bool …)` result's propositions: not yet")
                         r)))
          (desc-scoped fail ps at r as)))))
(define desc-clause (->* (fails pvars int syn atms) unit)
  (lambda (fail ps at c as)
    (let* ((parts (proper-items c)) (q (desc-kids at parts)) (head (syn-name (car parts))))
      (cond ((and (string=? head "requires") (= (len-kids q) 2))
             (begin (with-import (kid q 1) (bind-direct as) (kid q 1))
                    (spec fail ps (kid q 1) (nth parts 1))))
            ((and (string=? head "ensures") (= (len-kids q) 3))
             (let ((a (value-binder fail ps (kid q 1) (nth parts 1))))
               (begin (with-import (kid q 2) (bind-direct (append as (the atms (list a))))
                                   (kid q 2))
                      (spec fail ps (kid q 2) (nth parts 2)))))
            (else (fail-at fail (string-append "a specification is `(requires proposition)`, "
                                               "then `(ensures name proposition)`")
                           c))))))
;; A specification's proposition or integer `s`, at node `at`
;; (`macros.rs`'s `spec`): each name a value's, a parameter's or the
;; result's, else the top level's (which the checkers refuse there); a
;; call's head a global procedure's, written as it is, as a `(globals …)`'s
;; names are; the logic's words, numbers, `#t` and `#f` as they are.
(define spec (->* (fails pvars int syn) unit)
  (lambda (fail ps at s)
    (tagcase s
      (lst (items d a b x)
        (if (null? items)
            #u
            (let ((kids (desc-kids at items)) (h (car items)))
              (begin
                (cond ((and (syn-symbol? h) (not (pvar? (syn-symbol h) ps))
                            (logic-word? (syn-name h)))
                       #u)
                      ((syn-symbol? h) (desc-values fail ps (list (car kids)) 2))
                      (else (fail-at fail "a specification's proposition or integer" s)))
                (spec-each fail ps (cdr kids) (cdr items))))))
      (dotted (items tail d a b x)
        (fail-at fail "a specification's proposition is a list, not a dotted one" s))
      (else y (if (syn-symbol? s) (desc-values fail ps (list at) 1) #u)))))
(define spec-each (->* (fails pvars (listof int acyclic) syns-a) unit)
  (lambda (fail ps ks xs)
    (if (or (null? ks) (null? xs))
        #u
        (begin (spec fail ps (car ks) (car xs)) (spec-each fail ps (cdr ks) (cdr xs))))))
(define logic-word? (->* (string) bool)
  (lambda (h)
    (or (string=? h "<") (string=? h "<=") (string=? h "=") (string=? h ">") (string=? h ">=")
        (string=? h "not") (string=? h "and") (string=? h "or") (string=? h "implies")
        (string=? h "+") (string=? h "-") (string=? h "*"))))
;; Names of values at nodes `ks`, each the top level's if free (`free` 1)
;; or as written (2), or a pattern variable placed.
(define desc-values (->* (fails pvars (listof int acyclic) int) unit)
  (lambda (fail ps ks free)
    (if (null? ks)
        #u
        (let ((s (node-syn (car ks))))
          (if (syn-symbol? s)
              (begin
                (with-core (car ks) (s-id))
                (with-kids (car ks) (if (pvar? (syn-symbol s) ps)
                                        (k-pvar (syn-symbol s))
                                        (k-ref (syn-symbol s) #f free)))
                (desc-values fail ps (cdr ks) free))
              (fail-at fail "a name" s))))))
;; The binders of the `poly`s at the top of the description at node `at`,
;; outermost first (`Checker::bind_signature`'s).
(define poly-binders (->* (int pvars) atms)
  (lambda (at ps)
    (let ((items (proper-items (node-syn at))))
      (tagcase (node-kids at)
        (k-desc (kids)
          (if (and (= (len items) 3) (syn-symbol? (car items))
                   (string=? (syn-name (car items)) "poly")
                   (not (pvar? (syn-symbol (car items)) ps)))
              (append (entry-binders (tagcase (node-kids (kid kids 1))
                                       (k-desc (es) es)
                                       (else y (the (listof int acyclic) nil))))
                      (poly-binders (kid kids 2) ps))
              (the atms nil)))
        (else y (the atms nil))))))
(define entry-binders (->* ((listof int acyclic)) atms)
  (lambda (es)
    (if (null? es)
        nil
        (let ((rest (entry-binders (cdr es))))
          (tagcase (node-kids (car es))
            (k-desc (parts)
              (tagcase (node-kids (car parts))
                (k-pvar (n) (cons (atm-var n #t 0) rest))
                (k-binder (n d) (cons (atm-lit (car parts) #t) rest))
                (else y rest)))
            (else y rest))))))
;; The nodes under node `at`, itself first.
(define under (->* (int) (listof int acyclic))
  (lambda (at)
    (cons at (tagcase (node-kids at)
               (k-pair (x y) (append (under x) (under y)))
               (k-form (x) (under x))
               (k-seq (x) (under x))
               (k-desc (xs) (under-each xs))
               (else y (the (listof int acyclic) nil))))))
(define under-each (->* ((listof int acyclic)) (listof int acyclic))
  (lambda (xs) (if (null? xs) nil (append (under (car xs)) (under-each (cdr xs))))))
