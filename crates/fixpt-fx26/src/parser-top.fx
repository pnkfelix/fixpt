;;; The FX-26 parser, in FX-26: top-level forms, and a program of them.
;;; Part of the parser, `parser.fx` first (PLAN.md §11, step 9a).

;;; ------------------------------------------------------------- top level

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
;; The parser's other parts at these regions, the reader's types in them,
;; and what this file uses of them.
(define parser-exps-module ((proj (load-module "fx26:parser-exps.fx") rs re rm rc rp)))
(define parser-module (with parser-exps-module parser-module))
(define parser-ids-module (with parser-module parser-ids-module))
(import parser-ids-module walk-of number-form walk-state walk-count walk-given walk-wrong
        walk-done! (type seen))
(define readings ((proj (load-module "fx26:readings.fx") rs re rm rc)))
(import readings form-reading (type loads))
(define parser-types ((proj (load-module "fx26:parser-types.fx") rs re rm rc rp)))
(import parser-types (type keys keyed loaded-file))
(define reader-types (with parser-module reader-types))
(import reader-types lst (type syn))
(import parser-module parse-tag syn-start syn-end pfail syn-symbol? syn-symbol syn-items len nth
        keep mk-list form-head form-of? datatype? mk-pure-subr mk-poly expand-datatype import?
        expand-import e-var e-lambda t-define t-define-rec t-define-type t-define-effect
        includes-given include-given-at mk-symbol syn-name loaded-error e-module
        (type include-given)
        t-define-convention t-define-syscall t-define-generative t-exp p-ok p-err shared-taken
        shared-reset! loaded input-key?
        (type syns-a exp top param-list top-list presult names) (effect parses))
(import parser-exps-module parse-exp parse-rec-bindings type-loaded)
;; `(define name type expression)` or `(define name expression)`; for a
;; `define*` (`star?`), the type's list holds the head too.
(define parse-define (->* (syn bool) top)
  (lambda (s star?)
    (let* ((items (syn-items s "a definition")) (n (len items)) (a (syn-start s)) (b (syn-end s)))
      (case n ((4)
               (let* ((name (syn-symbol (nth items 1)))
                      (heads (if star? (the syns-a (cons (car items) nil)) (the syns-a nil)))
                      (ty (the syns-a (cons (nth items 2) heads))))
                 (t-define name ty (parse-exp (nth items 3)) a b)))
              ((3)
               (let ((name (syn-symbol (nth items 1))))
                 (t-define name (the syns-a nil) (parse-exp (nth items 2)) a b)))
              (else (pfail "`(define name type expression)` or `(define name expression)`" s))))))
(define parse-top (->* (syn) top)
  (lambda (s)
    (let ((head (form-head s)))
      (case head ((define) (parse-define s #f))
                 ;; `(define* name type lambda)`: its type is a list of it and the
                 ;; head, which says the checker finds what the lambda reads.
                 ((define*) (parse-define s #t))
                 ((define-rec)
                  (let ((items (syn-items s "a group of definitions")))
                    (if (null? (cdr items))
                        (pfail "`(define-rec (name type lambda) …)`" s)
                        (t-define-rec (parse-rec-bindings (cdr items)) (syn-start s) (syn-end s)))))
                 ((define-type)
                  (let ((items (syn-items s "a type definition")))
                    (if (= (len items) 3)
                        (t-define-type (nth items 1) (nth items 2) (syn-start s) (syn-end s))
                        (pfail "`(define-type name type)`" s))))
                 ((define-effect)
                  (let ((items (syn-items s "an effect definition")))
                    (if (= (len items) 3)
                        (t-define-effect (nth items 1) (nth items 2) (syn-start s) (syn-end s))
                        (pfail "`(define-effect name effect)`" s))))
                 ((define-convention)
                  (let ((items (syn-items s "a convention's declaration")))
                    (if (>= (len items) 2)
                        (t-define-convention (nth items 1) s (syn-start s) (syn-end s))
                        (pfail "`(define-convention name clause …)`" s))))
                 ((define-syscall) (t-define-syscall #t s (syn-start s) (syn-end s)))
                 ((define-optional-syscall) (t-define-syscall #f s (syn-start s) (syn-end s)))
                 (else (t-exp (parse-exp s)))))))

(define append-tops (->* (top-list top-list) top-list)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append-tops (cdr xs) ys)))))

;; `(define-generative head rep)`: the form, and its two conversions, each
;; the identity: `(define up-name (poly (param …) (subr pure (rep) (name p
;; …))) (lambda (x) x))`, and `down-name` the other way.
(define generative? (->* (syn) bool)
  (lambda (s) (form-of? s 'define-generative)))
;; A parameter as a binder, its variance left out.
(define gen-binder (->* (syn int int) syn)
  (lambda (param a b)
    (let ((p (syn-items param "a parameter")))
      (if (>= (len p) 2)
          (mk-list (list (car p) (nth p 1)) a b)
          (pfail "a parameter is `(name kind)`, `(name kind +)` or `(name kind -)`" param)))))
;; The parameters as binders, and their names.
(define gen-binders (->* (syns-a int int) syns-a)
  (lambda (ps a b)
    (if (null? ps)
        nil
        (let ((binder (gen-binder (car ps) a b)))
          (cons binder (gen-binders (cdr ps) a b))))))
(define gen-names (->* (syns-a) syns-a)
  (lambda (bs)
    (if (null? bs)
        nil
        (cons (car (syn-items (car bs) "a parameter")) (gen-names (cdr bs))))))
;; A conversion, `prefix` and the name `n`, of type `ty`: the identity.
(define gen-conversion (->* (string string syn exp int int) top)
  (lambda (prefix n ty identity a b)
    (t-define (string->symbol (string-append prefix n)) (the syns-a (cons ty nil)) identity a b)))
(define parse-generative (->* (syn) top-list)
  (lambda (s)
    (let* ((items (syn-items s "a generative type")) (a (syn-start s)) (b (syn-end s))
           (usage (string-append "`(define-generative name type)` or "
                                 "`(define-generative (name (param kind) …) type)`")))
      (if (not (= (len items) 3))
          (pfail usage s)
          (let* ((head (nth items 1))
                 (rep (nth items 2))
                 (family? (tagcase head (lst (hs d ha hb) (not (null? hs))) (else x #f)))
                 (hs (if family? (syn-items head "a generative type's name") (the syns-a nil)))
                 (name (if family? (car hs) head))
                 (n (if (syn-symbol? name) (symbol->string (syn-symbol name)) (pfail usage s)))
                 (binders (if family? (gen-binders (cdr hs) a b) (the syns-a nil)))
                 (used (if family? (mk-list (cons name (gen-names binders)) a b) name))
                 (conv (lambda ((from syn) (to syn))
                         (let ((t (mk-pure-subr (the syns-a (cons from nil)) to a b)))
                           (if family? (mk-poly binders t a b) t))))
                 (x (product (1 'x) (2 (the syns-a nil))))
                 (identity (e-lambda (the param-list (cons x nil)) (e-var 'x a b 0 0) a b 0 0))
                 (up (gen-conversion "up-" n (conv rep used) identity a b))
                 (down (gen-conversion "down-" n (conv used rep) identity a b)))
            (list (t-define-generative head rep a b) up down))))))

;; Each of `xs`, parsed as a top-level form.
(define parse-each-top (->* (syns-a) top-list)
  (lambda (xs) (if (null? xs) nil (cons (parse-top (car xs)) (parse-each-top (cdr xs))))))
;; What top-level form `x` makes: a generative type's or a datatype's
;; several forms, or one.
(define parse-made (->* (syn) top-list)
  (lambda (x)
    (cond ((generative? x) (parse-generative x))
          ((datatype? x) (parse-each-top (expand-datatype x)))
          ((import? x) (parse-each-top (expand-import x)))
          ((form-of? x 'include) (cons (included-mark x) (include-made x)))
          (else (the top-list (cons (parse-top x) nil))))))
;; Where a top-level `include` is, `x`: the end of what is declared ahead,
;; a type or effect defined after it read in order (`k-included?`), as the
;; Rust checker makes the `include` there (`declare_each`).
(define included-mark (->* (syn) top)
  (lambda (x)
    (let ((a (syn-start x)) (b (syn-end x)))
      (t-define-effect (mk-symbol "%included" a b) (mk-symbol "pure" a b) a b))))
;; What a top-level `include`, `x`, makes: the forms of the `import` the
;; driver says it is (`include-import`); or, refused, a form refused where
;; it is checked, so that what is before it is checked first, as the Rust
;; checker checks it.
(define include-made (->* (syn) top-list)
  (lambda (x)
    (let* ((given (include-given-at (get includes-given) (syn-start x)))
           (why (if (null? given)
                    (string-append "a top-level `include` is made an `import` by what runs "
                                   "the program, which knows the module's names; none was here")
                    (extract (car given) 5)))
           (at (if (null? given) (syn-start x) (extract (car given) 6)))
           (end (if (null? given) (syn-end x) (extract (car given) 7))))
      (if (string=? why "")
          (parse-each-top (expand-import (include-import x (car given))))
          (the top-list (list (t-exp (e-module (loaded-error why) at end 0 0))))))))
;; A top-level `(include m)`, `x`: the `(import m x … (type t …) (effect e
;; …))` of what `m` gives, `g`, at `x`'s span (`Checker::include_forms`).
(define include-import (->* (syn include-given) syn)
  (lambda (x g)
    (let* ((items (syn-items x "a top-level `include`")) (a (syn-start x)) (b (syn-end x)))
      (cond ((not (= (len items) 2)) (pfail "a top-level `include` names a module" x))
            (else
             (begin
               (mk-list (cons (mk-symbol "import" a b)
                              (cons (mk-symbol (syn-name (nth items 1)) a b)
                                    (append (names-at (extract g 2) a b)
                                            (append (group-at "type" (extract g 3) a b)
                                                    (group-at "effect" (extract g 4) a b)))))
                        a b)))))))
;; Names `ns` as symbols at `a`..`b`.
(define names-at (->* (names int int) syns-a)
  (lambda (ns a b)
    (if (null? ns) nil (cons (mk-symbol (symbol->string (car ns)) a b) (names-at (cdr ns) a b)))))
;; `(word n …)` at `a`..`b`, in a list of one; none if `ns` is.
(define group-at (->* (string names int int) syns-a)
  (lambda (word ns a b)
    (if (null? ns)
        nil
        (the syns-a (cons (mk-list (cons (mk-symbol word a b) (names-at ns a b)) a b) nil)))))

;; Forms `xs`, each read in the state the one before left (`t`), under the
;; switches `settings`: to trees, each expression numbered (`parser-ids.fx`)
;; of the form's reading (`form-reading`).
(define parse-tops (->* (seen string syns-a) top-list)
  (lambda (t settings xs)
    (if (null? xs)
        nil
        ;; Before each form, the hidden globals of the files it loads first
        ;; (`parse-loaded`), those its types name first (`type-loaded`).
        (let* ((made (parse-made (type-loaded (car xs))))
               (before (shared-taken))
               (r (form-reading (walk-state t) settings (car xs) (loads-of before)))
               (form (number-form t r (append-tops before made)))
               (rest (parse-tops t settings (cdr xs))))
          (append-tops form rest)))))
;; The files the hidden globals `ts` are, each by its key and its trees.
(define loads-of (->* (top-list) loads)
  (lambda (ts)
    (if (null? ts)
        nil
        (tagcase (car ts)
          (t-define (n ty e a b)
            (let* ((name (symbol->string n)) (key (substring name 8 (string-length name)))
                   (f (loaded-keyed (get loaded) key)))
              (if (null? f)
                  (loads-of (cdr ts))
                  (the loads (cons (product (1 key) (2 (extract (car f) 5)))
                                   (loads-of (cdr ts)))))))
          (else y (loads-of (cdr ts)))))))
;; The file read whose key, as a hidden global names it, is `key` (its own,
;; or a `load-input`'s, `input:` before it: `parse-loaded`), in a list of one.
(define loaded-keyed (->* ((listof loaded-file acyclic) string) (listof loaded-file acyclic))
  (lambda (fs key)
    (cond ((null? fs) nil)
          ((or (string=? (extract (car fs) 7) key)
               (and (not (input-key? (extract (car fs) 7)))
                    (string=? (string-append "input:" (extract (car fs) 7)) key)))
           (the (listof loaded-file acyclic) (cons (car fs) nil)))
          (else (loaded-keyed (cdr fs) key)))))

;; The entry point: a program's forms, as read, read with `keys` (the mode,
;; the session's state, the checker's switches: `parser-types.fx`), to
;; trees, each expression numbered (`parser-ids.fx`), or an error; and the
;; session's state after them, the parser's count before them, and the keys
;; given, in order (`walk-given`). The prompt
;; catches every failure, but its tag is a global whose type names `rp`, so
;; the control effect stays in the type, as the reader's on `re` do; `rp`
;; is one of the regions this module is given, so that is still licensed.
(define parse-program (->* (keys syns-a) keyed)
  (lambda (keys forms)
    (let* ((t (walk-of keys)) (base (walk-count t)))
      (begin (shared-reset!)
             (let* ((parsed (prompt parse-tag (p-ok (parse-tops t (extract keys 3) forms))
                                    (lambda (r) r)))
                    (done (walk-done! t))
                    ;; A key `validate` found given twice, the parse's error.
                    (wrong (walk-wrong))
                    (r (if (string=? (extract wrong 1) "")
                           parsed
                           (p-err (extract wrong 1) (extract wrong 2) (extract wrong 3)))))
               (product (1 r) (2 (walk-state t)) (3 base) (4 (walk-given t))))))))
