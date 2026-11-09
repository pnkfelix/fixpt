;;; Typed hygienic macros, in FX-26: a file's macros, which
;;; `import-with-syntax` brings (`macros.rs`'s `define_file`,
;;; `Checker::import_file_macros`), defined by the expander (`macros.fx`),
;;; each meaning what it meant in its file. Loaded by `parser-top.fx`; loads
;;; `macros-templates.fx`, and gives it on (`templates-module`), so that the
;;; parser's instances of the expander's parts are one.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define templates-module ((proj (load-module "fx26:macros-templates.fx") rs re rm rc rp)))
(define macros-module (with templates-module macros-module))
(import macros-module atom define-macro defined fail-at file-items file-syntax forms-module
        head-name import-usage in-loaded-as internal-names internal-of len load-base load-of
        load-path loaded-path loads macro-names macro-of macro? mk-list mk-symbol name-filter
        names-shown not-macros nth proper shown-names syn-end syn-start syn-symbol syn-symbol?
        taken? without-load
        (type fails file-macro files filter macro macro-env mades names scope syn syns-a))

;; Notes a top-level `(define name (load-module "path"))`, the file
;; `import-with-syntax` of `name` reads; any other definition of `name`
;; forgets it (`Checker::note_load_def`).
(define note-load-def! (->* (syn) unit)
  (lambda (form)
    (let ((items (proper form)))
      (if (and (>= (len items) 3) (string=? (head-name form) "define") (syn-symbol? (nth items 1)))
          (let* ((n (syn-symbol (nth items 1)))
                 (path (load-path (nth items (- (len items) 1))))
                 (kept (without-load n (get loads))))
            (set loads (if (and (not (null? path)) (<= (len items) 4))
                           (cons (tuple n (car path)) kept)
                           kept)))
          #u))))

;; The standard bindings' names, which a file's macro may name: what the
;; driver says, as the Rust checker has them (`standard-names!`).
(define standard-names (ref names rs) (new nil))
(define standard-names! (->* (names) unit) (lambda (ns) (set standard-names ns)))


;; `(import-with-syntax lib)`, `lib` a name defined as `(load-module
;; "path")`: the file's macros defined, each as the file means it, and the
;; rest of what it gives as `(include lib)` gives it: that `include`'s form,
;; in a list of one; none if `(only …)` names macros alone. Of `fs`, the
;; files the driver read (`Checker::import_file_macros`).
(define import-file-macros (->* (fails syn files) syns-a)
  (lambda (fail form fs)
    (let* ((items (proper form)) (a (syn-start form)) (b (syn-end form)))
      (if (not (and (or (= (len items) 2) (= (len items) 3)) (syn-symbol? (nth items 1))))
          (begin (fail-at fail import-usage form) nil)
          (let* ((lib (syn-symbol (nth items 1)))
                 (filter (if (= (len items) 3)
                             (the (listof filter acyclic) (list (name-filter fail (nth items 2))))
                             nil))
                 (path (load-of lib (get loads))))
            (if (null? path)
                (begin (fail-at fail (string-append "`import-with-syntax` takes a name defined as "
                                                    "`(load-module \"path\")`, and `"
                                                    (symbol->string lib) "` is not one")
                                form)
                       nil)
                (let ((exported (file-macros fail form (car path) filter fs)))
                  (include-of lib filter exported a b))))))))
;; The `include` that gives the rest: of the names `filter` lists, those
;; not macros.
(define include-of (->* (symbol (listof filter acyclic) names int int) syns-a)
  (lambda (lib filter exported a b)
    (let ((head (list (mk-symbol "include" a b) (mk-symbol (symbol->string lib) a b))))
      (if (null? filter)
          (list (mk-list head a b))
          (let ((rest (not-macros (extract (car filter) 2) exported)))
            (if (and (extract (car filter) 1) (null? rest))
                nil
                (list (mk-list (append head
                                       (list (mk-list (cons (mk-symbol (if (extract (car filter) 1)
                                                                           "only"
                                                                           "except")
                                                                       a b)
                                                            rest)
                                                      a b)))
                               a b))))))))

;; The macros of the file at `path`, defined (`define-file`): the names of
;; those not hidden.
(define file-macros (->* (fails syn string (listof filter acyclic) files) names)
  (lambda (fail form path filter fs)
    (let ((f (loaded-path path fs)))
      (cond
        ((null? f) (begin (fail-at fail (string-append "cannot read `" path "`") form) nil))
        (((with forms-module takes-modules?) (extract (car f) 5))
         (begin (fail-at fail (string-append "`" path "` takes module parameters: its macros "
                                             "cannot be imported, not yet")
                         form)
                nil))
        (else
         (let* ((key (extract (car f) 7)) (base (extract (car f) 2)) (forms (extract (car f) 5))
                ;; An error in the file, said in it, where the form starts.
                (in-file (lambda ((m string) (x int) (y int))
                           (if (and (>= x base) (< x (+ base load-base)))
                               (let ((at (syn-start form)))
                                 (fail (in-loaded-as fs base path m x) at at))
                               (fail m x y))))
                (macros (file-syntax forms))
                (shown (names-shown (file-items forms) nil nil))
                (internal (internal-names key (macro-names macros)))
                (scope (tuple (string->symbol (string-append "%shared:" key)) (extract shown 1)
                              (extract shown 2) internal (get standard-names))))
           (define-file in-file macros scope filter)))))))

;; A file's macros, `ms`, defined as the file means them (`scope`): among
;; themselves first, by their names in it, as its templates name them;
;; then each by the name the importer has it by, and each not hidden that
;; `filter` takes by its own name too. The names of those not hidden.
(define define-file (->* (fails (listof file-macro acyclic) scope (listof filter acyclic)) names)
  (lambda (fail ms scope filter)
    (let ((program (get defined)))
      (begin
        (set defined nil)
        (let* ((made (define-each fail ms scope)) (own (get defined)))
          (begin
            (set defined program)
            (give-each fail made own scope filter
                       (if (null? ms) (atom '() 0 0 0) (extract (car ms) 1)))
            (shown-names made)))))))
(define define-each (->* (fails (listof file-macro acyclic) scope) mades)
  (lambda (fail ms scope)
    (if (null? ms)
        nil
        (let ((ns (define-macro fail (extract (car ms) 1) (list scope))))
          (append (hidden-as ns (extract (car ms) 2)) (define-each fail (cdr ms) scope))))))
(define hidden-as (->* (names bool) mades)
  (lambda (ns h) (if (null? ns) nil (cons (tuple (car ns) h) (hidden-as (cdr ns) h)))))
(define give-each
  (->* (fails mades macro-env scope (listof filter acyclic) syn) unit)
  (lambda (fail made own scope filter first)
    (if (null? made)
        #u
        (let* ((n (extract (car made) 1)) (m (car (macro-of n own)))
               (internal (car (internal-of n (extract scope 4)))))
          (begin
            (if (and (not (extract (car made) 2)) (taken? n filter))
                (if (macro? n)
                    (fail-at fail (string-append "`" (symbol->string n) "` is a macro defined "
                                                 "already: a file's may not be defined again")
                             first)
                    (set defined (cons (tuple n m) (get defined))))
                #u)
            (set defined (cons (tuple internal m) (get defined)))
            (give-each fail (cdr made) own scope filter first))))))

