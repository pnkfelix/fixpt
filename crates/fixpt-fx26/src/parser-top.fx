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
(import parser-types (type keys keyed loaded-file loaded-files))
(define reader-types (with parser-module reader-types))
(import reader-types lst (type syn))
(import parser-module parse-tag syn-start syn-end pfail syn-symbol? syn-symbol syn-items len nth
        keep mk-list form-head form-of? datatype? mk-pure-subr mk-poly expand-datatype import?
        expand-import e-var e-lambda t-define t-define-rec t-define-type t-define-effect
        includes-given include-given-at mk-symbol syn-name loaded-error e-module pfail-at
        (type include-given)
        t-define-convention t-define-syscall t-define-generative t-exp p-ok p-err shared-taken
        shared-reset! loaded loaded-next input-key? label-name e-app e-plambda e-proj e-if
        loaded-based in-loaded-as
        e-letrec e-let e-begin e-prompt e-letregion e-rlambda e-the e-convention e-bloblet
        e-product e-extract e-sum e-tagcase e-with rl-none
        (type syns-a exp top param-list top-list presult names)
        (effect parses))
(import parser-exps-module parse-exp parse-rec-bindings type-loaded)
;; The expander (`macros.fx`), which each form goes through first.
;; A program's binding structure, walked, and the shapes of the modules its
;; forms open written in (`macros-shapes.fx`).
(define shapes-module ((proj (load-module "fx26:macros-shapes.fx") rs re rm rc rp)))
(import shapes-module top-shaped forms-written-in shapes-at! shapes-after! files-shaped
        shared-shaped! shape-definition? shape-defined! sealed-written aliases-resolved)
(define imports-module ((proj (load-module "fx26:macros-imports.fx") rs re rm rc rp)))
(define templates-module (with imports-module templates-module))
(define macros-module (with templates-module macros-module))
(import templates-module template-checks)
(import imports-module import-file-macros note-load-def!)
(import macros-module expand expand-top define-macro defines-syntax? macros-at! macros-after!
        syntax-names imports-syntax? globals! global-before? macro? later-macro-site def-envs-given
        file-scope-begin! file-scope-end! source-of)
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
                 (family? (tagcase head (lst (hs d ha hb xpn) (not (null? hs))) (else x #f)))
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
          ((datatype? x) (parse-each-top (written-each (expand-datatype x))))
          ((import? x) (parse-each-top (written-each (expand-import x))))
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
          (parse-each-top (written-each (expand-import (include-import x (car given)))))
          (the top-list (list (t-exp (e-module (loaded-error why) at end 0 0))))))))
;; A top-level `(include m)`, `x`: the `(import m x … (type t …) (effect e
;; …))` of what `m` gives, `g`, at `x`'s span (`Checker::include_forms`);
;; of `(include m (only n …))` or `(except n …)`, what `g` says it takes.
(define include-import (->* (syn include-given) syn)
  (lambda (x g)
    (let* ((items (syn-items x "a top-level `include`")) (a (syn-start x)) (b (syn-end x)))
      (cond ((not (or (= (len items) 2) (= (len items) 3)))
             (pfail "a top-level `include` names a module" x))
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
;; of the form's reading (`form-reading`). Each form is expanded first
;; (`macros.fx`): a `define-syntax` defines a macro and makes nothing, and
;; is in the state after it, as every form is; any other is its expansion.
;; The reading is of the form as written, the macros it was expanded with
;; in the state it was read in.
(define parse-tops (->* (seen string syns-a) top-list)
  (lambda (t settings xs)
    (if (null? xs)
        nil
        ;; Before each form, the hidden globals of the files it loads first
        ;; (`parse-loaded`), those its types name first (`type-loaded`).
        (let* ((written (car xs))
               (made (top-made written))
               (guarded (guard-defs made (cdr xs)))
               (before (shared-noted (shared-taken)))
               (r (form-reading (walk-state t) settings written (loads-of before)))
               (form (number-form t r (append-tops before guarded)))
               (rest (begin (macros-after! r) (shapes-after! r) (parse-tops t settings (cdr xs)))))
          (append-tops form rest)))))
;; What top-level form `written` makes, parsed. A `define-syntax`: the
;; checks of its templates, once, there. A `hide`: its forms', as if
;; written there, a program exporting nothing to hide them from; one form
;; still, of one reading.
(define top-made (->* (syn) top-list)
  (lambda (written)
    (cond ((shape-definition? written)
           (begin (global-macro written) (shape-defined! written) nil))
          ((defines-syntax? written)
           (begin (global-macro written)
                  (macro-checks (define-macro pfail-at written nil))))
          ;; A file's macros, and the `include` of the rest.
          ((imports-syntax? written)
           (let ((inc (import-file-macros pfail-at written (get loaded))))
             (if (null? inc) (the top-list nil) (parse-made (car inc)))))
          ((form-of? written 'hide) (tops-made (cdr (syn-items written ""))))
          (else (expanded-tops (expand-top pfail-at written))))))
(define tops-made (->* (syns-a) top-list)
  (lambda (xs)
    (if (null? xs) nil (let ((made (top-made (car xs)))) (append-tops made (tops-made (cdr xs)))))))
;; Each form a top-level form is expanded to (a use of a macro that makes
;; definitions, several), parsed, each as it is noted.
(define expanded-tops (->* (syns-a) top-list)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((x (car xs))
               (made (begin (note-load-def! x)
                            (unalias-tops (parse-made (type-loaded (written-top x)))))))
          (append-tops made (expanded-tops (cdr xs)))))))
;; Top-level form `x`, after expansion, with what each module it opens was
;; relied on for written in (`macros-shapes.fx`), the files it loads shaped
;; first, and their forms so written given the parser (`forms-written-in`).
;; Not a top-level `include`, an `import` or a datatype's definition, whose
;; forms are shaped as each is made (`include-made`, `written-each`), as the
;; Rust checker shapes them.
(define written-top (->* (syn) syn)
  (lambda (x)
    (if (or (form-of? x 'include) (import? x) (datatype? x))
        x
        (let ((shaped (top-shaped (aliases-resolved pfail-at (sealed-written pfail-at x)
                                                    (def-envs-given)))))
          (begin (files-written!) shaped)))))
;; The hidden globals of the files loaded, `ts`, each noted with its file's
;; shape (`shared-shaped!`), for the forms after: its definition is made,
;; not read, so is not shaped as forms are.
(define shared-noted (->* (top-list) top-list)
  (lambda (ts)
    (begin (shared-each ts) ts)))
(define shared-each (->* (top-list) unit)
  (lambda (ts)
    (if (null? ts)
        #u
        (begin (tagcase (car ts) (t-define (n t x a b) (shared-shaped! n)) (else y #u))
               (shared-each (cdr ts))))))
;; Each of `xs`, `written-top`.
(define written-each (->* (syns-a) syns-a)
  (lambda (xs) (if (null? xs) nil (cons (written-top (car xs)) (written-each (cdr xs))))))
;; The loads' files, their forms as their shapes wrote them, once more are
;; shaped.
(define files-shaped-count (ref int rs) (new 0))
(define files-written! (->* () unit)
  (lambda ()
    (let ((n (files-shaped)))
      (if (= n (get files-shaped-count))
          #u
          (begin (set files-shaped-count n)
                 (set loaded (forms-written-in (get loaded)))
                 (set loaded-next (forms-written-in (get loaded-next))))))))
;; Each of macros `ns`' templates' checks, expanded and parsed.
(define macro-checks (->* (names) top-list)
  (lambda (ns)
    (if (null? ns)
        nil
        (append-tops (parse-checks (template-checks pfail-at (car ns))) (macro-checks (cdr ns))))))
;; Each of a macro's templates' checks, expanded and parsed.
(define parse-checks (->* (syns-a) top-list)
  (lambda (cs)
    (if (null? cs)
        nil
        (append-tops (parse-made (aliases-resolved pfail-at (expand pfail-at (car cs))
                                                   (def-envs-given)))
                     (parse-checks (cdr cs))))))
;; A `define-syntax` (or `define-syntax-rec`) of a name a form before this
;; parse defined as a global: refused, where it is
;; (`Checker::macro_expanded`, which knows the globals checked; a program's
;; own are refused where each is checked, `guard-defs`).
(define global-macro (->* (syn) unit)
  (lambda (s) (globals-taken (syntax-names s) s)))
(define globals-taken (->* (names syn) unit)
  (lambda (ns s)
    (cond ((null? ns) #u)
          ((global-before? (car ns))
           (pfail (string-append "`" (symbol->string (car ns))
                                 "` is defined already: a macro may not take its name")
                  s))
          (else (globals-taken (cdr ns) s)))))
;; Tops `ts`, each definition's names noted as globals, until one of them
;; is a macro's: as the Rust checker refuses it where it is checked
;; (`top_defining_kept`), a form refused there, said where the macro is if
;; a form after this one (of `later`) makes it; else said at the
;; definition, which an `import` or `include` made after expansion.
(define guard-defs (->* (top-list syns-a) top-list)
  (lambda (ts later)
    (if (null? ts)
        nil
        (let ((bad (bad-name (top-names (car ts)) later)))
          (if (null? bad)
              (begin (globals! (top-names (car ts)))
                     (cons (car ts) (guard-defs (cdr ts) later)))
              (let* ((n (symbol->string (extract (car bad) 1))) (site (extract (car bad) 2))
                     (why (if (null? site)
                              (string-append "`" n "` is a macro's name, which is not defined "
                                             "again")
                              (string-append "`" n "` is defined already: a macro may not take its "
                                             "name")))
                     (a (if (null? site) (top-start (car ts)) (extract (car site) 1)))
                     (b (if (null? site) (top-end (car ts)) (extract (car site) 2))))
                (the top-list (list (t-exp (e-module (loaded-error why) a b 0 0))))))))))
;; The first of `ns` a macro's, with where a later form makes it one (none
;; if no later form does), in a list of one.
(define-type sites (listof (tupleof int int) acyclic))
(define bad-name (->* (names syns-a) (listof (productof (1 symbol) (2 sites)) acyclic))
  (lambda (ns later)
    (if (null? ns)
        nil
        (let ((site (later-macro-site (car ns) later (get loaded))))
          (if (or (not (null? site)) (macro? (car ns)))
              (list (product (1 (car ns)) (2 site)))
              (bad-name (cdr ns) later))))))
;; The names a top-level form defines as values (`Checker::defined_names`).
(define top-names (->* (top) names)
  (lambda (x)
    (tagcase x
      (t-define (n ty e a b) (list n))
      (t-define-rec (bs a b) (rec-binding-names bs))
      (t-define-syscall (req s a b)
        (let ((items (syn-items s "a syscall")))
          (if (and (> (len items) 1) (syn-symbol? (nth items 1)))
              (list (syn-symbol (nth items 1)))
              nil)))
      (else y nil))))
(define rec-binding-names (->* ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) names)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 1) (rec-binding-names (cdr bs))))))
(define top-start (->* (top) int)
  (lambda (x)
    (tagcase x
      (t-define (n ty e a b) a) (t-define-rec (bs a b) a) (t-define-syscall (q s a b) a)
      (else y 0))))
(define top-end (->* (top) int)
  (lambda (x)
    (tagcase x
      (t-define (n ty e a b) b) (t-define-rec (bs a b) b) (t-define-syscall (q s a b) b)
      (else y 0))))
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

;;; ------------------------------------------------------------ aliases

;; A procedural macro's aliases (`macros-procedural.fx`; `TODO.md` §228),
;; decided where both the checker and the compiler read them: `%~N:x`, which
;; an expansion bound, is a name of its own; one it left free is the top
;; level's `x`, `(with #%toplevel x)` (`aliases.rs`). The aliases the top
;; level defined so far, in the session: each read alone, as a REPL's entry
;; or `fixpt eval`'s form; an alias is spelled once in a session.
(define alias-defs (ref names rs) (new nil))
(define alias? (->* (symbol) bool)
  (lambda (n) (not (string=? (label-name (symbol->string n)) (symbol->string n)))))
(define name-in? (->* (symbol names) bool)
  (lambda (n ns) (and (not (null? ns)) (or (symbol=? n (car ns)) (name-in? n (cdr ns))))))
(define unalias-tops (->* (top-list) top-list)
  (lambda (ts) (if (null? ts) nil (cons (unalias-top (car ts)) (unalias-tops (cdr ts))))))
(define unalias-top (->* (top) top)
  (lambda (t)
    (tagcase t
      (t-define (n ty e a b)
        (begin (if (alias? n) (set alias-defs (cons n (get alias-defs))) #u)
               (t-define n ty (unalias e (list n)) a b)))
      (t-define-rec (bs a b)
        (let ((ns (rec-names bs)))
          (begin (set alias-defs (append ns (get alias-defs)))
                 (t-define-rec (unalias-rec bs ns) a b))))
      (t-exp (e) (t-exp (unalias e nil)))
      (else y t))))
;; Each alias in `e` that nothing binds where it is, `bound` those around
;; it, nor the top level defined: the top level's name.
(define unalias (->* (exp names) exp)
  (lambda (e bound)
    (tagcase e
      (e-var (s a b k kr)
        (if (or (not (alias? s)) (name-in? s bound) (name-in? s (get alias-defs)))
            e
            (e-with '#%toplevel (e-var (string->symbol (label-name (symbol->string s))) a b k kr)
                    a b k kr (rl-none))))
      (e-lambda (ps body a b k kr) (e-lambda ps (unalias body (param-names ps bound)) a b k kr))
      (e-app (f xs a b k kr) (e-app (unalias f bound) (unalias-each xs bound) a b k kr))
      (e-plambda (bs body a b k kr) (e-plambda bs (unalias body bound) a b k kr))
      (e-proj (body ds a b k kr) (e-proj (unalias body bound) ds a b k kr))
      (e-if (t c x a b k kr) (e-if (unalias t bound) (unalias c bound) (unalias x bound) a b k kr))
      (e-letrec (bs body a b k kr)
        (let ((in (append (rec-names bs) bound)))
          (e-letrec (unalias-rec bs in) (unalias body in) a b k kr)))
      (e-let (bs body a b k kr)
        (e-let (unalias-binds bs bound) (unalias body (bind-names bs bound)) a b k kr))
      (e-begin (xs a b k kr) (e-begin (unalias-each xs bound) a b k kr))
      (e-prompt (t body h a b k kr)
        (e-prompt (unalias t bound) (unalias body bound) (unalias h bound) a b k kr))
      (e-letregion (m r p body a b k kr) (e-letregion m r p (unalias body bound) a b k kr))
      (e-rlambda (r l a b k kr) (e-rlambda (unalias r bound) (unalias l bound) a b k kr))
      (e-the (t x a b k kr) (e-the t (unalias x bound) a b k kr))
      (e-convention (c x a b k kr) (e-convention c (unalias x bound) a b k kr))
      (e-bloblet (op i xs d a b k kr) (e-bloblet op i (unalias-each xs bound) d a b k kr))
      (e-product (fs a b k kr) (e-product (unalias-binds fs bound) a b k kr))
      (e-extract (x l d a b k kr) (e-extract (unalias x bound) l d a b k kr))
      (e-sum (l x a b k kr) (e-sum l (unalias x bound) a b k kr))
      (e-tagcase (x arms els d a b k kr)
        (e-tagcase (unalias x bound) (unalias-arms arms bound) (unalias-else els bound) d
                   a b k kr))
      (e-module (items a b k kr) (e-module (unalias-items items (item-names items bound)) a b k kr))
      (e-with (m body a b k kr wrl)
        (if (or (symbol=? m '#%fx) (symbol=? m '#%toplevel))
            e
            (e-with m (unalias body bound) a b k kr wrl)))
      (else y e))))
(define unalias-each (->* ((listof exp acyclic) names) (listof exp acyclic))
  (lambda (xs bound)
    (if (null? xs) nil (cons (unalias (car xs) bound) (unalias-each (cdr xs) bound)))))
(define param-names (->* (param-list names) names)
  (lambda (ps bound)
    (if (null? ps) bound (cons (extract (car ps) 1) (param-names (cdr ps) bound)))))
(define rec-names (->* ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) names)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 1) (rec-names (cdr bs))))))
(define unalias-rec
  (->* ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) names)
       (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
  (lambda (bs bound)
    (if (null? bs)
        nil
        (cons (product (1 (extract (car bs) 1)) (2 (extract (car bs) 2))
                       (3 (unalias (extract (car bs) 3) bound)))
              (unalias-rec (cdr bs) bound)))))
(define bind-names (->* ((listof (productof (1 symbol) (2 exp)) acyclic) names) names)
  (lambda (bs bound)
    (if (null? bs) bound (cons (extract (car bs) 1) (bind-names (cdr bs) bound)))))
(define unalias-binds
  (->* ((listof (productof (1 symbol) (2 exp)) acyclic) names)
       (listof (productof (1 symbol) (2 exp)) acyclic))
  (lambda (bs bound)
    (if (null? bs)
        nil
        (cons (product (1 (extract (car bs) 1)) (2 (unalias (extract (car bs) 2) bound)))
              (unalias-binds (cdr bs) bound)))))
;; A `tagcase`'s `else`, its name in scope in its body.
(define unalias-else
  (->* ((listof (productof (1 symbol) (2 exp)) acyclic) names)
       (listof (productof (1 symbol) (2 exp)) acyclic))
  (lambda (bs bound)
    (if (null? bs)
        nil
        (cons (product (1 (extract (car bs) 1))
                       (2 (unalias (extract (car bs) 2) (cons (extract (car bs) 1) bound))))
              (unalias-else (cdr bs) bound)))))
(define unalias-arms
  (->* ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) names)
       (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
  (lambda (arms bound)
    (if (null? arms)
        nil
        (let ((r (car arms)))
          (cons (product (1 (extract r 1)) (2 (extract r 2)) (3 (extract r 3))
                         (4 (unalias (extract r 4) (append (extract r 3) bound))))
                (unalias-arms (cdr arms) bound))))))
(define item-names
  (->* ((listof (productof (1 int) (2 names) (3 syns-a) (4 (listof exp acyclic))) acyclic) names)
       names)
  (lambda (items bound)
    (if (null? items) bound (append (extract (car items) 2) (item-names (cdr items) bound)))))
(define unalias-items
  (->* ((listof (productof (1 int) (2 names) (3 syns-a) (4 (listof exp acyclic))) acyclic) names)
       (listof (productof (1 int) (2 names) (3 syns-a) (4 (listof exp acyclic))) acyclic))
  (lambda (items bound)
    (if (null? items)
        nil
        (let ((it (car items)))
          (cons (product (1 (extract it 1)) (2 (extract it 2)) (3 (extract it 3))
                         (4 (unalias-each (extract it 4) bound)))
                (unalias-items (cdr items) bound))))))

;;; ------------------------------------------------------------ a file's own macros

;; Each file loaded, its own macros' uses expanded (`binding-shapes.md`,
;; step 3; Heist's (a); the Rust checker's `file_own_expanded`): each
;; `define-syntax`, hidden or not, defined in order where the file's items
;; are (`file-scope-begin!`), and the items after it expanded by them, each
;; name a template leaves free the file's item or standard binding of that
;; name, a binder at the use that would capture it renamed. Its
;; `define-syntax`es kept; a shape's no macro. Once for each file, both
;; lists of them alike; a file whose expansion fails keeps why, which its
;; load says.
(define loaded-own-expanded! (->* () unit)
  (lambda ()
    (let ((fs (files-own-expanded (get loaded))))
      (begin (set loaded fs) (set loaded-next (same-files (get loaded-next) fs))))))
(define files-own-expanded (->* (loaded-files) loaded-files)
  (lambda (fs)
    (if (null? fs) nil (cons (file-own-expanded (car fs)) (files-own-expanded (cdr fs))))))
(define same-files (->* (loaded-files loaded-files) loaded-files)
  (lambda (ns fs)
    (if (null? ns)
        nil
        (cons (let ((f (loaded-based fs (extract (car ns) 2)))) (if (null? f) (car ns) (car f)))
              (same-files (cdr ns) fs)))))
(define file-own-expanded (->* (loaded-file) loaded-file)
  (lambda (f)
    (if (or (<= (extract f 2) 0) (extract f 8)
            (not (or (own-macros? (extract f 5)) (imports-syntax-in? (extract f 5)))))
        f
        (let* ((saved (file-scope-begin!))
               (r (prompt parse-tag (begin (set own-out (own-each (extract f 5))) (p-ok nil))
                          (lambda ((r presult)) r)))
               (ended (file-scope-end! saved)))
          (tagcase r
            ;; Its forms as read, which its shape is found from; the
            ;; error said where it is loaded (`parse-load-file`).
            (p-err (m x y)
              (product (1 (extract f 1)) (2 (extract f 2))
                       ;; At its place in the file, an expansion's part's
                       ;; where its template has it.
                       (3 (in-loaded-as (get loaded) (extract f 2) (extract f 4) m
                                        (extract (source-of x) 1)))
                       (4 (extract f 4)) (5 (extract f 5)) (6 (extract f 6)) (7 (extract f 7))
                       (8 #f)))
            (else y
              (product (1 (extract f 1)) (2 (extract f 2)) (3 (extract f 3)) (4 (extract f 4))
                       (5 (get own-out)) (6 (extract f 6)) (7 (extract f 7)) (8 #f))))))))
(define own-out (ref syns-a rs) (new nil))
;; Whether forms `xs` import a file's macros (`import-with-syntax`), which a
;; module file may not yet (`own-each`).
(define imports-syntax-in? (->* (syns-a) bool)
  (lambda (xs) (and (not (null? xs)) (or (form-of? (car xs) 'import-with-syntax)
                                        (imports-syntax-in? (cdr xs))))))
;; Whether forms `xs` define a macro, hidden or not.
(define own-macros? (->* (syns-a) bool)
  (lambda (xs)
    (and (not (null? xs))
         (or (own-macro? (car xs))
             (and (form-of? (car xs) 'hide) (own-macros? (cdr (syn-items (car xs) ""))))
             (own-macros? (cdr xs))))))
(define own-macro? (->* (syn) bool)
  (lambda (x) (and (defines-syntax? x) (not (shape-definition? x)))))
(define own-each (->* (syns-a) syns-a)
  (lambda (xs)
    (if (null? xs)
        nil
        (let* ((x (car xs))
               (made (cond ((or (form-of? x 'module-parameters) (shape-definition? x)) (list x))
                           ((form-of? x 'import-with-syntax)
                            (begin (pfail-at (string-append "`import-with-syntax` in a module "
                                                            "file: not yet; a program's top "
                                                            "level imports a file's macros "
                                                            "(`binding-shapes.md`, step 4)")
                                             (syn-start x) (syn-end x))
                                   nil))
                           ((own-macro? x) (begin (define-macro pfail-at x nil) (list x)))
                           ((form-of? x 'hide)
                            (let ((items (syn-items x "")))
                              (list (mk-list (cons (car items) (own-each (cdr items)))
                                             (syn-start x) (syn-end x)))))
                           (else (own-expanded (expand-top pfail-at x))))))
          (append made (own-each (cdr xs)))))))
(define own-expanded (->* (syns-a) syns-a)
  (lambda (xs)
    (if (null? xs)
        nil
        (cons (aliases-resolved pfail-at (sealed-written pfail-at (car xs)) (def-envs-given))
              (own-expanded (cdr xs))))))

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
             (macros-at! (walk-state t))
             (loaded-own-expanded!)
             (shapes-at! (walk-state t) (get loaded))
             (set files-shaped-count -1)
             (let* ((parsed (prompt parse-tag (p-ok (parse-tops t (extract keys 3) forms))
                                    (lambda (r) r)))
                    (done (walk-done! t))
                    ;; A key `validate` found given twice, the parse's error.
                    (wrong (walk-wrong))
                    (r (if (string=? (extract wrong 1) "")
                           parsed
                           (p-err (extract wrong 1) (extract wrong 2) (extract wrong 3)))))
               (product (1 r) (2 (walk-state t)) (3 base) (4 (walk-given t))))))))
