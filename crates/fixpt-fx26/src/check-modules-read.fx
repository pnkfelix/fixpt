;;; The checker, in FX-26: first-class modules' descriptions, read
;;; (`docs/research/first-class-modules.md`, stage M2): `moduleof` and
;;; `select`, and a `module`'s items, in one recursive group with the
;;; expression walk (`check-resolve.fx`'s), as a module is an expression
;;; and its items hold them. Before `check-modules.fx`.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
;; Its types (`check-modules-types.fx`, its file's after it), loaded before the
;; module so that they are not among its values; the module names what it
;; uses of them.
(let* ((check-modules-types (load-module "fx26:check-modules-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (check-synth-types (load-module "fx26:check-synth-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-read-types (load-module "fx26:check-read-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (check-syntax-types (load-module "fx26:check-syntax-types.fx"))
       (check-read-descs-types (load-module "fx26:check-read-descs-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (reader-types (load-module "fx26:reader-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (check-syntax (select check-syntax-types check-syntax-sig))
           (check-read (select check-read-types check-read-sig))
           (check-env (select check-env-types check-env-sig))
           (check-read-descs (select check-read-descs-types check-read-descs-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (parser (select reader-types parser-sig)))
    (module
(hide (include check-modules-types) (include check-types-types) (include check-synth-types)
      (include parser-types) (include check-resolve-types) (include check-read-types)
      (include check-env-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-resolve) (include check-syntax) (include check-read)
      (include check-env) (include check-read-descs) (include check-subst) (include parser))

;; A module item as `x-module` has it.
(define k-item-of (->* (int names int k-ids kxs) k-item)
  (lambda (k ns v ts xs) (product (1 k) (2 (k-copy-names ns)) (3 v) (4 ts) (5 xs))))
(define k-push-binders (->* (k-binders) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (let ((v (extract (car bs) 1)))
          (begin (k-push-desc (k-dvar-name v) (ds-var v (extract (car bs) 2)))
                 (k-push-binders (cdr bs)))))))
;; The names a module's items give type abbreviations: each `define-type`
;; of a name, but of a `dlambda` or an effect.
(define k-module-type-names (->* (mod-items) k-names)
  (lambda (items)
    (if (null? items)
        nil
        (let* ((it (car items)) (ts (extract it 3)) (rest (k-module-type-names (cdr items))))
          (if (and (= (extract it 1) 1) (null? (cdr ts))
                   (not (string=? (k-list-head (car ts)) "dlambda")))
              (the k-names (cons (car (extract it 2)) rest))
              rest)))))
;; Whether the file read at `base` is built in (`fx26:…`): while one is
;; checked, the standard names only it may name are seen
;; (`k-built-in-only?`).
(define k-built-in-at? (->* (loaded-files int) bool)
  (lambda (fs base)
    (cond ((null? fs) #f)
          ((= (extract (car fs) 2) base)
           (let ((p (extract (car fs) 4)))
             (and (>= (string-length p) 5) (string=? (substring p 0 5) "fx26:"))))
          (else (k-built-in-at? (cdr fs) base)))))
(define k-in-loaded (->* (k-thunk-unit int int int) unit)
  (lambda (f base a b)
    (let* ((n (if (k-built-in-at? (get loaded) base) 1 0))
           (in (set k-in-built-in (+ (get k-in-built-in) n)))
           (r (prompt k-tag (begin (f) (k-done (k-te 0 nil))) (lambda (r) r)))
           (out (set k-in-built-in (- (get k-in-built-in) n))))
      (tagcase r
        (k-err (m ea eb)
          (if (and (>= ea base) (< ea (+ base load-base)))
              (k-fail-placed m ea)
              (k-fail m ea eb)))
        (else y #u)))))
;; Error `m` at `at`, in a file read, said in each file on the way out to
;; the program (`loaded-placed`), there.
(define k-fail-placed (->* (string int) void)
  (lambda (m at)
    (let ((p (loaded-placed (get loaded) m at)))
      (k-fail (extract p 1) (extract p 2) (extract p 2)))))
;; What a module's first item says of where it was read: from its file, at
;; a base (> 3); not, and why (-1); or not from a file (0 to 3).
(define k-items-kind (->* (mod-items) int)
  (lambda (items) (if (null? items) 0 (extract (car items) 1))))
;; The names a module's item defines as descriptions (`types`), or as values:
;; a generative type's name is one, its two conversions values; as the Rust
;; checker's `defined_twice` counts them.
(define k-item-names (->* (mod-item bool) k-names)
  (lambda (it types)
    (let ((k (extract it 1)))
      (case k ((0)
               (let* ((n (car (extract it 2))) (s (symbol->string n)))
                 (if types
                     (the k-names (list n))
                     (the k-names (list (string->symbol (string-append "up-" s))
                                        (string->symbol (string-append "down-" s)))))))
              ((1) (if types (extract it 2) (the k-names nil)))
              (else (if types (the k-names nil) (extract it 2)))))))
;; The first name of `items`, in order, that one before it defines too, as a
;; description (`seen`) or as a value (`vseen`): a module defining a name
;; twice has no type (`moduleof` refuses it), and which definition a use got
;; would depend on the path that ran it. A value may have a type's name.
(define k-defined-twice (->* (mod-items k-names k-names) k-names)
  (lambda (items seen vseen)
    (letrec ((first (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
               (lambda (ns seen)
                 (cond ((null? ns) nil)
                       ((k-has-name? seen (car ns)) (the k-names (list (car ns))))
                       (else (first (cdr ns) seen))))))
      (if (null? items)
          nil
          (let* ((ts (k-item-names (car items) #t)) (vs (k-item-names (car items) #f))
                 (twice (first ts seen)) (vtwice (first vs vseen)))
            (cond ((not (null? twice)) twice)
                  ((not (null? vtwice)) vtwice)
                  (else (k-defined-twice (cdr items) (k-names-onto ts seen)
                                         (k-names-onto vs vseen)))))))))
;; How many of `xs` there are.
;; A `blobref-variant!`'s operands resolved, `xs`, from `args`: its label, a
;; quoted name, kept as a constant whose type holds the name and whose value
;; is -1 (`check-read-helpers.fx`'s `k-variant-label`).
(define k-label-const (->* (symbol exp-list kxs) kxs)
  (lambda (op args xs)
    (if (and (symbol=? op 'blobref-variant!) (= (k-length xs) 2))
        (tagcase (car (cdr args))
          (e-sym (v a b abk) (list (car xs) (x-const (k-ty-new (ty-base v)) -1 a b abk)))
          (else y xs))
        xs)))
(define k-syns-count (->* (k-syns) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (k-syns-count (cdr xs))))))
;; The newest `n` of scope `s` onto `onto`: a module's file's parameters,
;; bound by the `plambda` around it, which it sees.
(define k-scope-newest (->* (int k-scope k-scope) k-scope)
  (lambda (n s onto)
    (if (or (<= n 0) (null? s)) onto (cons (car s) (k-scope-newest (- n 1) (cdr s) onto)))))
;; In a module with `include`s (its first item `%include`), a mark in the
;; description scope, `%include-scope`, so that a type name nothing else
;; defines is the modules included's (`k-type-unknown`, `TODO.md` §69); gone
;; with the module's scope.
(define k-include-mark (->* (mod-items) unit)
  (lambda (items)
    (if (and (not (null? items)) (symbol=? (car (extract (car items) 2)) '%include))
        (k-push-desc '%include-scope (ds-var -1 0))
        #u)))
;; Reading expressions (`check-resolve.fx`'s walk) and modules' items, one
;; recursive group: a module is an expression, and its items hold them.
(define-rec
  (k-resolve-all (->* ((listof exp acyclic)) kxs)
    (lambda (es)
      (if (null? es)
          nil
          (let* ((x (k-resolve-exp (car es))) (rest (k-resolve-all (cdr es))))
            (cons x rest)))))
  (k-resolve-exp (->* (exp) kx)
    (lambda (e)
      (tagcase e
        (e-var (s a b abk) (x-var s a b abk))
        (e-int (n a b abk) (x-const k-int n a b abk))
        (e-bool (v a b abk) (x-const k-bool (if v 1 0) a b abk))
        (e-str (v a b abk) (x-const k-string 0 a b abk))
        (e-char (v a b abk) (x-const k-char 0 a b abk))
        (e-float (v a b abk) (x-const k-f64 0 a b abk))
        (e-sym (v a b abk) (x-const k-symbol 0 a b abk))
        (e-unit (a b abk) (x-const k-unit 0 a b abk))
        (e-lambda (ps body a b abk)
          (let* ((params (k-resolve-params ps)) (x (k-resolve-exp body)))
            (x-lambda params x a b abk)))
        (e-app (f args a b abk)
          (let* ((fx (k-resolve-exp f)) (xs (k-resolve-all args))) (x-app fx xs a b abk)))
        (e-plambda (binders body a b abk)
          (let* ((saved (get k-dscope))
                 (lives (get k-lifetimes))
                 (bs (k-parse-binders binders))
                 ;; A procedure's regions and places outlive whatever its
                 ;; body binds.
                 (ordered (k-order-binders bs lives))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (set k-lifetimes lives) (x-plambda bs x a b abk))))
        (e-rlambda (r l a b abk)
          (let* ((rx (k-resolve-exp r)) (lx (k-resolve-exp l))) (x-rlambda rx lx a b abk)))
        (e-letregion (k name into body a b abk)
          (let* ((saved (get k-dscope))
                 ;; `letrena` and `letreap` make a place (which is also a
                 ;; region), `letregion` a region only.
                 (kind (if (or (= k 0) (= k 3)) 0 3))
                 (place (if (= k 3) (k-resolve-place into a b) (r-heap)))
                 (v (k-new-dvar-of name kind))
                 (lives (get k-lifetimes))
                 ;; A `letfreeze`'s data leaves in the place it freezes into,
                 ;; so it may be allocated only in that place or one outliving
                 ;; it: those are all it won't outlive.
                 (ordered (begin
                            ;; Fresh, so it aliases nothing (Lucassen's `PRIVATE`).
                            (k-set-distinct v)
                            (k-set-outer v (if (= k 3) (k-place-lives place) lives))
                            (set k-lifetimes (cons v lives))))
                 (pushed (k-push-desc name (ds-var v kind)))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (set k-lifetimes lives)
                   (x-letregion k v (k-freeze-into place) x a b abk))))
        (e-proj (body ds a b abk)
          (let* ((x (k-resolve-exp body)) (descs (k-resolve-descs ds))) (x-proj x descs a b abk)))
        (e-if (p c d a b abk)
          (let* ((px (k-resolve-exp p)) (cx (k-resolve-exp c)) (dx (k-resolve-exp d)))
            (x-if px cx dx a b abk)))
        (e-letrec (bs body a b abk)
          (let* ((rbs (k-resolve-letrec bs)) (x (k-resolve-exp body))) (x-letrec rbs x a b abk)))
        (e-let (bs body a b abk)
          (let* ((rbs (k-resolve-let bs)) (x (k-resolve-exp body))) (x-let rbs x a b abk)))
        (e-begin (es a b abk) (x-begin (k-resolve-all es) a b abk))
        (e-prompt (t body h a b abk)
          (let* ((tx (k-resolve-exp t)) (bx (k-resolve-exp body)) (hx (k-resolve-exp h)))
            (x-prompt tx bx hx a b abk)))
        (e-the (ty body a b abk)
          (let* ((t (k-parse-type ty)) (x (k-resolve-exp body))) (x-the t x a b abk)))
        (e-convention (c body a b abk)
          (let* ((cv (k-parse-conv c)) (x (k-resolve-exp body))) (x-convention cv x a b abk)))
        (e-bloblet (op i args got a b abk)
          (x-bloblet op i (k-label-const op args (k-resolve-all args)) a b abk))
        (e-product (fs a b abk) (x-product (k-resolve-fields fs nil a b) a b abk))
        (e-extract (body l got a b abk) (x-extract (k-resolve-exp body) l a b abk))
        (e-sum (l body a b abk) (x-sum l (k-resolve-exp body) a b abk))
        (e-tagcase (s arms els got a b abk)
          ;; The `else` arm, if any, is resolved as a `let` binding is.
          (let* ((sx (k-resolve-exp s))
                 (rarms (k-resolve-arms arms nil))
                 (rels (k-resolve-let els)))
            (x-tagcase sx rarms rels a b abk)))
        (e-module (items a b abk) (k-resolve-module-items items a b abk))
        ;; Its body read with `m`'s type names shadowing (`k-with-mark`).
        (e-with (m body a b abk)
          (let* ((saved (get k-dscope)) (marked (k-with-mark m)) (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (k-with-unmark m) (x-with m x a b abk)))))))
  (k-resolve-letrec (->* (exp-letrec-bs) k-letrec-bs)
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((star (set k-arrow-star (k-written-arrow-star? (extract (car bs) 2))))
                 (t (k-parse-type (extract (car bs) 2)))
                 (x (k-resolve-exp (extract (car bs) 3)))
                 (rest (k-resolve-letrec (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 t) (3 x)) rest)))))
  (k-resolve-let (->* (exp-let-bs) k-let-bs)
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((x (k-resolve-exp (extract (car bs) 2))) (rest (k-resolve-let (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 x)) rest)))))
  (k-resolve-fields (->* (exp-let-bs k-names int int) k-let-bs)
    (lambda (fs seen a b)
      (if (null? fs)
          nil
          (let ((l (extract (car fs) 1)))
            (if (k-has-name? seen l)
                (k-fail (string-append (k-quote (symbol->string l)) " appears twice") a b)
                (let* ((x (k-resolve-exp (extract (car fs) 2)))
                       (rest (k-resolve-fields (cdr fs) (cons l seen) a b)))
                  (cons (product (1 l) (2 x)) rest)))))))
  (k-resolve-arms (->* (exp-arms k-names) k-arms)
    (lambda (arms seen)
      (if (null? arms)
          nil
          (let* ((arm (car arms)) (tag (extract arm 1)))
            (if (k-has-name? seen tag)
                (k-fail (string-append (k-quote (symbol->string tag)) " has two arms")
                        (exp-start (extract arm 4)) (exp-end (extract arm 4)))
                (let* ((x (k-resolve-exp (extract arm 4)))
                       (rest (k-resolve-arms (cdr arms) (cons tag seen)))
                       (names (k-copy-names (extract arm 3))))
                  (cons (product (1 tag) (2 (extract arm 2)) (3 names) (4 x)) rest)))))))
  (k-resolve-rec-items (->* (syns-a exp-list) k-rec-read)
    (lambda (ts xs)
      (if (null? ts)
          (product (1 (the k-ids nil)) (2 (the kxs nil)))
          (let* ((star (set k-arrow-star (k-written-arrow-star? (car ts))))
                 (t (k-parse-type (car ts)))
                 (x (k-resolve-exp (car xs)))
                 (rest (k-resolve-rec-items (cdr ts) (cdr xs))))
            (product (1 (the k-ids (cons t (extract rest 1))))
                     (2 (the kxs (cons x (extract rest 2)))))))))
  ;; A module's `define-generative`: an abstract type, a type variable in scope
  ;; from here, its representation read in that scope; or, with parameters
  ;; (its head after its representation in `ts`), a type constructor: its
  ;; parameters read, then it, a variable of an arrow kind, and its
  ;; representation a `dlambda` of them (`check-kinds.fx`).
  (k-resolve-abstract (->* (k-names syns-a exp-list) k-item)
    (lambda (ns ts xs)
      (if (null? (cdr ts))
          (let* ((v (k-new-dvar-of (car ns) 2))
                 (pushed (k-push-desc (car ns) (ds-var v 2)))
                 (rep (k-parse-type (car ts))))
            (k-item-of 0 ns v (the k-ids (cons rep nil)) (k-resolve-all xs)))
          (let* ((ps (cdr (k-items (car (cdr ts)) "a module's definition")))
                 (saved (get k-dscope))
                 (bs (k-binders-each ps))
                 (restored (set k-dscope saved))
                 (kind (k-arrow (k-binder-kinds bs) 2))
                 (v (k-new-dvar-of (car ns) kind))
                 (noted (set k-abstract-funs (cons v (get k-abstract-funs))))
                 (pushed (k-push-desc (car ns) (ds-var v kind)))
                 (inner (get k-dscope))
                 (bound (k-push-binders bs))
                 (rep (k-parse-type (car ts)))
                 (back (set k-dscope inner))
                 (lam (k-ty-new (ty-lam bs (dt rep)))))
            (k-item-of 0 ns v (the k-ids (cons lam nil)) (k-resolve-all xs))))))
  ;; One item: an abstract type a type variable in scope from here (with
  ;; its representation read in that scope), and a transparent one an alias.
  (k-resolve-item (->* (mod-item) k-item)
    (lambda (it)
      (let ((k (extract it 1)) (ns (extract it 2)) (ts (extract it 3)) (xs (extract it 4)))
        (cond ((or (< k 0) (> k 3)) (k-item-of k ns -1 nil nil))
              ((= k 0) (k-resolve-abstract ns ts xs))
              ;; `(define-effect e E)`: its types the effect and a mark.
              ((and (= k 1) (not (null? (cdr ts))))
               (let ((e (k-parse-effect (car ts))))
                 (begin (k-push-desc (car ns) (ds-eff e))
                        (k-item-of k ns -1 (the k-ids (cons (k-effect-desc e) nil)) nil))))
              ((and (= k 1) (string=? (k-list-head (car ts)) "dlambda"))
               (let ((f (k-parse-fun (car ts) -1)))
                 (begin (k-push-desc (car ns) (ds-fun f))
                        (k-item-of k ns -1 (the k-ids (cons f nil)) nil))))
              ;; As a program's: declared ahead, or a knot of its own.
              ((= k 1)
               (let ((t (k-define-type (car ns) (car ts) (syn-start (car ts)) (syn-end (car ts)))))
                 (k-item-of k ns -1 (the k-ids (cons t nil)) nil)))
              ;; A `define*`'s types its type and a mark: its variable -2.
              ((and (= k 2) (not (null? ts)) (not (null? (cdr ts))))
               (let* ((both (if (k-written-arrow-star? (car ts))
                                (k-sfail (string-append "`define*` and `->*` each find what a "
                                                        "procedure does: write one")
                                         (car ts))
                                #u))
                      (t (k-parse-types (the syns-a (cons (car ts) nil)))) (x (k-resolve-all xs)))
                 (k-item-of k ns -2 t x)))
              ((= k 2)
               (let* ((star (if (null? ts) #u (set k-arrow-star (k-written-arrow-star? (car ts)))))
                      (t (if (null? ts) (the k-ids nil) (k-parse-types ts))) (x (k-resolve-all xs)))
                 (k-item-of k ns -1 t x)))
              (else
               (let ((r (k-resolve-rec-items ts xs)))
                 (k-item-of k ns -1 (extract r 1) (extract r 2))))))))
  (k-resolve-items (->* (mod-items) k-items)
    (lambda (items)
      (if (null? items)
          nil
          (let* ((x (k-resolve-item (car items))) (rest (k-resolve-items (cdr items))))
            (cons x rest)))))
  ;; A module's items, its type abbreviations declared ahead, as a program's
  ;; are (`k-ahead`): each defined once, by name, in scope before any is
  ;; read, so that they may name each other, and themselves, in any order;
  ;; each checked grounded once all are.
  (k-resolve-items-ahead (->* (mod-items) k-items)
    (lambda (items)
      (let* ((outer-names (get k-ahead-names)) (outer-filled (get k-ahead-filled))
             (names (k-module-type-names items))
             (cleared (begin (set k-ahead-names nil) (set k-ahead-filled nil)))
             (declared (k-ahead-declare names names))
             (got (the (ref k-items @t) (new nil)))
             ;; What is wrong in the items, kept until the state outside is back.
             (r (prompt k-tag (begin (set got (k-resolve-items items)) (k-done (k-te 0 nil)))
                        (lambda (r) r)))
             (filled (get k-ahead-filled)))
        (begin (set k-ahead-names outer-names)
               (set k-ahead-filled outer-filled)
               (tagcase r
                 (k-err (m a b) (k-fail m a b))
                 (else y (begin (k-ground-filled (k-filled-reversed filled nil))
                                (k-note-closed-filled filled))))
               (get got)))))
  ;; `(module item …)`: each item read in the scope of the descriptions
  ;; before it; read from a file, of the standard ones only, and its
  ;; parameters (`(module-parameters …)`), the `plambda` around it binds.
  (k-resolve-module-items (->* (mod-items int int int) kx)
    (lambda (items a b abk)
      (let ((k (k-items-kind items)) (saved (get k-dscope)))
        (cond
          ;; Said in each file on the way out, if loaded in a file read.
          ((< k 0)
           (if (>= a load-base)
               (k-fail-placed (symbol->string (car (extract (car items) 2))) a)
               (k-fail (symbol->string (car (extract (car items) 2))) a b)))
          ((not (null? (k-defined-twice items nil nil)))
           (k-fail (string-append (k-quote (symbol->string (car (k-defined-twice items nil nil))))
                                  " is defined twice in this module")
                   a b))
          ((> k 3)
           (let ((got (the (ref k-items @t) (new nil)))
                 (ps (k-syns-count (extract (car items) 3))))
             (begin (set k-dscope (k-scope-newest ps saved (get k-std-dscope)))
                    (k-in-loaded (lambda () (begin (k-include-mark items)
                                                   (set got (k-resolve-items-ahead items))))
                                 k a b)
                    (set k-dscope saved)
                    (x-module (get got) a b abk))))
          (else
           (let ((xs (begin (k-include-mark items) (k-resolve-items-ahead items))))
             (begin (set k-dscope saved) (x-module xs a b abk))))))))))))
