;;; The checker, in FX-26: first-class modules' descriptions, read
;;; (`docs/research/first-class-modules.md`, stage M2): `moduleof` and
;;; `select`, and a `module`'s items, in one recursive group with the
;;; expression walk (`check-resolve.fx`'s), as a module is an expression
;;; and its items hold them. Before `check-modules.fx`.

;; Its types (`check-modules-types.fx`, its file's after it), loaded before the
;; module so that they are not among its values; the module names what it
;; uses of them.
(define check-modules-types (load-module "fx26:check-modules-types.fx"))
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-modules-read-module (module
(define-type k-rec-read (select check-modules-types k-rec-read))
(define-type k-thunk-unit (select check-modules-types k-thunk-unit))

;; A module item as `x-module` has it.
(define k-item-of (subr (maxeff (read @globals) (alloc @t)) (int names int k-ids kxs) k-item)
  (lambda (k ns v ts xs) (product (1 k) (2 (k-copy-names ns)) (3 v) (4 ts) (5 xs))))
(define k-push-binders (subr kstate (k-binders) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (let ((v (extract (car bs) 1)))
          (begin (k-push-desc (k-dvar-name v) (ds-var v (extract (car bs) 2)))
                 (k-push-binders (cdr bs)))))))
;; The names a module's items give type abbreviations: each `define-type`
;; of a name, but of a `dlambda` or an effect.
(define k-module-type-names (subr (maxeff (read @globals) (read @s) (alloc @t)) (mod-items) k-names)
  (lambda (items)
    (if (null? items)
        nil
        (let* ((it (car items)) (ts (extract it 3)) (rest (k-module-type-names (cdr items))))
          (if (and (= (extract it 1) 1) (null? (cdr ts))
                   (not (string=? (k-list-head (car ts)) "dlambda")))
              (the k-names (cons (car (extract it 2)) rest))
              rest)))))
(define k-in-loaded (subr (maxeff checks spin) (k-thunk-unit int int int) unit)
  (lambda (f base a b)
    (let ((r (prompt k-tag (begin (f) (k-done (k-te 0 nil))) (lambda (r) r))))
      (tagcase r
        (k-err (m ea eb)
          (if (and (>= ea base) (< ea (+ base load-base)))
              (k-fail (in-loaded (get loaded) base m ea) a b)
              (k-fail m ea eb)))
        (else y #u)))))
;; What a module's first item says of where it was read: from its file, at
;; a base (> 3); not, and why (-1); or not from a file (0 to 3).
(define k-items-kind (subr pure (mod-items) int)
  (lambda (items) (if (null? items) 0 (extract (car items) 1))))
;; The names a module's item defines as descriptions (`types`), or as values:
;; a generative type's name is one, its two conversions values; as the Rust
;; checker's `defined_twice` counts them.
(define k-item-names (subr (maxeff (read @globals) (alloc @t)) (mod-item bool) k-names)
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
(define k-defined-twice (subr (maxeff kreads (alloc @t)) (mod-items k-names k-names) k-names)
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
(define k-syns-count (subr (read @globals) (k-syns) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (k-syns-count (cdr xs))))))
;; The newest `n` of scope `s` onto `onto`: a module's file's parameters,
;; bound by the `plambda` around it, which it sees.
(define k-scope-newest (subr (maxeff (read @globals) (alloc @t)) (int k-scope k-scope) k-scope)
  (lambda (n s onto)
    (if (or (<= n 0) (null? s)) onto (cons (car s) (k-scope-newest (- n 1) (cdr s) onto)))))
;; Reading expressions (`check-resolve.fx`'s walk) and modules' items, one
;; recursive group: a module is an expression, and its items hold them.
(define-rec
  (k-resolve-all (subr (maxeff checks spin) ((listof exp acyclic)) kxs)
    (lambda (es)
      (if (null? es)
          nil
          (let* ((x (k-resolve-exp (car es))) (rest (k-resolve-all (cdr es))))
            (cons x rest)))))
  (k-resolve-exp (subr (maxeff checks spin) (exp) kx)
    (lambda (e)
      (tagcase e
        (e-var (s a b) (x-var s a b))
        (e-int (n a b) (x-const k-int n a b))
        (e-bool (v a b) (x-const k-bool (if v 1 0) a b))
        (e-str (v a b) (x-const k-string 0 a b))
        (e-char (v a b) (x-const k-char 0 a b))
        (e-float (v a b) (x-const k-f64 0 a b))
        (e-sym (v a b) (x-const k-symbol 0 a b))
        (e-unit (a b) (x-const k-unit 0 a b))
        (e-lambda (ps body a b)
          (let* ((params (k-resolve-params ps)) (x (k-resolve-exp body))) (x-lambda params x a b)))
        (e-app (f args a b)
          (let* ((fx (k-resolve-exp f)) (xs (k-resolve-all args))) (x-app fx xs a b)))
        (e-plambda (binders body a b)
          (let* ((saved (get k-dscope))
                 (lives (get k-lifetimes))
                 (bs (k-parse-binders binders))
                 ;; A procedure's regions and places outlive whatever its
                 ;; body binds.
                 (ordered (k-order-binders bs lives))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (set k-lifetimes lives) (x-plambda bs x a b))))
        (e-rlambda (r l a b)
          (let* ((rx (k-resolve-exp r)) (lx (k-resolve-exp l))) (x-rlambda rx lx a b)))
        (e-letregion (k name into body a b)
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
                            (k-set-outer v (if (= k 3) (k-place-lives place) lives))
                            (set k-lifetimes (cons v lives))))
                 (pushed (k-push-desc name (ds-var v kind)))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (set k-lifetimes lives)
                   (x-letregion k v (k-freeze-into place) x a b))))
        (e-proj (body ds a b)
          (let* ((x (k-resolve-exp body)) (descs (k-resolve-descs ds))) (x-proj x descs a b)))
        (e-if (p c d a b)
          (let* ((px (k-resolve-exp p)) (cx (k-resolve-exp c)) (dx (k-resolve-exp d)))
            (x-if px cx dx a b)))
        (e-letrec (bs body a b)
          (let* ((rbs (k-resolve-letrec bs)) (x (k-resolve-exp body))) (x-letrec rbs x a b)))
        (e-let (bs body a b)
          (let* ((rbs (k-resolve-let bs)) (x (k-resolve-exp body))) (x-let rbs x a b)))
        (e-begin (es a b) (x-begin (k-resolve-all es) a b))
        (e-prompt (t body h a b)
          (let* ((tx (k-resolve-exp t)) (bx (k-resolve-exp body)) (hx (k-resolve-exp h)))
            (x-prompt tx bx hx a b)))
        (e-the (ty body a b)
          (let* ((t (k-parse-type ty)) (x (k-resolve-exp body))) (x-the t x a b)))
        (e-convention (c body a b)
          (let* ((cv (k-parse-conv c)) (x (k-resolve-exp body))) (x-convention cv x a b)))
        (e-bloblet (op i args a b) (x-bloblet op i (k-resolve-all args) a b))
        (e-product (fs a b) (x-product (k-resolve-fields fs nil a b) a b))
        (e-extract (body l a b) (x-extract (k-resolve-exp body) l a b))
        (e-sum (l body a b) (x-sum l (k-resolve-exp body) a b))
        (e-tagcase (s arms els a b)
          ;; The `else` arm, if any, is resolved as a `let` binding is.
          (let* ((sx (k-resolve-exp s))
                 (rarms (k-resolve-arms arms nil))
                 (rels (k-resolve-let els)))
            (x-tagcase sx rarms rels a b)))
        (e-module (items a b) (k-resolve-module-items items a b))
        (e-with (m body a b) (x-with m (k-resolve-exp body) a b)))))
  (k-resolve-letrec (subr (maxeff checks spin) (exp-letrec-bs) k-letrec-bs)
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((t (k-parse-type (extract (car bs) 2)))
                 (x (k-resolve-exp (extract (car bs) 3)))
                 (rest (k-resolve-letrec (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 t) (3 x)) rest)))))
  (k-resolve-let (subr (maxeff checks spin) (exp-let-bs) k-let-bs)
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((x (k-resolve-exp (extract (car bs) 2))) (rest (k-resolve-let (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 x)) rest)))))
  (k-resolve-fields (subr (maxeff checks spin) (exp-let-bs k-names int int) k-let-bs)
    (lambda (fs seen a b)
      (if (null? fs)
          nil
          (let ((l (extract (car fs) 1)))
            (if (k-has-name? seen l)
                (k-fail (string-append (k-quote (symbol->string l)) " appears twice") a b)
                (let* ((x (k-resolve-exp (extract (car fs) 2)))
                       (rest (k-resolve-fields (cdr fs) (cons l seen) a b)))
                  (cons (product (1 l) (2 x)) rest)))))))
  (k-resolve-arms (subr (maxeff checks spin) (exp-arms k-names) k-arms)
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
  (k-resolve-rec-items (subr (maxeff checks spin) (syns-a exp-list) k-rec-read)
    (lambda (ts xs)
      (if (null? ts)
          (product (1 (the k-ids nil)) (2 (the kxs nil)))
          (let* ((t (k-parse-type (car ts)))
                 (x (k-resolve-exp (car xs)))
                 (rest (k-resolve-rec-items (cdr ts) (cdr xs))))
            (product (1 (the k-ids (cons t (extract rest 1))))
                     (2 (the kxs (cons x (extract rest 2)))))))))
  ;; A module's `define-generative`: an abstract type, a type variable in scope
  ;; from here, its representation read in that scope; or, with parameters
  ;; (its head after its representation in `ts`), a type constructor: its
  ;; parameters read, then it, a variable of an arrow kind, and its
  ;; representation a `dlambda` of them (`check-kinds.fx`).
  (k-resolve-abstract (subr (maxeff checks spin) (k-names syns-a exp-list) k-item)
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
  (k-resolve-item (subr (maxeff checks spin) (mod-item) k-item)
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
               (let* ((t (k-parse-types (the syns-a (cons (car ts) nil)))) (x (k-resolve-all xs)))
                 (k-item-of k ns -2 t x)))
              ((= k 2)
               (let* ((t (if (null? ts) (the k-ids nil) (k-parse-types ts))) (x (k-resolve-all xs)))
                 (k-item-of k ns -1 t x)))
              (else
               (let ((r (k-resolve-rec-items ts xs)))
                 (k-item-of k ns -1 (extract r 1) (extract r 2))))))))
  (k-resolve-items (subr (maxeff checks spin) (mod-items) k-items)
    (lambda (items)
      (if (null? items)
          nil
          (let* ((x (k-resolve-item (car items))) (rest (k-resolve-items (cdr items))))
            (cons x rest)))))
  ;; A module's items, its type abbreviations declared ahead, as a program's
  ;; are (`k-ahead`): each defined once, by name, in scope before any is
  ;; read, so that they may name each other, and themselves, in any order;
  ;; each checked grounded once all are.
  (k-resolve-items-ahead (subr (maxeff checks spin) (mod-items) k-items)
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
  (k-resolve-module-items (subr (maxeff checks spin) (mod-items int int) kx)
    (lambda (items a b)
      (let ((k (k-items-kind items)) (saved (get k-dscope)))
        (cond
          ((< k 0) (k-fail (symbol->string (car (extract (car items) 2))) a b))
          ((not (null? (k-defined-twice items nil nil)))
           (k-fail (string-append (k-quote (symbol->string (car (k-defined-twice items nil nil))))
                                  " is defined twice in this module")
                   a b))
          ((> k 3)
           (let ((got (the (ref k-items @t) (new nil)))
                 (ps (k-syns-count (extract (car items) 3))))
             (begin (set k-dscope (k-scope-newest ps saved (get k-std-dscope)))
                    (k-in-loaded (lambda () (set got (k-resolve-items-ahead items))) k a b)
                    (set k-dscope saved)
                    (x-module (get got) a b))))
          (else
           (let ((xs (k-resolve-items-ahead items)))
             (begin (set k-dscope saved) (x-module xs a b)))))))))))

(define k-defined-twice (with check-modules-read-module k-defined-twice))
(define k-in-loaded (with check-modules-read-module k-in-loaded))
(define k-push-binders (with check-modules-read-module k-push-binders))
(define k-resolve-exp (with check-modules-read-module k-resolve-exp))
