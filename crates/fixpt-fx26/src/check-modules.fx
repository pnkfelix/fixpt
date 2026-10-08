;;; The checker, in FX-26: first-class modules' descriptions
;;; (`docs/research/first-class-modules.md`, stage M2): reading `moduleof`
;;; and `select`, and a `module`'s items; a module's type bound to a name,
;;; its abstract types named for that binding; `select`s resolved; what
;;; may not leave a binding's scope. The Rust checker's `modules.rs`, as it
;;; reads and resolves. Part of the checker, `check-types.fx` first.
;;;
;;; A module's type is an existential package: its abstract types are
;;; binders of its `moduleof`. A variable of that type has them renamed for
;;; itself as it is bound (`k-name-module`), each a type equal only to
;;; itself, named `m..t`; `(select m t)` is that type. Its rules, `module`
;;; and `with`, are `check-module-rules.fx`'s.

;;; ------------------------------------------------------------ reading


;; Kind `s`, or -1 where `k-parse-kind` would refuse it: for a reader that
;; gives its own message instead (`moduleof`'s `abs`).

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-modules-module (module
;; A `define-rec`'s types and expressions, each type read before its
;; expression, as the Rust parser reads them.
(define-type k-rec-read (productof (1 k-ids) (2 kxs)))
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
;; Run `f`; an error it makes in the file read at `base` (`load-module`)
;; said at `a`..`b`, with where in the file, as the Rust checker says it.
(define-type k-thunk-unit (subr (maxeff checks spin) () unit))
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
             (begin (set k-dscope saved) (x-module xs a b)))))))))

;;; ------------------------------------------------------------ walking types

;; Descriptions `ds`, the `i`th on, each of the kind of `ks` it is given for.
;; Function `f`, as an error says it: its type, quoted. Printed only for an
;; error, as printing a type is not cheap.
(define k-fun-shown (subr kbuilds (int) string) (lambda (f) (k-quote (k-show-ty f))))
(define k-check-app-args (subr (maxeff checks spin) (int k-descs k-ids int int int) unit)
  (lambda (f ds ks i a b)
    (cond ((null? ds) #u)
          ((not (k-desc-of-kind? (car ds) (car ks)))
           (k-fail (k-cat5 (k-fun-shown f) " takes a " (k-kind-text (car ks)) " as description "
                           (int->string i))
                   a b))
          (else (k-check-app-args f (cdr ds) (cdr ks) (+ i 1) a b)))))
;; Function `f` applied to `ds`, at `a`..`b`: given as many descriptions as
;; it takes, each of the kind it takes, and giving a type.
(define k-check-app (subr (maxeff checks spin) (int k-descs int int) unit)
  (lambda (f ds a b)
    (let ((k (k-fun-kind f)))
      (cond ((< k 0) #u)
            ((not (k-arrow-kind? k))
             (k-fail (string-append (k-fun-shown f) " is not a description function: it is applied")
                     a b))
            ((not (= (k-length (k-arrow-params k)) (k-length ds)))
             (k-fail (k-cat5 (k-fun-shown f) " takes " (int->string (k-length (k-arrow-params k)))
                             " description(s), and has " (int->string (k-length ds)))
                     a b))
            ((not (or (= (k-arrow-result k) 2) (= (k-arrow-result k) 4)))
             (k-fail (k-cat4 (k-fun-shown f) " gives a description of kind "
                             (k-kind-text (k-arrow-result k)) ", not a type")
                     a b))
            (else (k-check-app-args f ds (k-arrow-params k) 1 a b))))))
;; Each description function applied in `t` given what it takes, at
;; `a`..`b`: checked where a `select` has just said what the function is.
(define-rec
  (k-check-apps-from (subr (maxeff checks spin) (int k-seen int int) unit)
    (lambda (t seen a b)
      (let ((t (k-resolve t)))
        (if (k-seen? seen t)
            #u
            (begin
              (tagcase (k-get t) (ty-app (f ds) (k-check-app f ds a b)) (else y #u))
              (k-check-apps-each (k-ty-kids t) seen a b))))))
  (k-check-apps-each (subr (maxeff checks spin) (k-ids k-seen int int) unit)
    (lambda (ts seen a b)
      (if (null? ts)
          #u
          (begin (k-check-apps-from (car ts) seen a b) (k-check-apps-each (cdr ts) seen a b))))))
(define k-check-apps (subr (maxeff checks spin) (int int int) unit)
  (lambda (t a b) (k-check-apps-from t (k-new-seen) a b)))
;; Whether type variable `v` is somewhere in `t`, or in `ts`; `seen`, the
;; nodes walked.
(define-rec
  (k-mentions-from? (subr (maxeff kstate spin) (int int (ref k-ids @t)) bool)
    (lambda (t v seen)
      (let ((t (k-resolve t)))
        (if (k-has-id? (get seen) t)
            #f
            (begin
              (set seen (cons t (get seen)))
              (or (tagcase (k-get t) (ty-var (w) (= w v)) (else y #f))
                  (k-any-mentions? (k-ty-kids t) v seen)))))))
  (k-any-mentions? (subr (maxeff kstate spin) (k-ids int (ref k-ids @t)) bool)
    (lambda (ts v seen)
      (and (not (null? ts))
           (or (k-mentions-from? (car ts) v seen) (k-any-mentions? (cdr ts) v seen))))))
(define k-mentions-var? (subr (maxeff kstate spin) (int int) bool)
  (lambda (t v) (k-mentions-from? t v (the (ref k-ids @t) (new nil)))))
;; The first of `vs` that `t` mentions, or -1.
(define k-first-mentioned (subr (maxeff kstate spin) (int k-ids) int)
  (lambda (t vs)
    (cond ((null? vs) -1)
          ((k-mentions-var? t (car vs)) (car vs))
          (else (k-first-mentioned t (cdr vs))))))

;;; ------------------------------------------------------------ naming

;; Whether `v` was made for a module's abstract type as it was bound.
(define k-module-var? (subr kreads (int) bool)
  (lambda (v) (k-has-id? (get k-module-vars) v)))
;; Abstract types `abs` renamed for a binding, each `prefix` and its name:
;; the new ones, and what each old one becomes.
(define-type k-renamed (productof (1 k-parts) (2 k-map)))
(define k-rename-abs (subr (maxeff kstate spin) (string k-parts) k-renamed)
  (lambda (prefix abs)
    (if (null? abs)
        (product (1 (the k-parts nil)) (2 (the k-map nil)))
        (let* ((a (extract (car abs) 1))
               (k (k-dvar-kind (extract (car abs) 2)))
               (w (k-new-dvar-of (string->symbol (string-append prefix (symbol->string a))) k))
               (noted (begin (set k-skolems (cons w (get k-skolems)))
                             (set k-module-vars (cons w (get k-module-vars)))
                             (if (= k 2) #u (set k-abstract-funs (cons w (get k-abstract-funs))))))
               (to (if (= k 2) (dt (k-ty-new (ty-var w))) (df (k-ty-new (ty-var w)))))
               (rest (k-rename-abs prefix (cdr abs))))
          (product (1 (the k-parts (cons (product (1 a) (2 w)) (extract rest 1))))
                   (2 (the k-map (cons (cons (extract (car abs) 2) to) (extract rest 2)))))))))
;; Parts `ps`, each type with `m` for its binders.
(define k-subst-each (subr (maxeff kstate spin) (k-parts k-map) k-parts)
  (lambda (ps m)
    (if (null? ps)
        nil
        (let* ((t (k-subst (extract (car ps) 2) m)) (rest (k-subst-each (cdr ps) m)))
          (cons (product (1 (extract (car ps) 1)) (2 t)) rest)))))
;; A module's type, bound to `name`: its abstract types renamed for this
;; binding, each `name..t`, kept until the binding's scope ends. Any other
;; type as it is.
(define k-name-module (subr (maxeff kstate spin) (symbol int) int)
  (lambda (name t)
    (tagcase (k-get (k-resolve t))
      (ty-module (abs ds vs)
        (if (null? abs)
            t
            (let* ((r (k-rename-abs (string-append (symbol->string name) "..") abs))
                   (ds2 (k-subst-each ds (extract r 2)))
                   (vs2 (k-subst-each vs (extract r 2))))
              (k-ty-new (ty-module (extract r 1) ds2 vs2)))))
      (else y t))))
;; Of the sizes and abstract types `vs`, named in a scope that `t` leaves:
;; the sizes, to be forgotten. A module's abstract type cannot be: nothing
;; may leave its binding's scope still mentioning it.
(define k-sizes-of (subr (maxeff kreads (alloc @t)) (k-ids) k-ids)
  (lambda (vs)
    (cond ((null? vs) nil)
          ((k-module-var? (car vs)) (k-sizes-of (cdr vs)))
          (else (cons (car vs) (k-sizes-of (cdr vs)))))))
(define k-escaping (subr (maxeff kstate spin) (int k-ids) int)
  (lambda (t vs)
    (cond ((null? vs) -1)
          ((and (k-module-var? (car vs)) (k-mentions-var? t (car vs))) (car vs))
          (else (k-escaping t (cdr vs))))))
(define k-unescaped (subr (maxeff checks spin) (int k-ids int int) k-ids)
  (lambda (t vs a b)
    (let ((v (k-escaping t vs)))
      (if (< v 0)
          (k-sizes-of vs)
          (k-fail (k-cat5 "this is a " (k-show-ty t) ", and `" (k-dvar-string v)
                          (string-append "` is a module's abstract type, not known outside "
                                         "the scope where the module is named"))
                  a b)))))

;;; ------------------------------------------------------------ select

;; Each `(select m n)` node in `t`, onto `out` (newest first); the
;; nodes walked, `seen`.
;; `(select m n)`, as an error shows it.
(define k-select-shown (subr (read @globals) (symbol symbol) string)
  (lambda (m n) (k-cat5 "`(select " (symbol->string m) " " (symbol->string n) ")`")))
;; The type component `n` of parts `ps`, or -1.
(define k-comp-find (subr kreads (k-parts symbol) int)
  (lambda (ps n)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) n) (extract (car ps) 2))
          (else (k-comp-find (cdr ps) n)))))
;; What `(select m n)` is, `m` a module bound to a type of abstract types
;; `abs` and descriptions `ds`: its abstract type `n`, or its description;
;; an error at `a`..`b` if it has neither.
(define k-select-component (subr (maxeff checks spin) (symbol symbol k-parts k-parts int int) int)
  (lambda (m n abs ds a b)
    (let ((v (k-comp-find abs n)) (d (k-comp-find ds n)))
      (cond ((>= v 0) (k-ty-new (ty-var v)))
            ((>= d 0) d)
            (else (k-fail (k-cat5 (k-select-shown m n) ": `" (symbol->string m) "` has no type `"
                                  (string-append (symbol->string n) "`"))
                          a b))))))
;; What an error about `(select m n)` starts with; made only for an error.
(define k-select-prefix (subr (read @globals) (symbol symbol) string)
  (lambda (m n) (k-cat3 (k-select-shown m n) ": `" (symbol->string m))))
;; A global module's type, as `select` node `node` names it: that node from
;; now on, linked to `to`, so that whatever leads to it is not rebuilt, and
;; is shared, and shown by its name. Not a family, which is read as the
;; `select` it is; nor a local module's, which may differ by scope.
(define k-link-global-select (subr (maxeff kstate spin) (symbol int int) unit)
  (lambda (m node to)
    (if (and (or (k-global? m) (k-fixed? m))
             (tagcase (k-get to)
               (ty-lam (bs d) #f)
               (ty-var (v) (= (k-dvar-kind v) 2))
               (else y #t)))
        (k-set-link node to)
        #u)))
;; Module `m`'s component `n`, as select node `node` names it, linked.
(define k-link-alias (subr (maxeff kstate spin) (symbol symbol int) unit)
  (lambda (m n node)
    (let ((mt (k-lookup m)))
      (if (< mt 0)
          #u
          (tagcase (k-get mt)
            (ty-module (abs ds vs)
              (let ((v (k-comp-find abs n)) (d (k-comp-find ds n)))
                (cond ((>= v 0) (k-link-global-select m node (k-ty-new (ty-var v))))
                      ((>= d 0) (k-link-global-select m node d))
                      (else #u))))
            (else y #u))))))
;; Each `define-type` alias in `ds`, `(define-type t (select m t))`, of the
;; global module `m` just bound, linked now to what it names: the aliases are
;; declared ahead of `m`, and a type naming one shows by its name from the
;; first, not once some later resolution meets it. As the Rust checker's
;; `link_aliases`.
(define k-link-aliases (subr (maxeff kstate spin) (symbol k-scope) unit)
  (lambda (m ds)
    (if (null? ds)
        #u
        (begin
          (tagcase (cdr (car ds))
            (ds-rec (t)
              (tagcase (k-get t)
                (ty-select (x n) (if (symbol=? x m) (k-link-alias m n (k-resolve t)) #u))
                (else y #u)))
            (else z #u))
          (k-link-aliases m (cdr ds))))))
;; What each of `found` is where it is checked, at `a`..`b`.
(define k-selection (subr (maxeff checks spin) (k-selects int int) k-selects)
  (lambda (found a b)
    (if (null? found)
        nil
        (let* ((m (extract (car found) 1)) (n (extract (car found) 2))
               (mt (k-lookup m))
               (to (if (< mt 0)
                       (k-fail (string-append (k-select-prefix m n) "` is not bound here") a b)
                       (tagcase (k-get mt)
                         (ty-module (abs ds vs) (k-select-component m n abs ds a b))
                         (else y (k-fail (k-cat4 (k-select-prefix m n) "` is a " (k-show-ty mt)
                                                 ", not a module")
                                         a b)))))
               (linked (k-link-global-select m (extract (car found) 3) to))
               (rest (k-selection (cdr found) a b)))
          (cons (product (1 m) (2 n) (3 to)) rest)))))
;;; ------------------------------------------------------------ effects selected

;; The entry of `ss` for variable `v`, or none.
(define k-effect-sel-var (subr (maxeff (read @globals) (read @t)) (k-effect-sels int) k-effect-sels)
  (lambda (ss v)
    (cond ((null? ss) nil)
          ((= (extract (car ss) 3) v) ss)
          (else (k-effect-sel-var (cdr ss) v)))))
;; `e`'s effect variables that stand for `(select m e)`s, onto `out`, each
;; once.
(define k-esels-note (subr (maxeff kstate spin) (k-eff (ref k-effect-sels @t)) unit)
  (lambda (e out)
    (if (null? e)
        #u
        (begin
          (tagcase (car e)
            (a-var (v)
              (let ((sel (k-effect-sel-var (get k-effect-selects) v)))
                (if (or (null? sel) (not (null? (k-effect-sel-var (get out) v))))
                    #u
                    (set out (cons (car sel) (get out))))))
            (else y #u))
          (k-esels-note (cdr e) out)))))
;; The effects of descriptions `ds`, noted.
(define k-esels-descs (subr (maxeff kstate spin) (k-descs (ref k-effect-sels @t)) unit)
  (lambda (ds out)
    (if (null? ds)
        #u
        (begin (tagcase (car ds) (de (e) (k-esels-note e out)) (else x #u))
               (k-esels-descs (cdr ds) out)))))
;; Each effect `(select m e)` in `t`, onto `out`; the nodes walked, `seen`.
(define-rec
  (k-esels-from (subr (maxeff kstate spin) (int k-seen (ref k-effect-sels @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-seen? seen t)
            #u
            (begin
              (tagcase (k-get t)
                (ty-subr (e ps r cv) (k-esels-note e out))
                (ty-tag (a h e r) (k-esels-note e out))
                (ty-comp (a h e r) (k-esels-note e out))
                (ty-lam (bs d) (k-esels-descs (the k-descs (list d)) out))
                (ty-app (f ds) (k-esels-descs ds out))
                (ty-named (g ds) (k-esels-descs ds out))
                (else y #u))
              (k-esels-each (k-ty-kids t) seen out))))))
  (k-esels-each (subr (maxeff kstate spin) (k-ids k-seen (ref k-effect-sels @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-esels-from (car ts) seen out) (k-esels-each (cdr ts) seen out))))))
;; The effect `(select m e)`s in `t`, in the order met.
(define k-effect-selects-in (subr (maxeff kstate spin) (int) k-effect-sels)
  (lambda (t)
    (if (null? (get k-effect-selects))
        nil
        (let ((out (the (ref k-effect-sels @t) (new nil))))
          (begin (k-esels-from t (k-new-seen) out) (reverse (get out)))))))
;; The effect a module's description `d` is, in a list; none if not one.
(define k-desc-effect (subr (maxeff kreads spin) (int) (listof k-eff acyclic))
  (lambda (d)
    (tagcase (k-get d)
      (ty-lam (bs body)
        (if (null? bs)
            (tagcase body
              (de (e) (the (listof k-eff acyclic) (list e)))
              (else x (the (listof k-eff acyclic) nil)))
            (the (listof k-eff acyclic) nil)))
      (else y (the (listof k-eff acyclic) nil)))))
;; Module `m`'s effect `e`, as its type says, `m` bound here; or an error
;; at `a`..`b`.
(define k-selected-effect (subr (maxeff checks spin) (symbol symbol int int) k-eff)
  (lambda (m e a b)
    (let ((mt (k-lookup m)))
      (if (< mt 0)
          (begin (k-fail (string-append (k-select-prefix m e) "` is not bound here") a b)
                 (the k-eff nil))
          (tagcase (k-get mt)
            (ty-module (abs ds vs)
              (let* ((d (k-comp-find ds e))
                     (x (if (< d 0) (the (listof k-eff acyclic) nil) (k-desc-effect d))))
                (if (null? x)
                    (let ((msg (k-cat4 (k-select-prefix m e) "` has no effect `"
                                       (symbol->string e) "`")))
                      (begin (k-fail msg a b) (the k-eff nil)))
                    (car x))))
            (else y (begin (k-fail (k-cat4 (k-select-prefix m e) "` is a " (k-show-ty mt)
                                           ", not a module")
                                   a b)
                           (the k-eff nil))))))))
;; What each effect selected stands for, as a substitution.
(define k-effects-given (subr (maxeff checks spin) (k-effect-sels int int) k-map)
  (lambda (ss a b)
    (if (null? ss)
        nil
        (let* ((x (car ss)) (e (k-selected-effect (extract x 1) (extract x 2) a b))
               (rest (k-effects-given (cdr ss) a b)))
          (the k-map (cons (cons (extract x 3) (de e)) rest))))))
;; Whether `e` names a variable `given` replaces.
(define k-eff-given? (subr (maxeff kreads spin) (k-eff k-map) bool)
  (lambda (e given)
    (and (not (null? e))
         (or (tagcase (car e) (a-var (v) (not (null? (k-map-find given v)))) (else y #f))
             (k-eff-given? (cdr e) given)))))
(define k-descs-given? (subr (maxeff kreads spin) (k-descs k-map) bool)
  (lambda (ds given)
    (and (not (null? ds))
         (or (tagcase (car ds) (de (e) (k-eff-given? e given)) (else x #f))
             (k-descs-given? (cdr ds) given)))))
;; Whether node `n` is itself what a `select`'s resolution changes: a
;; `select`, a `(select $k t)`, or an effect naming a variable `given`
;; replaces.
(define k-select-seed? (subr (maxeff kreads spin) (int k-map) bool)
  (lambda (n given)
    (tagcase (k-get n)
      (ty-select (m s) #t)
      (ty-param (k s) #t)
      (ty-subr (e ps r cv) (k-eff-given? e given))
      (ty-tag (a h e r) (k-eff-given? e given))
      (ty-comp (a h e r) (k-eff-given? e given))
      (ty-lam (bs d) (k-descs-given? (the k-descs (list d)) given))
      (ty-app (f ds) (k-descs-given? ds given))
      (ty-named (g ds) (k-descs-given? ds given))
      (else y #f))))
;; The nodes reached from `t`, through `k-ty-kids`, onto `out`; `e` the walk.
(define-rec
  (k-nodes-from (subr (maxeff kstate spin) (int int (ref k-ids @t)) unit)
    (lambda (t e out)
      (let ((t (k-resolve t)))
        (if (k-visit? t e)
            #u
            (begin (set out (cons t (get out))) (k-nodes-each (k-ty-kids t) e out))))))
  (k-nodes-each (subr (maxeff kstate spin) (k-ids int (ref k-ids @t)) unit)
    (lambda (ts e out)
      (if (null? ts) #u (begin (k-nodes-from (car ts) e out) (k-nodes-each (cdr ts) e out))))))
;; Whether a child of `n` is marked `d`.
(define k-kid-marked? (subr (maxeff kstate spin) (k-ids int) bool)
  (lambda (ks d)
    (and (not (null? ks)) (or (= (k-keep-at (k-resolve (car ks))) d) (k-kid-marked? (cdr ks) d)))))
;; Each of `ns` not marked `d` with a child that is, marked `d`: whether any.
(define k-mark-parents (subr (maxeff kstate spin) (k-ids int bool) bool)
  (lambda (ns d changed)
    (cond ((null? ns) changed)
          ((and (not (= (k-keep-at (car ns)) d)) (k-kid-marked? (k-ty-kids (car ns)) d))
           (begin (k-keep-set! (car ns) d) (k-mark-parents (cdr ns) d #t)))
          (else (k-mark-parents (cdr ns) d changed)))))
(define k-mark-until-still (subr (maxeff kstate spin) (k-ids int) unit)
  (lambda (ns d) (if (k-mark-parents ns d #f) (k-mark-until-still ns d) #u)))
;; Each of `ns` that is itself what resolving changes (`k-select-seed?`),
;; marked `d`.
(define k-mark-seeds (subr (maxeff kstate spin) (k-ids k-map int) unit)
  (lambda (ns given d)
    (if (null? ns)
        #u
        (begin (if (k-select-seed? (car ns) given) (k-keep-set! (car ns) d) #u)
               (k-mark-seeds (cdr ns) given d)))))
(define k-mark-kept (subr (maxeff kstate spin) (k-ids int int) unit)
  (lambda (ns d k)
    (if (null? ns)
        #u
        (begin (if (= (k-keep-at (car ns)) d) #u (k-keep-set! (car ns) k))
               (k-mark-kept (cdr ns) d k)))))
;; The nodes of `t` from which no `select` is reached, marked kept: the
;; epoch they are marked with. As the Rust checker's `select_clean`.
(define k-select-clean (subr (maxeff kstate spin) (int k-map) int)
  (lambda (t given)
    (let* ((out (the (ref k-ids @t) (new nil)))
           (walked (k-nodes-from t (k-new-epoch) out))
           (ns (get out))
           (d (k-new-epoch))
           (seeded (k-mark-seeds ns given d))
           (spread (k-mark-until-still ns d))
           (k (k-new-epoch)))
      (begin (k-mark-kept ns d k) k))))
;; `t` with each `(select m n)` in it replaced by what it is: `m`'s
;; abstract type `n`, as `m` was bound, or its description `n`. An error
;; at `a`..`b` if one is not.
(define k-resolve-selects (subr (maxeff checks spin) (int int int) int)
  (lambda (t a b)
    (let ((found (k-selects-in t)) (efound (k-effect-selects-in t)))
      (if (and (null? found) (null? efound))
          t
          (let ((given (k-effects-given efound a b)) (outer (get k-select-map)))
            (begin
              (set k-select-map (k-selection found a b))
              ;; Only what leads to a `select` is rebuilt; the rest stays
              ;; itself.
              (let* ((outer-keep (get k-subst-keep))
                     (kept (set k-subst-keep (k-select-clean t given)))
                     (r (k-subst-memo t given (k-new-smemo))))
                (begin (set k-subst-keep outer-keep)
                       (set k-select-map outer)
                       (k-check-apps r a b)
                       r))))))))
;; The same for a type written as `s`, at `s`.
(define k-select-syn (subr (maxeff checks spin) (int syn) int)
  (lambda (t s) (k-resolve-selects t (syn-start s) (syn-end s))))
;; The same for the types a `letrec`'s bindings `bs` are declared, at the
;; `letrec`, `a`..`b`.
(define k-letrec-selected (subr (maxeff checks spin) (k-letrec-bs int int) k-letrec-bs)
  (lambda (bs a b)
    (if (null? bs)
        nil
        (let* ((x (car bs))
               (t (k-resolve-selects (extract x 2) a b))
               (rest (k-letrec-selected (cdr bs) a b)))
          (cons (product (1 (extract x 1)) (2 t) (3 (extract x 3))) rest)))))
;; The first `select` of `found` from one of `params`, or none.
(define k-select-from (subr kreads (k-selects k-names) k-selects)
  (lambda (found params)
    (cond ((null? found) nil)
          ((k-has-name? params (extract (car found) 1)) (cons (car found) nil))
          (else (k-select-from (cdr found) params)))))
;; `t` resolved, at `a`..`b`, where `params` are not yet bound, and so may
;; not be selected from: one that names the parameter it is the type of, or
;; a later one.
(define k-resolve-outside (subr (maxeff checks spin) (int k-names int int) int)
  (lambda (t params a b)
    (let ((dependent (k-select-from (k-selects-in t) params)))
      (if (null? dependent)
          (k-resolve-selects t a b)
          (let ((s (car dependent)))
            (k-fail (string-append
                     (k-select-shown (extract s 1) (extract s 2))
                     (string-append " names a parameter of the same `lambda`: "
                                    "a dependent type, not supported yet"))
                    a b))))))
(define k-binding-names (subr kmakes (k-bindings) k-names)
  (lambda (bs) (if (null? bs) nil (cons (car (car bs)) (k-binding-names (cdr bs))))))))

(define k-push-binders (with check-modules-module k-push-binders))
(define k-in-loaded (with check-modules-module k-in-loaded))
(define k-defined-twice (with check-modules-module k-defined-twice))
(define k-resolve-exp (with check-modules-module k-resolve-exp))
(define k-check-apps-each (with check-modules-module k-check-apps-each))
(define k-first-mentioned (with check-modules-module k-first-mentioned))
(define k-subst-each (with check-modules-module k-subst-each))
(define k-name-module (with check-modules-module k-name-module))
(define k-unescaped (with check-modules-module k-unescaped))
(define k-link-global-select (with check-modules-module k-link-global-select))
(define k-link-aliases (with check-modules-module k-link-aliases))
(define k-resolve-selects (with check-modules-module k-resolve-selects))
(define k-select-syn (with check-modules-module k-select-syn))
(define k-letrec-selected (with check-modules-module k-letrec-selected))
(define k-resolve-outside (with check-modules-module k-resolve-outside))
(define k-binding-names (with check-modules-module k-binding-names))
