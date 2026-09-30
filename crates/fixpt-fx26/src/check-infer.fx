;;; The checker, in FX-26: instantiation, `tagcase`, and what synthesis needs.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ instantiation
;;; A projection left out: the binders of a `poly` solved by matching (local
;;; type inference). A type binder must be solved; an effect binder nothing
;;; constrains is `pure`; a region binder nothing constrains is a fresh
;;; region.

(define-type k-solved (ref k-map @t))
(define k-append-binders (subr kmakes (k-binders k-binders) k-binders)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (k-append-binders (cdr xs) ys)))))
;; Binders, and the type under them.
(define-type k-bound-body (productof (1 k-binders) (2 int)))
(define k-binders-from (subr (maxeff kmakes spin) (int k-binders) k-bound-body)
  (lambda (t acc)
    (tagcase (k-get t)
      (ty-poly (bs body) (k-binders-from (k-resolve body) (k-append-binders acc bs)))
      (else y (product (1 acc) (2 t))))))

;; The binders of `t` through every nested `poly`, and the type under them.
(define k-binders-of (subr (maxeff kmakes spin) (int) k-bound-body)
  (lambda (t) (k-binders-from (k-resolve t) nil)))

;; Whether `v` is one of the binders being solved.
(define k-unknown? (subr kreads (k-binders int) bool)
  (lambda (kinds v) (k-binder-has? kinds v)))
(define k-open? (subr kreads (k-binders k-solved int) bool)
  (lambda (kinds solved v) (and (k-unknown? kinds v) (null? (k-map-find (get solved) v)))))
(define k-solve (subr kstate (k-solved int k-desc) unit)
  (lambda (solved v d) (set solved (cons (cons v d) (get solved)))))

;; `a ≤ b`: region `a` won't outlive region `b`. The same; `b` a constant
;; (which never ends: `@name`, a fresh region, `const`); `b` bound around
;; `a`'s binder; or `a`'s bound won't outlive `b`.
(define k-outlived? (subr (maxeff kmakes spin) (k-region k-region) bool)
  (lambda (a b)
    (or (k-region=? a b)
        (tagcase b
          (r-var (w)
            (tagcase a
              (r-frozen (p f) (and (>= p 0) (k-outlived? (r-var p) b)))
              (r-var (v)
                (or (k-has-id? (k-outer-of v) w)
                    (let ((c (k-bound-of v)))
                      (and (not (null? c)) (not (k-region=? (car c) a))
                           (k-outlived? (car c) b)))))
              (else x #f)))
          (else y #t)))))

;; Each region binder nothing has solved gets a fresh region of its own,
;; named after it; or, if it has a bound, its bound, as solved (so `(rcons p
;; x y)`, with nothing else saying, allocates at `p`'s own region). A bounded
;; binder waits for its bound to be solved.
;; Whether binder `v`, of kind `k`, is a region binder not yet solved.
(define k-unsolved-region? (subr kreads (int int k-solved) bool)
  (lambda (k v solved) (and (= k 0) (null? (k-map-find (get solved) v)))))
;; A fresh region named after binder `v`.
(define k-fresh-region-for (subr kstate (int) k-region)
  (lambda (v) (k-fresh-region (string-append "@" (symbol->string (k-dvar-name v))))))
(define k-default-bounded (subr kstate (k-binders k-binders k-solved) unit)
  (lambda (all kinds solved)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (bd (k-bound-of v)))
          (begin
            (if (and (k-unsolved-region? (extract (car kinds) 2) v solved) (not (null? bd)))
                (tagcase (car bd)
                  (r-var (w)
                    (let ((f (k-map-find (get solved) w)))
                      (cond ((not (null? f))
                             (tagcase (cdr (car f)) (dr (x) (k-solve solved v (dr x))) (else y #u)))
                            ((k-unknown? all w) #u)
                            (else (k-solve solved v (dr (car bd)))))))
                  (else y (k-solve solved v (dr (car bd)))))
                #u)
            (k-default-bounded all (cdr kinds) solved))))))
(define k-default-free (subr kstate (k-binders k-binders k-solved) unit)
  (lambda (all kinds solved)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (bd (k-bound-of v))
               (waits (and (not (null? bd))
                           (tagcase (car bd) (r-var (w) (k-unknown? all w)) (else y #f)))))
          (begin
            (if (and (k-unsolved-region? (extract (car kinds) 2) v solved) (not waits))
                (k-solve solved v (dr (k-fresh-region-for v)))
                #u)
            (k-default-free all (cdr kinds) solved))))))

(define k-default-regions (subr kstate (k-binders k-solved) unit)
  (lambda (kinds solved)
    (begin (k-default-bounded kinds kinds solved) (k-default-free kinds kinds solved))))

;; `t` with its frozen regions made acyclic: what data `acyclic?` has found
;; acyclic is.
(define k-fin-region (subr (read @globals) (k-region) k-region)
  (lambda (r) (tagcase r (r-frozen (p f) (r-frozen p #t)) (else y r))))
;; Whether `k-finitize` rebuilds a node: a pair, product, sum or bloblet.
(define k-finitizes? (subr pure (k-ty) bool)
  (lambda (n)
    (tagcase n
      (ty-pair (a b r) #t) (ty-product (ps) #t) (ty-sum (ps) #t) (ty-bloblet (fs z r) #t)
      (else y #f))))
(define-rec
  (k-finitize (subr (maxeff kstate spin) (int (ref k-pairs @t)) int)
    (lambda (t memo)
      (let* ((t (k-resolve t)) (done (k-memo-find (get memo) t)))
        (cond ((>= done 0) done)
              ((not (k-finitizes? (k-get t))) t)
              (else
               (let ((slot (k-slot)))
                 (begin
                   (set memo (cons (cons t slot) (get memo)))
                   (let ((new (k-finitize-node t memo)))
                     (begin (k-set-link slot (k-ty-new new)) slot)))))))))
  ;; Node `t`, its parts made acyclic, and its region if frozen.
  (k-finitize-node (subr (maxeff kstate spin) (int (ref k-pairs @t)) k-ty)
    (lambda (t memo)
      (tagcase (k-get t)
        (ty-pair (a b r)
          (let* ((a2 (k-finitize a memo)) (b2 (k-finitize b memo)))
            (ty-pair a2 b2 (k-fin-region r))))
        (ty-product (ps) (ty-product (k-finitize-parts ps memo)))
        (ty-sum (ps) (ty-sum (k-finitize-parts ps memo)))
        (ty-bloblet (fs z r) (ty-bloblet (k-finitize-list fs memo) z (k-fin-region r)))
        (else y (k-get t)))))
  (k-finitize-parts (subr (maxeff kstate spin) (k-parts (ref k-pairs @t)) k-parts)
    (lambda (ps memo)
      (if (null? ps)
          nil
          (let* ((x (k-finitize (extract (car ps) 2) memo))
                 (rest (k-finitize-parts (cdr ps) memo)))
            (cons (product (1 (extract (car ps) 1)) (2 x)) rest)))))
  (k-finitize-list (subr (maxeff kstate spin) (k-ids (ref k-pairs @t)) k-ids)
    (lambda (ts memo)
      (if (null? ts)
          nil
          (let* ((x (k-finitize (car ts) memo)) (rest (k-finitize-list (cdr ts) memo)))
            (cons x rest))))))
(define k-finitized (subr (maxeff kstate spin) (int) int)
  (lambda (t) (k-finitize t (the (ref k-pairs @t) (new nil)))))
;; Which binding of `s` is in scope: how deep its name's stack is.
(define k-binding-depth (subr (maxeff kreads spin) (symbol) int)
  (lambda (s) (k-length (table-ref (get k-env) s nil))))
;; Whether `s`, bound at depth `d`, is among the certified `cs`.
(define k-certified-has? (subr kreads (k-named symbol int) bool)
  (lambda (cs s d) (k-named-has? cs s d)))
;; Whether `xs` is one argument.
(define k-sc-one-arg? (subr (read @t) (kxs) bool)
  (lambda (xs) (and (not (null? xs)) (null? (cdr xs)))))
;; Region binder `v`, as `m` solves it, won't outlive its bound, as solved;
;; or an error.
(define k-check-bound (subr (maxeff checks spin) (int k-region k-map int int) unit)
  (lambda (v bound m a b)
    (let ((r (k-subst-region (r-var v) m)) (c (k-subst-region bound m)))
      (if (k-outlived? r c)
          #u
          (k-fail (k-cat5 (k-quote-dvar v) " must not outlive " (k-quote (k-region-show bound))
                          ", and " (k-cat3 (k-region-show r) " could outlive " (k-region-show c)))
                  a b)))))
(define k-check-bounds (subr (maxeff checks spin) (k-binders k-map int int) unit)
  (lambda (kinds m a b)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (bd (k-bound-of v)))
          (begin
            ;; A `data` binder takes only data, at its place (F13); a region
            ;; binder won't outlive its bound.
            (cond ((= (extract (car kinds) 2) 4) (k-check-data v bd m a b))
                  ((null? bd) #u)
                  (else (k-check-bound v (car bd) m a b)))
            (k-check-bounds (cdr kinds) m a b))))))
;; A size binder instantiated as `finite` is sound only where it stands for
;; one size a caller supplies (`docs/research/soundness-findings.md`, F4): as
;; the size of at most one parameter, that parameter's own `(nlist T v)` or
;; `(nat v)` (less a constant, perhaps), and nowhere else a caller supplies
;; or can write. Its occurrences in what the callee gives back only forget a
;; size. Polarity: 1 given back, -1 supplied by a caller, 0 both, as in
;; anything that can be written.
;; Whether a size's terms are one variable, once.
(define k-one-var? (subr pure (k-terms) bool)
  (lambda (ts) (and (not (null? ts)) (null? (cdr ts)) (= (cdr (car ts)) 1))))
(define* k-size-alone? (subr pure (k-size int) bool)
  (lambda (z v)
    (tagcase z
      (sz-lin (k ts) (and (<= k 0) (k-one-var? ts) (= (car (car ts)) v)))
      (else y #f))))
;; Whether size `z` mentions variable `v`.
(define k-size-mentions? (subr (read @globals) (k-size int) bool)
  (lambda (z v) (tagcase z (sz-lin (k ts) (not (= (k-coef-of ts v) 0))) (else y #f))))
(define k-size-bad (subr (read @globals) (k-size int int) int)
  (lambda (z pol v) (if (and (not (= pol 1)) (k-size-mentions? z v)) 1 0)))
(define-type k-seen-pol (ref k-pairs @t))
;; How many occurrences of size variable `v` in `t` a caller supplies or
;; can write.
(define-rec
  (k-size-walk (subr (maxeff kstate spin) (int int int k-seen-pol) int)
    (lambda (t0 pol v seen)
      (let ((t (k-resolve t0)))
        (if (k-pair-seen? (get seen) t pol)
            0
            (begin
              (set seen (cons (cons t pol) (get seen)))
              (tagcase (k-get t)
                (ty-nat (z) (k-size-bad z pol v))
                (ty-nlist (e z r) (+ (k-size-bad z pol v) (k-size-walk e pol v seen)))
                (ty-named (g ds) (k-size-walk-descs ds v seen))
                (ty-subr (e ps r cv)
                  (+ (k-size-walk-list ps (- 0 pol) v seen) (k-size-walk r pol v seen)))
                (ty-poly (bs body) (k-size-walk body pol v seen))
                (ty-pair (x y r)
                  (let ((p (tagcase r (r-frozen (q f) pol) (else w 0))))
                    (+ (k-size-walk x p v seen) (k-size-walk y p v seen))))
                (ty-bloblet (fs z r) (k-size-walk-list fs (if z pol 0) v seen))
                (ty-product (ps) (k-size-walk-parts ps pol v seen))
                (ty-sum (ps) (k-size-walk-parts ps pol v seen))
                (ty-ref (x r) (k-size-walk x 0 v seen))
                (ty-array (x r) (k-size-walk x 0 v seen))
                (ty-icell (x r) (k-size-walk x 0 v seen))
                (ty-markkey (x r) (k-size-walk x 0 v seen))
                (ty-tag (x y e r) (+ (k-size-walk x 0 v seen) (k-size-walk y 0 v seen)))
                (ty-comp (x y e r) (+ (k-size-walk x 0 v seen) (k-size-walk y 0 v seen)))
                (else y 0)))))))
  (k-size-walk-list (subr (maxeff kstate spin) (k-ids int int k-seen-pol) int)
    (lambda (ts pol v seen)
      (if (null? ts)
          0
          (let ((here (k-size-walk (car ts) pol v seen)))
            (+ here (k-size-walk-list (cdr ts) pol v seen))))))
  (k-size-walk-parts (subr (maxeff kstate spin) (k-parts int int k-seen-pol) int)
    (lambda (ps pol v seen)
      (if (null? ps)
          0
          (let ((here (k-size-walk (extract (car ps) 2) pol v seen)))
            (+ here (k-size-walk-parts (cdr ps) pol v seen))))))
  (k-size-walk-descs (subr (maxeff kstate spin) (k-descs int k-seen-pol) int)
    (lambda (ds v seen)
      (if (null? ds)
          0
          (let ((here (tagcase (car ds)
                        (dz (z) (k-size-bad z 0 v))
                        (dt (x) (k-size-walk x 0 v seen))
                        (else y 0))))
            (+ here (k-size-walk-descs (cdr ds) v seen)))))))
;; A count of such occurrences, and of parameters sized by `v` alone.
(define-type k-counts (productof (1 int) (2 int)))
;; Parameter `p`'s, as a whole.
(define k-size-whole (subr (maxeff kstate spin) (int int k-seen-pol) k-counts)
  (lambda (p v seen) (product (1 (k-size-walk p -1 v seen)) (2 0))))
;; Parameter `p`'s.
(define k-size-param (subr (maxeff kstate spin) (int int k-seen-pol) k-counts)
  (lambda (p v seen)
    (tagcase (k-get p)
      (ty-nat (z) (if (k-size-alone? z v) (product (1 0) (2 1)) (k-size-whole p v seen)))
      (ty-nlist (e z r)
        (if (k-size-alone? z v)
            (product (1 (k-size-walk e -1 v seen)) (2 1))
            (k-size-whole p v seen)))
      (else y (k-size-whole p v seen)))))
;; Each parameter's count of such occurrences, and how many parameters are
;; sized by `v` alone.
(define k-size-params (subr (maxeff kstate spin) (k-ids int k-seen-pol) k-counts)
  (lambda (ps v seen)
    (if (null? ps)
        (product (1 0) (2 0))
        (let* ((here (k-size-param (k-resolve (car ps)) v seen))
               (rest (k-size-params (cdr ps) v seen)))
          (product (1 (+ (extract here 1) (extract rest 1)))
                   (2 (+ (extract here 2) (extract rest 2))))))))
(define k-finite-size-ok? (subr (maxeff kstate spin) (int int) bool)
  (lambda (body v)
    (let ((seen (the k-seen-pol (new nil))))
      (tagcase (k-get (k-resolve body))
        (ty-subr (e ps r cv)
          (let* ((counts (k-size-params ps v seen)) (res (k-size-walk r 1 v seen)))
            (and (= (+ (extract counts 1) res) 0) (<= (extract counts 2) 1))))
        (else y (= (k-size-walk body 1 v seen) 0))))))
;; The sizes of `vs` named since `saved`, its tail, onto `out`: oldest
;; first.
(define k-named-since (subr (maxeff kstate spin) (k-ids k-ids k-ids) k-ids)
  (lambda (saved vs out)
    (if (= (k-length vs) (k-length saved))
        out
        (k-named-since saved (cdr vs) (the k-ids (cons (car vs) out))))))
;; Each size of `vs` is given back by `t` only; or an error at `a`–`b`.
(define k-check-forgettable (subr (maxeff checks spin) (int k-ids int int) unit)
  (lambda (t vs a b)
    (cond ((null? vs) #u)
          ((> (k-size-walk t 1 (car vs) (the k-seen-pol (new nil))) 0)
           (let* ((name (k-quote-dvar (car vs)))
                  (ty (k-show-ty t))
                  (what (k-cat3 "this is a " ty ", which takes something of the size of ")))
             (k-fail (k-cat5 what name ", and that size is not known outside " name "'s scope")
                     a b)))
          (else (k-check-forgettable t (cdr vs) a b)))))
;; `m`, each of `vs` `finite`.
(define k-finite-map (subr (maxeff kstate spin) (k-ids k-map) k-map)
  (lambda (vs m)
    (if (null? vs) m (k-finite-map (cdr vs) (cons (cons (car vs) (dz (sz-finite))) m)))))
;; `t` with the sizes named since `saved` forgotten, as `finite`: they mean
;; nothing outside the scope that named them. Pops them. Each stands for one
;; value's size, which no caller chooses, so it may be forgotten only where
;; `t` gives it back: where a caller would supply something of that size,
;; forgetting it would let any size in (`docs/research/soundness-findings.md`,
;; F8), and that is an error at `a`–`b`.
(define k-forget-nats (subr (maxeff checks spin) (k-ids int int int) int)
  (lambda (saved t a b)
    (let ((vs (k-named-since saved (get k-skolems) nil)))
      (begin (set k-skolems saved)
             (k-check-forgettable t vs a b)
             (if (null? vs) t (k-subst t (k-finite-map vs nil)))))))
;; Size binder `v` would be `z`, not known to be no less than 0: an error.
(define k-size-below-zero (subr (maxeff checks spin) (int k-size int int) void)
  (lambda (v z a b)
    (k-fail (k-cat5 "the size " (k-quote-dvar v) " would be " (k-show-size z)
                    (string-append ", which is not known here to be no less than 0: "
                                   "an argument may be shorter than this procedure's type needs"))
            a b)))
;; Size binder `v` cannot be `finite`: an error.
(define k-size-not-finite (subr (maxeff checks spin) (int int int) void)
  (lambda (v a b)
    (let ((name (k-quote-dvar v)))
      (k-fail (k-cat5 "the size " name " cannot be `finite` here: " name
                      (k-cat3 " is the size of more than one argument,"
                              " or of something inside one,"
                              " and `finite` would not keep them the same"))
              a b))))
;; Whether a size is `finite`.
(define k-finite-size? (subr pure (k-size) bool)
  (lambda (z) (tagcase z (sz-finite () #t) (else w #f))))
(define k-check-finite-sizes (subr (maxeff checks spin) (k-binders k-map int int int) unit)
  (lambda (kinds m body a b)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (f (k-map-find m v))
               ;; Whether `v` is a size binder solved, and as what.
               (sized (and (= (extract (car kinds) 2) 5) (not (null? f))
                           (tagcase (cdr (car f)) (dz (z) #t) (else y #f))))
               (z (if sized (tagcase (cdr (car f)) (dz (z) z) (else y (sz-finite))) (sz-finite)))
               (fin (and sized (k-finite-size? z))))
          (cond
            ;; A size binder solved from `v + k` against a size is that
            ;; size less `k`: a natural only where the facts here show it.
            ((and sized (not (k-finite-size? z)) (not (k-size-nonneg? z)))
             (k-size-below-zero v z a b))
            ((and fin (not (k-finite-size-ok? body v))) (k-size-not-finite v a b))
            (else (k-check-finite-sizes (cdr kinds) m body a b)))))))
;; What a binder of kind `k`, 1, 6 or 5, nothing says is: an effect, pure;
;; a convention, the program's; a size, some size.
(define k-default-desc (subr kreads (int) k-desc)
  (lambda (k)
    (cond ((= k 1) (de nil))
          ((= k 6) (dc (get k-conv-default)))
          (else (dz (sz-finite))))))
(define k-finish-each (subr (maxeff checks spin) (k-binders k-map int int int) k-map)
  (lambda (kinds m a b ft)
    (if (null? kinds)
        m
        (let ((v (extract (car kinds) 1)) (k (extract (car kinds) 2)))
          (cond ((not (null? (k-map-find m v))) (k-finish-each (cdr kinds) m a b ft))
                ((or (= k 1) (= k 6) (= k 5))
                 (k-finish-each (cdr kinds) (cons (cons v (k-default-desc k)) m) a b ft))
                (else (k-fail (k-cat5 (k-quote-dvar v) " cannot be inferred for " (k-show-ty ft)
                                      ": nothing here says what it is. Use `proj`, or `the`" "")
                              a b)))))))

;; The whole solution: every type binder solved, effects defaulting to pure.
(define k-finish (subr (maxeff checks spin) (k-binders k-solved int int int) k-map)
  (lambda (kinds solved a b ft)
    (k-finish-each kinds (k-data-places-solved kinds kinds (get solved)) a b ft)))

;; Solve a size binder: a pattern `v + k` against a size `s` gives
;; `v = s - k` (`finite` stays `finite`).
(define k-unify-size (subr (maxeff kstate spin) (k-size k-size k-binders k-solved) unit)
  (lambda (p a kinds solved)
    (tagcase p
      (sz-lin (k ts)
        (if (k-one-var? ts)
            (let ((v (car (car ts))))
              (if (k-open? kinds solved v) (k-solve solved v (dz (k-size-plus a (- 0 k)))) #u))
            #u))
      (else y #u))))
(define k-wrong-shape? (subr (maxeff kmakes spin) (int int) bool)
  (lambda (pattern actual)
    (let ((p (k-ty-rank pattern)) (a (k-ty-rank actual)))
      (cond ((or (= p 2) (= a 1)) #f)
            ((= p 3) (null? (k-as-subr actual)))
            ((and (= p 6) (= a 18)) #f)
            ;; A `nat` is an `int`.
            ((and (= p 0) (= a 19)) #f)
            (else (not (= p a)))))))

;; Each type binder of `kinds` not yet solved, onto `acc`, mapped to `?`.
(define* k-holes (subr (maxeff kstate spin) (k-binders k-solved k-map) k-map)
  (lambda (kinds solved acc)
    (if (null? kinds)
        acc
        (let* ((v (extract (car kinds) 1))
               (open (and (= (extract (car kinds) 2) 2) (null? (k-map-find (get solved) v))))
               (hole (the (pairof int k-desc @t) (cons v (dt (k-ty-new (ty-base '?)))))))
          (k-holes (cdr kinds) solved (if open (the k-map (cons hole acc)) acc))))))
;; `t` as a message shows it, each type binder not yet solved shown as `?`:
;; what it is is not known, and its name is the callee's own.
(define k-show-open (subr (maxeff kstate spin) (int k-binders k-solved) string)
  (lambda (t kinds solved) (k-show-ty (k-subst t (k-holes kinds solved (the k-map nil))))))
;; Whether no instantiation of a callee's `result` could fit `want`, what the
;; context expects, by their outermost shapes. An unknown fits anything; a
;; pair may be told to be a `nlist`.
(define k-result-misfits? (subr (maxeff kmakes spin) (int int) bool)
  (lambda (want result)
    (let ((w (k-ty-rank want)) (r (k-ty-rank result)))
      (cond ((= r 2) #f) ((and (= w 18) (= r 6)) #f) (else (k-wrong-shape? want result))))))
;; An argument of the wrong shape altogether is the error to report, before
;; any binder it left unsolved.
(define k-inst-shapes
  (subr (maxeff checks spin) (kxs k-ids int k-binders k-solved (arrayof int @t)) unit)
  (lambda (args params i kinds solved done-t)
    (if (null? args)
        #u
        (let ((t (array-ref done-t i)))
          (if (and (>= t 0) (k-wrong-shape? (car params) t))
              (let ((p (k-show-open (k-subst (car params) (get solved)) kinds solved)))
                (k-fail (k-cat5 "argument " (int->string (+ i 1)) " is a " (k-show-ty t)
                                (k-cat3 ", where a " p " is expected"))
                        (k-start (car args)) (k-end (car args))))
              (k-inst-shapes (cdr args) (cdr params) (+ i 1) kinds solved done-t))))))
;; The error that the callee's `result` cannot fit `expected`, what the
;; context expects, by their outermost shapes; none if it may.
(define k-result-shape (subr (maxeff checks spin) (int int k-binders k-solved int int) unit)
  (lambda (expected result kinds solved a b)
    (if (and (>= expected 0) (k-result-misfits? expected result))
        (let ((got (k-show-open (k-subst result (get solved)) kinds solved)))
          (k-fail (k-cat5 "this is a " got ", where a " (k-show-ty expected) " is expected") a b))
        #u)))

;; Whether `t` mentions a binder of any kind not yet solved.
(define k-open-region? (subr kreads (k-region k-binders k-solved) bool)
  (lambda (r kinds solved)
    (tagcase r
      (r-var (v) (k-open? kinds solved v))
      (r-frozen (p f) (and (>= p 0) (k-open? kinds solved p)))
      (else y #f))))
(define k-open-conv? (subr kreads (k-conv k-binders k-solved) bool)
  (lambda (c kinds solved) (tagcase c (cv-var (v) (k-open? kinds solved v)) (else y #f))))
;; Whether an atom mentions a binder not yet solved.
(define k-open-atom? (subr kreads (k-atom k-binders k-solved) bool)
  (lambda (a kinds solved)
    (tagcase a
      (a-var (v) (k-open? kinds solved v))
      (else y (k-open-region? (k-atom-region a) kinds solved)))))
(define k-open-effect? (subr kreads (k-eff k-binders k-solved) bool)
  (lambda (e kinds solved)
    (cond ((null? e) #f)
          ((k-open-atom? (car e) kinds solved) #t)
          (else (k-open-effect? (cdr e) kinds solved)))))
(define k-push-ids (subr kmakes (k-ids k-ids) k-ids)
  (lambda (xs onto) (if (null? xs) onto (cons (car xs) (k-push-ids (cdr xs) onto)))))
(define k-push-parts (subr kmakes (k-parts k-ids) k-ids)
  (lambda (ps onto) (if (null? ps) onto (cons (extract (car ps) 2) (k-push-parts (cdr ps) onto)))))
(define k-descs-open? (subr kreads (k-descs k-binders k-solved) bool)
  (lambda (ds kinds solved)
    (and (not (null? ds))
         (or (tagcase (car ds)
               (dr (r) (k-open-region? r kinds solved))
               (de (e) (k-open-effect? e kinds solved))
               (dc (c) (k-open-conv? c kinds solved))
               (else y #f))
             (k-descs-open? (cdr ds) kinds solved)))))
;; Whether a size's terms mention a variable still to be solved.
(define k-terms-open? (subr (maxeff kstate spin) (k-terms k-binders k-solved) bool)
  (lambda (xs kinds solved)
    (and (not (null? xs))
         (or (k-open? kinds solved (car (car xs))) (k-terms-open? (cdr xs) kinds solved)))))
;; Whether a size mentions a variable still to be solved.
(define k-size-open? (subr (maxeff kstate spin) (k-size k-binders k-solved) bool)
  (lambda (z kinds solved)
    (tagcase z (sz-lin (k ts) (k-terms-open? ts kinds solved)) (else w #f))))
(define k-any-walk (subr (maxeff kstate spin) (k-ids int k-binders k-solved) bool)
  (lambda (stack seen kinds solved)
    (if (null? stack)
        #f
        (let ((t (k-resolve (car stack))) (rest (cdr stack)))
          (if (k-visit? t seen)
              (k-any-walk rest seen kinds solved)
              (letrec ((reg (subr kreads (k-region) bool)
                            (lambda (r) (k-open-region? r kinds solved)))
                       (go (subr (maxeff kstate spin) (k-ids) bool)
                           (lambda (s) (k-any-walk s seen kinds solved))))
                (tagcase (k-get t)
                  (ty-var (v) (or (k-open? kinds solved v) (go rest)))
                  (ty-subr (e ps r cv)
                    (or (k-open-effect? e kinds solved) (k-open-conv? cv kinds solved)
                        (go (k-push-ids ps (cons r rest)))))
                  (ty-poly (bs body) (go (cons body rest)))
                  (ty-ref (x r) (or (reg r) (go (cons x rest))))
                  (ty-markkey (x r) (or (reg r) (go (cons x rest))))
                  (ty-array (x r) (or (reg r) (go (cons x rest))))
                  (ty-icell (x r) (or (reg r) (go (cons x rest))))
                  (ty-place (r) (or (reg r) (go rest)))
                  (ty-pair (x y r) (or (reg r) (go (cons x (cons y rest)))))
                  (ty-bloblet (fs z r) (or (reg r) (go (k-push-ids fs rest))))
                  (ty-product (ps) (go (k-push-parts ps rest)))
                  (ty-sum (ps) (go (k-push-parts ps rest)))
                  (ty-tag (x y e r)
                    (or (reg r) (k-open-effect? e kinds solved) (go (cons x (cons y rest)))))
                  (ty-comp (x y e r)
                    (or (reg r) (k-open-effect? e kinds solved) (go (cons x (cons y rest)))))
                  (ty-named (g ds)
                    (or (k-descs-open? ds kinds solved) (go (k-push-ids (k-desc-types ds) rest))))
                  (ty-nlist (e z r) (or (reg r) (k-size-open? z kinds solved) (go (cons e rest))))
                  (ty-nat (z) (or (k-size-open? z kinds solved) (go rest)))
                  (else y (go rest)))))))))
(define k-mentions-any-unknown? (subr (maxeff kstate spin) (int k-binders k-solved) bool)
  (lambda (t kinds solved) (k-any-walk (cons t nil) (k-new-epoch) kinds solved)))

(define-rec
  (k-vars-walk (subr (maxeff kstate spin) (int int k-binders k-solved) bool)
    (lambda (t seen kinds solved)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #f
            (letrec ((w (subr (maxeff kstate spin) (int) bool)
                        (lambda (x) (k-vars-walk x seen kinds solved)))
                     (ws (subr (maxeff kstate spin) (k-ids) bool)
                         (lambda (xs) (k-vars-walks xs seen kinds solved))))
              (begin
                (tagcase (k-get t)
                  (ty-var (v) (k-open? kinds solved v))
                  (ty-subr (e ps r cv) (or (ws ps) (w r)))
                  (ty-poly (bs body) (w body))
                  (ty-ref (a r) (w a))
                  (ty-markkey (a r) (w a))
                  (ty-array (a r) (w a))
                  (ty-icell (a r) (w a))
                  (ty-bloblet (fs z r) (ws fs))
                  (ty-product (ps) (ws (k-push-parts ps nil)))
                  (ty-sum (ps) (ws (k-push-parts ps nil)))
                  (ty-pair (a b r) (or (w a) (w b)))
                  (ty-tag (a b e r) (or (w a) (w b)))
                  (ty-comp (a b e r) (or (w a) (w b)))
                  (ty-named (g ds) (ws (k-desc-types ds)))
                  (ty-nlist (e z r) (w e))
                  (else y #f))))))))
  (k-vars-walks (subr (maxeff kstate spin) (k-ids int k-binders k-solved) bool)
    (lambda (ts seen kinds solved)
      (cond ((null? ts) #f)
            ((k-vars-walk (car ts) seen kinds solved) #t)
            (else (k-vars-walks (cdr ts) seen kinds solved))))))

;; Whether `t` mentions a type binder not yet solved.
(define k-mentions-unknown-type? (subr (maxeff kstate spin) (int k-binders k-solved) bool)
  (lambda (t kinds solved) (k-vars-walk t (k-new-epoch) kinds solved)))
(define k-any-unknown-type? (subr (maxeff kstate spin) (k-ids k-binders k-solved) bool)
  (lambda (ts kinds solved)
    (cond ((null? ts) #f)
          ((k-mentions-unknown-type? (car ts) kinds solved) #t)
          (else (k-any-unknown-type? (cdr ts) kinds solved)))))
;; A convention binder takes the actual's convention, if nothing has yet.
(define k-unify-conv (subr kstate (k-conv k-conv k-binders k-solved) unit)
  (lambda (pc ac kinds solved)
    (tagcase pc
      (cv-var (v) (if (k-open? kinds solved v) (k-solve solved v (dc ac)) #u))
      (else y #u))))
;; A region binder takes the actual region; a place frozen into, `(acyclic
;; p)` or `(const p)`, takes the actual's place (the heap, where that is
;; frozen into the heap).
(define k-unify-region (subr kstate (k-region k-region k-binders k-solved) unit)
  (lambda (p a kinds solved)
    (tagcase p
      (r-var (v) (if (k-open? kinds solved v) (k-solve solved v (dr a)) #u))
      (r-frozen (v f)
        (if (and (>= v 0) (k-open? kinds solved v))
            (tagcase a
              (r-frozen (q g) (k-solve solved v (dr (if (< q 0) (r-heap) (r-var q)))))
              (else y #u))
            #u))
      (else y #u))))
(define k-same-kind-regions (subr kmakes (k-eff int) k-regions)
  (lambda (e rank)
    (cond ((null? e) nil)
          ((= (k-atom-rank (car e)) rank)
           (cons (k-atom-region (car e)) (k-same-kind-regions (cdr e) rank)))
          (else (k-same-kind-regions (cdr e) rank)))))
;; An effect binder takes all of `actual`; a region named in an atom is
;; matched against the actual's atoms of that kind when there is only one.
(define k-unify-effect (subr (maxeff kstate spin) (k-eff k-eff k-binders k-solved) unit)
  (lambda (pattern actual kinds solved)
    (if (null? pattern)
        #u
        (let ((atom (car pattern)))
          (begin
            (tagcase atom
              (a-var (v)
                (if (k-unknown? kinds v)
                    (let* ((f (k-map-find (get solved) v))
                           (prev (if (null? f)
                                     (the k-eff nil)
                                     (tagcase (cdr (car f)) (de (e) e) (else y (the k-eff nil))))))
                      (k-solve solved v (de (k-union prev actual))))
                    #u))
              (else y
                (tagcase (k-atom-region atom)
                  (r-var (v)
                    (if (k-open? kinds solved v)
                        (let ((same (k-same-kind-regions actual (k-atom-rank atom))))
                          (if (and (not (null? same)) (null? (cdr same)))
                              (k-solve solved v (dr (car same)))
                              #u))
                        #u))
                  (else z #u))))
            (k-unify-effect (cdr pattern) actual kinds solved))))))

;;; Matching: solve binders in `pattern` so that `actual` fits it. Never
;;; fails; what cannot be matched is left for the subtype check after.

;; A type binder takes the actual type `a`; one already solved takes it
;; only if it is strictly above what it was.
(define k-unify-var (subr (maxeff kstate spin) (int int k-binders k-solved) unit)
  (lambda (v a kinds solved)
    (if (k-unknown? kinds v)
        (let ((f (k-map-find (get solved) v)))
          (if (null? f)
              (k-solve solved v (dt a))
              (tagcase (cdr (car f))
                (dt (was)
                  (if (and (not (k-subtype a was)) (k-subtype was a)) (k-solve solved v (dt a)) #u))
                (else y #u))))
        #u)))
(define-rec
  (k-unify (subr (maxeff kstate spin) (int int k-binders k-solved k-trail) unit)
    (lambda (pattern actual kinds solved trail)
      (let ((p (k-resolve pattern)) (a (k-resolve actual)))
        (if (k-pair-seen? (get trail) p a)
            #u
            (begin
              (set trail (cons (cons p a) (get trail)))
              (let ((pt (k-get p)) (at (k-get a)))
                (if (and (tagcase at (ty-void () #t) (else y #f))
                         (not (tagcase pt (ty-var (v) (k-open? kinds solved v)) (else y #f))))
                    #u
                    (k-unify-node a pt at kinds solved trail))))))))
  ;; Node `pt` matched against `a`, whose node is `at`, by their shapes.
  (k-unify-node (subr (maxeff kstate spin) (int k-ty k-ty k-binders k-solved k-trail) unit)
    (lambda (a pt at kinds solved trail)
      (letrec ((u (subr (maxeff kstate spin) (int int) unit)
                  (lambda (x y) (k-unify x y kinds solved trail)))
               (ur (subr kstate (k-region k-region) unit)
                   (lambda (r s) (k-unify-region r s kinds solved)))
               (ue (subr (maxeff kstate spin) (k-eff k-eff) unit)
                   (lambda (e f) (k-unify-effect e f kinds solved))))
        (tagcase pt
          (ty-var (v) (k-unify-var v a kinds solved))
          (ty-subr (pe pp pr pc)
            (let ((c (k-as-subr a)))
              (if (null? c)
                  #u
                  (begin
                   ;; A convention binder takes the actual's convention.
                   (tagcase at (ty-subr (e ps r ac) (k-unify-conv pc ac kinds solved)) (else y #u))
                   (let ((ap (extract (car c) 2)))
                     (if (not (= (k-length pp) (k-length ap)))
                         #u
                         (begin (k-unify-lists pp ap kinds solved trail)
                                (u pr (extract (car c) 3))
                                (ue pe (extract (car c) 1)))))))))
          (ty-ref (x r) (tagcase at (ty-ref (y s) (begin (ur r s) (u x y))) (else z #u)))
          (ty-markkey (x r) (tagcase at (ty-markkey (y s) (begin (ur r s) (u x y))) (else z #u)))
          (ty-array (x r) (tagcase at (ty-array (y s) (begin (ur r s) (u x y))) (else z #u)))
          (ty-icell (x r) (tagcase at (ty-icell (y s) (begin (ur r s) (u x y))) (else z #u)))
          (ty-place (r) (tagcase at (ty-place (s) (ur r s)) (else z #u)))
          (ty-pair (x1 x2 r)
            (tagcase at
              (ty-pair (y1 y2 s) (begin (ur r s) (u x1 y1) (u x2 y2)))
              ;; A `nlist`'s tail is the `nlist` one shorter.
              (ty-nlist (y sz s)
                (begin (ur r s) (u x1 y)
                       (u x2 (tagcase sz (sz-finite () a) (else w (k-nlist-tail y sz s))))))
              (else z #u)))
          (ty-nlist (x sz r)
            (tagcase at
              (ty-nlist (y sz2 s) (begin (ur r s) (u x y) (k-unify-size sz sz2 kinds solved)))
              (else z #u)))
          (ty-nat (sz) (tagcase at (ty-nat (sz2) (k-unify-size sz sz2 kinds solved)) (else z #u)))
          (ty-product (pp)
            (tagcase at (ty-product (pa) (k-unify-parts pp pa kinds solved trail)) (else z #u)))
          (ty-sum (pp)
            (tagcase at (ty-sum (pa) (k-unify-parts pp pa kinds solved trail)) (else z #u)))
          (ty-bloblet (fp zp r)
            (tagcase at
              (ty-bloblet (fa za s)
                (if (= (k-length fp) (k-length fa))
                    (begin (ur r s) (k-unify-lists fp fa kinds solved trail))
                    #u))
              (else z #u)))
          (ty-tag (a1 h1 d1 r1)
            (tagcase at
              (ty-tag (a2 h2 d2 r2) (begin (ur r1 r2) (u a1 a2) (u h1 h2) (ue d1 d2)))
              (else z #u)))
          (ty-comp (h1 a1 d1 r1)
            (tagcase at
              (ty-comp (h2 a2 d2 r2) (begin (ur r1 r2) (u a1 a2) (u h1 h2) (ue d1 d2)))
              (else z #u)))
          (ty-named (g xs)
            (tagcase at
              (ty-named (h ys) (if (= g h) (k-unify-descs xs ys kinds solved trail) #u))
              (else z #u)))
          (else z #u)))))
  (k-unify-descs (subr (maxeff kstate spin) (k-descs k-descs k-binders k-solved k-trail) unit)
    (lambda (xs ys kinds solved trail)
      (if (null? xs)
          #u
          (begin
            (tagcase (car xs)
              (dt (x) (tagcase (car ys) (dt (y) (k-unify x y kinds solved trail)) (else z #u)))
              (dr (r) (tagcase (car ys) (dr (q) (k-unify-region r q kinds solved)) (else z #u)))
              (de (d) (tagcase (car ys) (de (e) (k-unify-effect d e kinds solved)) (else z #u)))
              (dz (m) #u)
              (dc (c) (tagcase (car ys) (dc (d) (k-unify-conv c d kinds solved)) (else z #u))))
            (k-unify-descs (cdr xs) (cdr ys) kinds solved trail)))))
  (k-unify-lists (subr (maxeff kstate spin) (k-ids k-ids k-binders k-solved k-trail) unit)
    (lambda (xs ys kinds solved trail)
      (if (null? xs)
          #u
          (begin (k-unify (car xs) (car ys) kinds solved trail)
                 (k-unify-lists (cdr xs) (cdr ys) kinds solved trail)))))
  (k-unify-parts (subr (maxeff kstate spin) (k-parts k-parts k-binders k-solved k-trail) unit)
    (lambda (pp pa kinds solved trail)
      (if (null? pp)
          #u
          (let ((y (k-part-find pa (extract (car pp) 1))))
            (begin (if (>= y 0) (k-unify (extract (car pp) 2) y kinds solved trail) #u)
                   (k-unify-parts (cdr pp) pa kinds solved trail)))))))

;; Instantiate a polymorphic value used, unapplied, where `expected` is
;; wanted.
(define k-instantiate-against (subr (maxeff checks spin) (int int int int) int)
  (lambda (t expected a b)
    (let* ((bo (k-binders-of t)) (kinds (extract bo 1)) (inner (extract bo 2))
           (solved (the k-solved (new nil))))
      (begin
        (k-unify inner expected kinds solved (the k-trail (new nil)))
        (k-default-regions kinds solved)
        (let ((m (k-finish kinds solved a b t)))
          (begin (k-check-bounds kinds m a b)
                 (k-check-finite-sizes kinds m inner a b)
                 (let ((inst (k-subst inner m))) (begin (k-no-knot inst a b) inst))))))))
(define k-plambda-matches? (subr kreads (kx k-ty) bool)
  (lambda (x et)
    (tagcase x
      (x-plambda (binders body a b)
        (tagcase et
          (ty-poly (bs want) (and (= (k-length bs) (k-length binders)) (k-same-kinds? bs binders)))
          (else y #f)))
      (else y #f))))
(define k-same-labels? (subr kreads (k-let-bs k-parts) bool)
  (lambda (fs ps)
    (cond ((null? fs) (null? ps))
          ((null? ps) #f)
          (else (and (symbol=? (extract (car fs) 1) (extract (car ps) 1))
                     (k-same-labels? (cdr fs) (cdr ps)))))))

;;; ------------------------------------------------------------ tagcase

(define k-all-fit? (subr (maxeff kstate spin) (k-ids int) bool)
  (lambda (types t)
    (cond ((null? types) #t)
          ((k-subtype (car types) t) (k-all-fit? (cdr types) t))
          (else #f))))
;; The first of `candidates` every one of `types` fits, or -1.
(define k-upper-bound (subr (maxeff kstate spin) (k-ids k-ids) int)
  (lambda (candidates types)
    (cond ((null? candidates) -1)
          ((k-all-fit? types (car candidates)) (car candidates))
          (else (k-upper-bound (cdr candidates) types)))))
(define k-part-names (subr kmakes (k-parts) (listof string acyclic))
  (lambda (ps)
    (if (null? ps) nil (cons (symbol->string (extract (car ps) 1)) (k-part-names (cdr ps))))))
(define k-arm-named? (subr kreads (k-arms symbol) bool)
  (lambda (arms l)
    (cond ((null? arms) #f)
          ((symbol=? (extract (car arms) 1) l) #t)
          (else (k-arm-named? (cdr arms) l)))))
(define k-variants-not-named (subr kmakes (k-parts k-arms) k-parts)
  (lambda (vs arms)
    (cond ((null? vs) nil)
          ((k-arm-named? arms (extract (car vs) 1)) (k-variants-not-named (cdr vs) arms))
          (else (cons (car vs) (k-variants-not-named (cdr vs) arms))))))
(define k-cannot-take-apart (subr (maxeff checks spin) (symbol int k-names kx) k-bindings)
  (lambda (tag t names body)
    (k-fail (k-cat5 (k-quote (symbol->string tag)) " carries a " (k-show-ty t)
                    ", which cannot be taken apart into "
                    (string-append (int->string (k-length names)) " name(s)"))
            (k-start body) (k-end body))))
(define k-zip-fields (subr kmakes (k-names k-parts) k-bindings)
  (lambda (ns fs)
    (if (null? ns)
        nil
        (cons (cons (car ns) (extract (car fs) 2)) (k-zip-fields (cdr ns) (cdr fs))))))
;; The atoms of `e` in neither `bound` nor `own`.
(define k-beyond (subr (maxeff kmakes spin) (k-eff k-eff k-eff) k-eff)
  (lambda (e bound own)
    (cond ((null? e) nil)
          ((or (k-covered? bound (car e)) (k-contains? own (car e))) (k-beyond (cdr e) bound own))
          (else (cons (car e) (k-beyond (cdr e) bound own))))))
(define k-none-reach? (subr (maxeff kstate spin) (k-names k-names k-region) bool)
  (lambda (vs tv r)
    (cond ((null? vs) #t)
          ((k-has-name? tv (car vs)) (k-none-reach? (cdr vs) tv r))
          (else (let ((t (k-lookup (car vs))))
                  (and (or (< t 0) (not (k-has-region-in? (k-regions-in t) r)))
                       (k-none-reach? (cdr vs) tv r)))))))
;; Whether the only way `body` can name anything in region `r` is the
;; variable `tag`, if it is one.
(define k-reaches-only? (subr (maxeff kstate spin) (kx kx k-region) bool)
  (lambda (body tag r)
    (let ((tv (the k-names (tagcase tag (x-var (s a b) (cons s nil)) (else y nil)))))
      (k-none-reach? (k-free-vars body) tv r))))

;;; ------------------------------------------------------------ synthesis

;; `(letrena r …)`'s or `(letreap r …)`'s body, of type `t` and effect `e`,
;; closed: its value
;; may not mention `r`, and no continuation captured in it may outlive it;
;; what it does to `r` is masked, as nothing outside can name `r`.
(define k-close-region (subr (maxeff checks spin) (kx string int int k-eff int int) k-te)
  (lambda (x form r t e a b)
    (let ((name (k-cat3 form " " (symbol->string (k-dvar-name r)))))
      (if (k-has-region-in? (k-regions-in t) (r-var r))
          (k-fail (k-cat4 "the value of `" name "` would outlive its region: its type is "
                          (k-show-ty t))
                  a b)
          (let ((masked (k-mask x e t)))
            (if (k-has-comefrom? masked)
                (k-fail (k-cat4 "a continuation captured in `" name
                                "` could outlive its region: its effect is "
                                (k-show-effect masked))
                        a b)
                (k-te t masked)))))))

;; Whether an effect writes region `r`.
(define k-eff-writes? (subr (maxeff kreads spin) (k-eff k-region) bool)
  (lambda (e r)
    (and (not (null? e))
         (or (tagcase (car e) (a-write (x) (k-region=? x r)) (else y #f))
             (k-eff-writes? (cdr e) r)))))
;; A generative type's representation writing one of its parameters writes
;; whatever it was given: cautiously, any region given any. Whether some
;; effect in a walk wrote a parameter, and whether some generative type was
;; given the region.
(define k-wrote-param (ref bool @t) (new #f))
(define k-given (ref bool @t) (new #f))
(define k-eff-writes-param? (subr kreads (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e)
               (a-write (x) (k-gen-region? x))
               (a-var (v) (k-gen-param? v))
               (else y #f))
             (k-eff-writes-param? (cdr e))))))
(define k-eff-writes-noting? (subr (maxeff kstate spin) (k-eff k-region) bool)
  (lambda (e r)
    (begin
      (if (k-eff-writes-param? e) (set k-wrote-param #t) #u)
      (k-eff-writes? e r))))
(define k-note-given (subr (maxeff kstate spin) (k-descs k-region) unit)
  (lambda (ds r)
    (if (null? ds)
        #u
        (begin
          (tagcase (car ds)
            (dr (x) (if (k-region=? x r) (set k-given #t) #u))
            (de (e) (if (k-eff-writes? e r) (set k-given #t) #u))
            (else y #u))
          (k-note-given (cdr ds) r)))))
;; Whether a latent effect anywhere in `t` writes `r`: what a `letfreeze`'s
;; value may not do to its region.
(define-rec
  (k-writes-in (subr (maxeff kstate spin) (int k-region int) bool)
    (lambda (t r seen)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #f
            (tagcase (k-get t)
              (ty-subr (e ps x cv)
                (or (k-eff-writes-noting? e r) (k-writes-list ps r seen) (k-writes-in x r seen)))
              (ty-tag (a h e x)
                (or (k-eff-writes-noting? e r) (k-writes-in a r seen) (k-writes-in h r seen)))
              (ty-comp (b a e x)
                (or (k-eff-writes-noting? e r) (k-writes-in a r seen) (k-writes-in b r seen)))
              (ty-poly (bs body) (k-writes-in body r seen))
              (ty-ref (a x) (k-writes-in a r seen))
              (ty-array (a x) (k-writes-in a r seen))
              (ty-icell (a x) (k-writes-in a r seen))
              (ty-markkey (a x) (k-writes-in a r seen))
              (ty-pair (a b x) (or (k-writes-in a r seen) (k-writes-in b r seen)))
              (ty-bloblet (fs z x) (k-writes-list fs r seen))
              (ty-product (ps) (k-writes-parts ps r seen))
              (ty-sum (ps) (k-writes-parts ps r seen))
              (ty-nlist (e z x) (k-writes-in e r seen))
              (ty-named (g ds)
                (begin (k-note-given ds r)
                       (or (k-writes-in (extract (k-gen-of g) 4) r seen)
                           (k-writes-list (k-desc-types ds) r seen))))
              (else x #f))))))
  (k-writes-list (subr (maxeff kstate spin) (k-ids k-region int) bool)
    (lambda (ts r seen)
      (and (not (null? ts)) (or (k-writes-in (car ts) r seen) (k-writes-list (cdr ts) r seen)))))
  (k-writes-parts (subr (maxeff kstate spin) (k-parts k-region int) bool)
    (lambda (ps r seen)
      (and (not (null? ps))
           (or (k-writes-in (extract (car ps) 2) r seen) (k-writes-parts (cdr ps) r seen))))))

(define k-any-frozen? (subr kreads (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (k-frozen-atom? (car e)) (k-any-frozen? (cdr e))))))
(define k-writes-frozen? (subr kreads (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (and (k-frozen-atom? (car e)) (= (k-atom-rank (car e)) 1))
             (k-writes-frozen? (cdr e))))))
;; Whether an atom reads, allocates or awaits data frozen in the heap,
;; which never ends: that is pure.
(define k-pure-on-const? (subr (read @globals) (k-atom) bool)
  (lambda (a)
    (and (k-frozen-atom? a)
         (let ((k (k-atom-rank a))) (or (= k 0) (or (= k 2) (= k 5))))
         (tagcase (k-atom-region a) (r-frozen (p f) (< p 0)) (else y #f)))))
;; `e` without its reads, allocations and awaits on `const`, which are pure.
(define k-drop-frozen (subr kmakes (k-eff) k-eff)
  (lambda (e)
    (cond ((null? e) nil)
          ;; Only data frozen in the heap, which never ends; what is done to
          ;; data frozen into a place stays, until masking removes it.
          ((k-pure-on-const? (car e)) (k-drop-frozen (cdr e)))
          (else (cons (car e) (k-drop-frozen (cdr e)))))))
;; `x`'s effect `e`, noted.
(define k-note-effect (subr kstate (kx k-eff) unit)
  (lambda (x e)
    (let ((fact (product (1 (k-start x)) (2 (k-end x)) (3 (k-summary e)))))
      (set k-effect-notes (the k-facts (cons fact (get k-effect-notes)))))))
;; `e`, the effect of `x`, with what it does to frozen data taken out; or an
;; error, if it writes it.
(define k-frozen (subr checks (kx k-eff) k-eff)
  (lambda (x e)
    (cond ((not (k-any-frozen? e)) e)
          ((k-writes-frozen? e)
           (k-fail "this writes frozen data, whose region is `const`" (k-start x) (k-end x)))
          (else (k-drop-frozen e)))))

;; A `letfreeze r`'s value, of type `t`, as it leaves: `r` made `const`,
;; unless something in it could still write `r`.
(define k-frozen-result (subr (maxeff checks spin) (int k-region bool int int int) int)
  (lambda (r into written t a b)
    (if (begin (set k-wrote-param #f) (set k-given #f)
               (or (k-writes-in t (r-var r) (k-new-epoch)) (and (get k-wrote-param) (get k-given))))
        (k-fail (k-cat4 "the value of `letfreeze " (symbol->string (k-dvar-name r))
                        "` could still write its region's data: its type is " (k-show-ty t))
                a b)
        (let ((frozen (tagcase into (r-frozen (p f) (r-frozen p (not written))) (else y into))))
          (k-subst t (the k-map (cons (cons r (dr frozen)) nil)))))))
