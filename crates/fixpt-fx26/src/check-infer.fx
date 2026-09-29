;;; The checker, in FX-26: instantiation, `tagcase`, and what synthesis needs.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ instantiation
;;; A projection left out: the binders of a `poly` solved by matching (local
;;; type inference). A type binder must be solved; an effect binder nothing
;;; constrains is `pure`; a region binder nothing constrains is a fresh
;;; region.

(define-type k-solved (ref k-map @t))
(define k-append-binders (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-binders k-binders) k-binders)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (k-append-binders (cdr xs) ys)))))
(define k-binders-from (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-binders) (productof (1 k-binders) (2 int)))
  (lambda (t acc)
    (tagcase (k-get t)
      (ty-poly (bs body) (k-binders-from (k-resolve body) (k-append-binders acc bs)))
      (else y (product (1 acc) (2 t))))))

;; The binders of `t` through every nested `poly`, and the type under them.
(define k-binders-of (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) (productof (1 k-binders) (2 int)))
  (lambda (t) (k-binders-from (k-resolve t) nil)))

(define k-unknown? (subr (maxeff (read @globals) (read @t)) (k-binders int) bool)
  (lambda (kinds v) (cond ((null? kinds) #f) ((= (extract (car kinds) 1) v) #t) (else (k-unknown? (cdr kinds) v)))))
(define k-open? (subr (maxeff (read @globals) (read @t)) (k-binders k-solved int) bool)
  (lambda (kinds solved v) (and (k-unknown? kinds v) (null? (k-map-find (get solved) v)))))
(define k-solve (subr kstate (k-solved int k-desc) unit)
  (lambda (solved v d) (set solved (cons (cons v d) (get solved)))))

;; `a ≤ b`: region `a` won't outlive region `b`. The same; `b` a constant
;; (which never ends: `@name`, a fresh region, `const`); `b` bound around
;; `a`'s binder; or `a`'s bound won't outlive `b`.
(define k-outlived? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-region k-region) bool)
  (lambda (a b)
    (or (k-region=? a b)
        (tagcase b
          (r-var (w)
            (tagcase a
              (r-frozen (p f) (and (>= p 0) (k-outlived? (r-var p) b)))
              (r-var (v)
                (or (k-has-id? (k-outer-of v) w)
                    (let ((c (k-bound-of v)))
                      (and (not (null? c)) (and (not (k-region=? (car c) a)) (k-outlived? (car c) b))))))
              (else x #f)))
          (else y #t)))))

;; Each region binder nothing has solved gets a fresh region of its own,
;; named after it; or, if it has a bound, its bound, as solved (so `(rcons p
;; x y)`, with nothing else saying, allocates at `p`'s own region). A bounded
;; binder waits for its bound to be solved.
(define k-default-bounded (subr kstate (k-binders k-binders k-solved) unit)
  (lambda (all kinds solved)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (bd (k-bound-of v)))
          (begin
            (if (and (= (extract (car kinds) 2) 0) (and (null? (k-map-find (get solved) v)) (not (null? bd))))
                (tagcase (car bd)
                  (r-var (w)
                    (let ((f (k-map-find (get solved) w)))
                      (cond ((not (null? f)) (tagcase (cdr (car f)) (dr (x) (k-solve solved v (dr x))) (else y #u)))
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
               (waits (and (not (null? bd)) (tagcase (car bd) (r-var (w) (k-unknown? all w)) (else y #f)))))
          (begin
            (if (and (= (extract (car kinds) 2) 0) (and (null? (k-map-find (get solved) v)) (not waits)))
                (k-solve solved v (dr (k-fresh-region (string-append "@" (symbol->string (k-dvar-name v))))))
                #u)
            (k-default-free all (cdr kinds) solved))))))

(define k-default-regions (subr kstate (k-binders k-solved) unit)
  (lambda (kinds solved)
    (begin (k-default-bounded kinds kinds solved) (k-default-free kinds kinds solved))))

;; Each bounded region binder, as solved, won't outlive its bound, as solved;
;; or an error saying which would.
;; Whether `t` is data: built only from base types, `datum`, products and
;; sums, and pairs and bloblets that are frozen, of data; and type variables
;; of kind `data`.
(define-rec
  (k-data-walk (subr (maxeff kstate spin) (int int) bool)
    (lambda (t seen)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #t
            (tagcase (k-get t)
              (ty-base (s) #t)
              (ty-void () #t)
              (ty-var (v) (k-data-var? v))
              (ty-product (ps) (k-data-parts ps seen))
              (ty-sum (ps) (k-data-parts ps seen))
              (ty-pair (a b r) (and (tagcase r (r-frozen (p f) #t) (else y #f)) (k-data-walk a seen) (k-data-walk b seen)))
              (ty-bloblet (fs z r) (and z (k-data-list fs seen)))
              (ty-nlist (e z r) (k-data-walk e seen))
              (ty-nat (z) #t)
              (else y #f))))))
  (k-data-parts (subr (maxeff kstate spin) (k-parts int) bool)
    (lambda (ps seen) (or (null? ps) (and (k-data-walk (extract (car ps) 2) seen) (k-data-parts (cdr ps) seen)))))
  (k-data-list (subr (maxeff kstate spin) (k-ids int) bool)
    (lambda (ts seen) (or (null? ts) (and (k-data-walk (car ts) seen) (k-data-list (cdr ts) seen))))))
(define k-is-data? (subr (maxeff kstate spin) (int) bool)
  (lambda (t) (k-data-walk t (k-new-epoch))))
;; `t` with its frozen regions made acyclic: what data `acyclic?` has found
;; acyclic is.
(define k-fin-region (subr (read @globals) (k-region) k-region)
  (lambda (r) (tagcase r (r-frozen (p f) (r-frozen p #t)) (else y r))))
(define-rec
  (k-finitize (subr (maxeff kstate spin) (int (ref (listof (pairof int int @t) acyclic) @t)) int)
    (lambda (t memo)
      (let* ((t (k-resolve t)) (done (k-memo-find (get memo) t)))
        (if (>= done 0)
            done
            (if (not (tagcase (k-get t) (ty-pair (a b r) #t) (ty-product (ps) #t) (ty-sum (ps) #t) (ty-bloblet (fs z r) #t) (else y #f)))
                t
                (let ((slot (k-slot)))
                  (begin
                    (set memo (cons (cons t slot) (get memo)))
                    (let ((new (tagcase (k-get t)
                                 (ty-pair (a b r) (let* ((a2 (k-finitize a memo)) (b2 (k-finitize b memo))) (ty-pair a2 b2 (k-fin-region r))))
                                 (ty-product (ps) (ty-product (k-finitize-parts ps memo)))
                                 (ty-sum (ps) (ty-sum (k-finitize-parts ps memo)))
                                 (ty-bloblet (fs z r) (ty-bloblet (k-finitize-list fs memo) z (k-fin-region r)))
                                 (else y (k-get t)))))
                      (begin (k-set-link slot (k-ty-new new)) slot)))))))))
  (k-finitize-parts (subr (maxeff kstate spin) (k-parts (ref (listof (pairof int int @t) acyclic) @t)) k-parts)
    (lambda (ps memo)
      (if (null? ps)
          nil
          (let* ((x (k-finitize (extract (car ps) 2) memo)) (rest (k-finitize-parts (cdr ps) memo)))
            (cons (product (1 (extract (car ps) 1)) (2 x)) rest)))))
  (k-finitize-list (subr (maxeff kstate spin) (k-ids (ref (listof (pairof int int @t) acyclic) @t)) k-ids)
    (lambda (ts memo) (if (null? ts) nil (let* ((x (k-finitize (car ts) memo)) (rest (k-finitize-list (cdr ts) memo))) (cons x rest))))))
(define k-finitized (subr (maxeff kstate spin) (int) int)
  (lambda (t) (k-finitize t (the (ref (listof (pairof int int @t) acyclic) @t) (new nil)))))
;; Which binding of `s` is in scope: how deep its name's stack is.
(define k-binding-depth (subr (maxeff (read @globals) (read @t) spin) (symbol) int)
  (lambda (s) (k-length (table-ref (get k-env) s nil))))
(define k-certified-has? (subr (maxeff (read @globals) (read @t)) ((listof (pairof symbol int @t) acyclic) symbol int) bool)
  (lambda (cs s d) (and (not (null? cs)) (or (and (symbol=? (car (car cs)) s) (= (cdr (car cs)) d)) (k-certified-has? (cdr cs) s d)))))
(define k-sc-one-arg? (subr (read @t) (kxs) bool) (lambda (xs) (and (not (null? xs)) (null? (cdr xs)))))
(define k-check-bounds (subr (maxeff checks spin) (k-binders k-map int int) unit)
  (lambda (kinds m a b)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (bd (k-bound-of v)))
          (begin
            ;; A `data` binder takes only data.
            (if (= (extract (car kinds) 2) 4)
                (let ((f (k-map-find m v)))
                  (if (null? f)
                      #u
                      (tagcase (cdr (car f))
                        (dt (t) (if (k-is-data? t)
                                    #u
                                    (k-fail (k-cat5 (k-quote (symbol->string (k-dvar-name v))) " is bound as data, and a " (k-show-ty t) " is not data" "")
                                            a b)))
                        (else z #u))))
                #u)
            (if (null? bd)
                #u
                (let ((r (k-subst-region (r-var v) m)) (c (k-subst-region (car bd) m)))
                  (if (k-outlived? r c)
                      #u
                      (k-fail (k-cat5 (k-quote (symbol->string (k-dvar-name v))) " must not outlive "
                                      (k-quote (k-region-show (car bd)))
                                      ", and " (k-cat3 (k-region-show r) " could outlive " (k-region-show c)))
                              a b))))
            (k-check-bounds (cdr kinds) m a b))))))
;; A size binder instantiated as `finite` is sound only where it stands for
;; one size a caller supplies (`docs/research/soundness-findings.md`, F4): as
;; the size of at most one parameter, that parameter's own `(nlist T v)` or
;; `(nat v)` (less a constant, perhaps), and nowhere else a caller supplies
;; or can write. Its occurrences in what the callee gives back only forget a
;; size. Polarity: 1 given back, -1 supplied by a caller, 0 both, as in
;; anything that can be written.
(define k-size-alone? (subr pure (k-size int) bool)
  (lambda (z v)
    (tagcase z
      (sz-lin (k ts) (and (<= k 0) (not (null? ts)) (null? (cdr ts)) (= (car (car ts)) v) (= (cdr (car ts)) 1)))
      (else y #f))))
(define k-size-bad (subr (read @globals) (k-size int int) int)
  (lambda (z pol v)
    (if (and (not (= pol 1)) (tagcase z (sz-lin (k ts) (not (= (k-coef-of ts v) 0))) (else y #f))) 1 0)))
(define-type k-seen-pol (ref (listof (pairof int int @t) acyclic) @t))
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
                (ty-subr (e ps r cv) (+ (k-size-walk-list ps (- 0 pol) v seen) (k-size-walk r pol v seen)))
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
      (if (null? ts) 0 (let ((here (k-size-walk (car ts) pol v seen))) (+ here (k-size-walk-list (cdr ts) pol v seen))))))
  (k-size-walk-parts (subr (maxeff kstate spin) (k-parts int int k-seen-pol) int)
    (lambda (ps pol v seen)
      (if (null? ps) 0 (let ((here (k-size-walk (extract (car ps) 2) pol v seen))) (+ here (k-size-walk-parts (cdr ps) pol v seen))))))
  (k-size-walk-descs (subr (maxeff kstate spin) ((listof k-desc acyclic) int k-seen-pol) int)
    (lambda (ds v seen)
      (if (null? ds)
          0
          (let ((here (tagcase (car ds) (dz (z) (k-size-bad z 0 v)) (dt (x) (k-size-walk x 0 v seen)) (else y 0))))
            (+ here (k-size-walk-descs (cdr ds) v seen)))))))
;; Each parameter's count of such occurrences, and how many parameters are
;; sized by `v` alone.
(define k-size-params (subr (maxeff kstate spin) (k-ids int k-seen-pol) (productof (1 int) (2 int)))
  (lambda (ps v seen)
    (if (null? ps)
        (product (1 0) (2 0))
        (let* ((p (k-resolve (car ps)))
               (here (tagcase (k-get p)
                       (ty-nat (z) (if (k-size-alone? z v) (product (1 0) (2 1)) (product (1 (k-size-walk p -1 v seen)) (2 0))))
                       (ty-nlist (e z r)
                         (if (k-size-alone? z v) (product (1 (k-size-walk e -1 v seen)) (2 1)) (product (1 (k-size-walk p -1 v seen)) (2 0))))
                       (else y (product (1 (k-size-walk p -1 v seen)) (2 0)))))
               (rest (k-size-params (cdr ps) v seen)))
          (product (1 (+ (extract here 1) (extract rest 1))) (2 (+ (extract here 2) (extract rest 2))))))))
(define k-finite-size-ok? (subr (maxeff kstate spin) (int int) bool)
  (lambda (body v)
    (let ((seen (the k-seen-pol (new nil))))
      (tagcase (k-get (k-resolve body))
        (ty-subr (e ps r cv)
          (let* ((counts (k-size-params ps v seen)) (res (k-size-walk r 1 v seen)))
            (and (= (+ (extract counts 1) res) 0) (<= (extract counts 2) 1))))
        (else y (= (k-size-walk body 1 v seen) 0))))))
;; `t` with the sizes named since `saved` forgotten, as `finite`: they mean
;; nothing outside the scope that named them. Pops them.
;; `t` with the sizes named since `saved` forgotten, as `finite`: they mean
;; nothing outside the scope that named them. Pops them. Each stands for one
;; value's size, which no caller chooses, so it may be forgotten only where
;; `t` gives it back: where a caller would supply something of that size,
;; forgetting it would let any size in (`docs/research/soundness-findings.md`,
;; F8), and that is an error at `a`–`b`.
(define k-forget-nats (subr (maxeff checks spin) (k-ids int int int) int)
  (lambda (saved t a b)
    (letrec ((named (subr (maxeff (read @globals) kstate spin) (k-ids k-ids) k-ids)
                      (lambda (vs out) (if (= (k-length vs) (k-length saved)) out (named (cdr vs) (the k-ids (cons (car vs) out))))))
             (check (subr (maxeff (read @globals) checks spin) (k-ids) unit)
                      (lambda (vs)
                        (cond ((null? vs) #u)
                              ((> (k-size-walk t 1 (car vs) (the k-seen-pol (new nil))) 0)
                               (let ((name (k-quote (symbol->string (k-dvar-name (car vs))))))
                                 (k-fail (k-cat5 (k-cat3 "this is a " (k-show-ty t) ", which takes something of the size of ") name
                                                 ", and that size is not known outside " name "'s scope")
                                         a b)))
                              (else (check (cdr vs))))))
             (go (subr (maxeff (read @globals) kstate spin) (k-ids k-map) k-map)
                   (lambda (vs m) (if (null? vs) m (go (cdr vs) (cons (cons (car vs) (dz (sz-finite))) m))))))
      (let ((vs (named (get k-skolems) nil)))
        (begin (set k-skolems saved)
               (check vs)
               (if (null? vs) t (k-subst t (go vs nil))))))))
(define k-check-finite-sizes (subr (maxeff checks spin) (k-binders k-map int int int) unit)
  (lambda (kinds m body a b)
    (if (null? kinds)
        #u
        (let* ((v (extract (car kinds) 1)) (f (k-map-find m v))
               (fin (and (= (extract (car kinds) 2) 5) (not (null? f))
                         (tagcase (cdr (car f)) (dz (z) (tagcase z (sz-finite () #t) (else w #f))) (else y #f)))))
          (if (and (= (extract (car kinds) 2) 5) (not (null? f))
                   (tagcase (cdr (car f)) (dz (z) (tagcase z (sz-finite () #f) (else w (not (k-size-nonneg? z))))) (else y #f)))
              ;; A size binder solved from `v + k` against a size is that
              ;; size less `k`: a natural only where the facts here show it.
              (let ((name (k-quote (symbol->string (k-dvar-name v))))
                    (z (tagcase (cdr (car f)) (dz (z) z) (else y (sz-finite)))))
                (k-fail (k-cat5 "the size " name " would be " (k-show-size z)
                                ", which is not known here to be no less than 0: an argument may be shorter than this procedure's type needs")
                        a b))
          (if (and fin (not (k-finite-size-ok? body v)))
              (let ((name (k-quote (symbol->string (k-dvar-name v)))))
                (k-fail (k-cat5 "the size " name " cannot be `finite` here: " name
                                " is the size of more than one argument, or of something inside one, and `finite` would not keep them the same")
                        a b))
              (k-check-finite-sizes (cdr kinds) m body a b)))))))
(define k-finish-each (subr (maxeff checks spin) (k-binders k-map int int int) k-map)
  (lambda (kinds m a b ft)
    (if (null? kinds)
        m
        (let ((v (extract (car kinds) 1)) (k (extract (car kinds) 2)))
          (cond ((not (null? (k-map-find m v))) (k-finish-each (cdr kinds) m a b ft))
                ((= k 1) (k-finish-each (cdr kinds) (cons (cons v (de nil)) m) a b ft))
                ;; A convention nothing says is the program's.
                ((= k 6) (k-finish-each (cdr kinds) (cons (cons v (dc (get k-conv-default))) m) a b ft))
                ;; A size nothing says is some size.
                ((= k 5) (k-finish-each (cdr kinds) (cons (cons v (dz (sz-finite))) m) a b ft))
                (else (k-fail (k-cat5 (k-quote (symbol->string (k-dvar-name v))) " cannot be inferred for " (k-show-ty ft)
                                      ": nothing here says what it is. Use `proj`, or `the`" "")
                              a b)))))))

;; The whole solution: every type binder solved, effects defaulting to pure.
(define k-finish (subr (maxeff checks spin) (k-binders k-solved int int int) k-map)
  (lambda (kinds solved a b ft) (k-finish-each kinds (get solved) a b ft)))

;; Solve a size binder: a pattern `v + k` against a size `s` gives
;; `v = s - k` (`finite` stays `finite`).
(define k-unify-size (subr (maxeff kstate spin) (k-size k-size k-binders k-solved) unit)
  (lambda (p a kinds solved)
    (tagcase p
      (sz-lin (k ts)
        (if (and (not (null? ts)) (null? (cdr ts)) (= (cdr (car ts)) 1))
            (let ((v (car (car ts))))
              (if (and (k-unknown? kinds v) (null? (k-map-find (get solved) v)))
                  (k-solve solved v (dz (k-size-plus a (- 0 k))))
                  #u))
            #u))
      (else y #u))))
(define k-wrong-shape? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int int) bool)
  (lambda (pattern actual)
    (let ((p (k-ty-rank pattern)) (a (k-ty-rank actual)))
      (cond ((or (= p 2) (= a 1)) #f)
            ((= p 3) (null? (k-as-subr actual)))
            ((and (= p 6) (= a 18)) #f)
            ;; A `nat` is an `int`.
            ((and (= p 0) (= a 19)) #f)
            (else (not (= p a)))))))

;; An argument of the wrong shape altogether is the error to report, before
;; any binder it left unsolved.
(define k-inst-shapes (subr (maxeff checks spin) (kxs k-ids int k-solved (arrayof int @t)) unit)
  (lambda (args params i solved done-t)
    (if (null? args)
        #u
        (let ((t (array-ref done-t i)))
          (if (and (>= t 0) (k-wrong-shape? (car params) t))
              (let ((p (k-subst (car params) (get solved))))
                (k-fail (k-cat5 "argument " (int->string (+ i 1)) " is a " (k-show-ty t) (k-cat3 ", where a " (k-show-ty p) " is expected"))
                        (k-start (car args)) (k-end (car args))))
              (k-inst-shapes (cdr args) (cdr params) (+ i 1) solved done-t))))))

;; Whether `t` mentions a binder of any kind not yet solved.
(define k-open-region? (subr (maxeff (read @globals) (read @t)) (k-region k-binders k-solved) bool)
  (lambda (r kinds solved)
    (tagcase r
      (r-var (v) (k-open? kinds solved v))
      (r-frozen (p f) (and (>= p 0) (k-open? kinds solved p)))
      (else y #f))))
(define k-open-conv? (subr (maxeff (read @globals) (read @t)) (k-conv k-binders k-solved) bool)
  (lambda (c kinds solved) (tagcase c (cv-var (v) (k-open? kinds solved v)) (else y #f))))
(define k-open-effect? (subr (maxeff (read @globals) (read @t)) (k-eff k-binders k-solved) bool)
  (lambda (e kinds solved)
    (cond ((null? e) #f)
          ((tagcase (car e) (a-var (v) (k-open? kinds solved v)) (else y (k-open-region? (k-atom-region (car e)) kinds solved))) #t)
          (else (k-open-effect? (cdr e) kinds solved)))))
(define k-push-ids (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-ids k-ids) k-ids)
  (lambda (xs onto) (if (null? xs) onto (cons (car xs) (k-push-ids (cdr xs) onto)))))
(define k-push-parts (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts k-ids) k-ids)
  (lambda (ps onto) (if (null? ps) onto (cons (extract (car ps) 2) (k-push-parts (cdr ps) onto)))))
(define k-descs-open? (subr (maxeff (read @globals) (read @t)) ((listof k-desc acyclic) k-binders k-solved) bool)
  (lambda (ds kinds solved)
    (and (not (null? ds))
         (or (tagcase (car ds)
               (dr (r) (k-open-region? r kinds solved))
               (de (e) (k-open-effect? e kinds solved))
               (dc (c) (k-open-conv? c kinds solved))
               (else y #f))
             (k-descs-open? (cdr ds) kinds solved)))))
;; Whether a size mentions a variable still to be solved.
(define k-size-open? (subr (maxeff kstate spin) (k-size k-binders k-solved) bool)
  (lambda (z kinds solved)
    (tagcase z
      (sz-lin (k ts) (letrec ((any (subr (maxeff (read @globals) kstate spin) (k-terms) bool)
                                   (lambda (xs) (and (not (null? xs)) (or (k-open? kinds solved (car (car xs))) (any (cdr xs)))))))
                       (any ts)))
      (else w #f))))
(define k-any-walk (subr (maxeff kstate spin) (k-ids int k-binders k-solved) bool)
  (lambda (stack seen kinds solved)
    (if (null? stack)
        #f
        (let ((t (k-resolve (car stack))) (rest (cdr stack)))
          (if (k-visit? t seen)
              (k-any-walk rest seen kinds solved)
              (let ((seen seen))
               (letrec ((reg (subr (maxeff (read @globals) (read @t)) (k-region) bool) (lambda (r) (k-open-region? r kinds solved)))
                        (go (subr (maxeff (read @globals) kstate spin) (k-ids) bool) (lambda (s) (k-any-walk s seen kinds solved))))
                (tagcase (k-get t)
                  (ty-var (v) (or (k-open? kinds solved v) (go rest)))
                  (ty-subr (e ps r cv) (or (k-open-effect? e kinds solved) (k-open-conv? cv kinds solved) (go (k-push-ids ps (cons r rest)))))
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
                  (ty-tag (x y e r) (or (reg r) (k-open-effect? e kinds solved) (go (cons x (cons y rest)))))
                  (ty-comp (x y e r) (or (reg r) (k-open-effect? e kinds solved) (go (cons x (cons y rest)))))
                  (ty-named (g ds) (or (k-descs-open? ds kinds solved) (go (k-push-ids (k-desc-types ds) rest))))
                  (ty-nlist (e z r) (or (reg r) (k-size-open? z kinds solved) (go (cons e rest))))
                  (ty-nat (z) (or (k-size-open? z kinds solved) (go rest)))
                  (else y (go rest))))))))))
(define k-mentions-any-unknown? (subr (maxeff kstate spin) (int k-binders k-solved) bool)
  (lambda (t kinds solved) (k-any-walk (cons t nil) (k-new-epoch) kinds solved)))

(define-rec
  (k-vars-walk (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int int k-binders k-solved) bool)
    (lambda (t seen kinds solved)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #f
            (letrec ((w (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int) bool) (lambda (x) (k-vars-walk x seen kinds solved)))
                  (ws (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-ids) bool) (lambda (xs) (k-vars-walks xs seen kinds solved))))
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
  (k-vars-walks (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-ids int k-binders k-solved) bool)
    (lambda (ts seen kinds solved) (cond ((null? ts) #f) ((k-vars-walk (car ts) seen kinds solved) #t) (else (k-vars-walks (cdr ts) seen kinds solved))))))

;; Whether `t` mentions a type binder not yet solved.
(define k-mentions-unknown-type? (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (int k-binders k-solved) bool)
  (lambda (t kinds solved) (k-vars-walk t (k-new-epoch) kinds solved)))
(define k-any-unknown-type? (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-ids k-binders k-solved) bool)
  (lambda (ts kinds solved)
    (cond ((null? ts) #f) ((k-mentions-unknown-type? (car ts) kinds solved) #t) (else (k-any-unknown-type? (cdr ts) kinds solved)))))
;; A convention binder takes the actual's convention, if nothing has yet.
(define k-unify-conv (subr kstate (k-conv k-conv k-binders k-solved) unit)
  (lambda (pc ac kinds solved)
    (tagcase pc
      (cv-var (v) (if (and (k-unknown? kinds v) (null? (k-map-find (get solved) v))) (k-solve solved v (dc ac)) #u))
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
(define k-same-kind-regions (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-eff int) k-regions)
  (lambda (e rank)
    (cond ((null? e) nil)
          ((= (k-atom-rank (car e)) rank) (cons (k-atom-region (car e)) (k-same-kind-regions (cdr e) rank)))
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
                           (prev (if (null? f) (the k-eff nil) (tagcase (cdr (car f)) (de (e) e) (else y (the k-eff nil))))))
                      (k-solve solved v (de (k-union prev actual))))
                    #u))
              (else y
                (tagcase (k-atom-region atom)
                  (r-var (v)
                    (if (k-open? kinds solved v)
                        (let ((same (k-same-kind-regions actual (k-atom-rank atom))))
                          (if (and (not (null? same)) (null? (cdr same))) (k-solve solved v (dr (car same))) #u))
                        #u))
                  (else z #u))))
            (k-unify-effect (cdr pattern) actual kinds solved))))))

;;; Matching: solve binders in `pattern` so that `actual` fits it. Never
;;; fails; what cannot be matched is left for the subtype check after.

(define-rec
  (k-unify (subr (maxeff kstate spin) (int int k-binders k-solved k-trail) unit)
    (lambda (pattern actual kinds solved trail)
      (let ((p (k-resolve pattern)) (a (k-resolve actual)))
        (if (k-trail-has? (get trail) p a)
            #u
            (begin
              (set trail (cons (cons p a) (get trail)))
              (let ((pt (k-get p)) (at (k-get a)))
                (if (and (tagcase at (ty-void () #t) (else y #f))
                         (not (tagcase pt (ty-var (v) (k-open? kinds solved v)) (else y #f))))
                    #u
                    (letrec ((u (subr (maxeff (read @globals) kstate spin) (int int) unit) (lambda (x y) (k-unify x y kinds solved trail)))
                          (ur (subr (maxeff (read @globals) kstate) (k-region k-region) unit) (lambda (r s) (k-unify-region r s kinds solved)))
                          (ue (subr (maxeff (read @globals) kstate spin) (k-eff k-eff) unit) (lambda (e f) (k-unify-effect e f kinds solved))))
                      (tagcase pt
                        (ty-var (v)
                          (if (k-unknown? kinds v)
                              (let ((f (k-map-find (get solved) v)))
                                (if (null? f)
                                    (k-solve solved v (dt a))
                                    (tagcase (cdr (car f))
                                      (dt (prev) (if (and (not (k-subtype a prev)) (k-subtype prev a)) (k-solve solved v (dt a)) #u))
                                      (else y #u))))
                              #u))
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
                                     (u x2 (tagcase sz (sz-finite () a) (else w (k-ty-new (ty-nlist y (k-tail-size sz) s)))))))
                            (else z #u)))
                        (ty-nlist (x sz r) (tagcase at (ty-nlist (y sz2 s) (begin (ur r s) (u x y) (k-unify-size sz sz2 kinds solved))) (else z #u)))
                        (ty-nat (sz) (tagcase at (ty-nat (sz2) (k-unify-size sz sz2 kinds solved)) (else z #u)))
                        (ty-product (pp) (tagcase at (ty-product (pa) (k-unify-parts pp pa kinds solved trail)) (else z #u)))
                        (ty-sum (pp) (tagcase at (ty-sum (pa) (k-unify-parts pp pa kinds solved trail)) (else z #u)))
                        (ty-bloblet (fp zp r)
                          (tagcase at
                            (ty-bloblet (fa za s)
                              (if (= (k-length fp) (k-length fa)) (begin (ur r s) (k-unify-lists fp fa kinds solved trail)) #u))
                            (else z #u)))
                        (ty-tag (a1 h1 d1 r1)
                          (tagcase at (ty-tag (a2 h2 d2 r2) (begin (ur r1 r2) (u a1 a2) (u h1 h2) (ue d1 d2))) (else z #u)))
                        (ty-comp (h1 a1 d1 r1)
                          (tagcase at (ty-comp (h2 a2 d2 r2) (begin (ur r1 r2) (u a1 a2) (u h1 h2) (ue d1 d2))) (else z #u)))
                        (ty-named (g xs)
                          (tagcase at (ty-named (h ys) (if (= g h) (k-unify-descs xs ys kinds solved trail) #u)) (else z #u)))
                        (else z #u))))))))))
  (k-unify-descs (subr (maxeff kstate spin) ((listof k-desc acyclic) (listof k-desc acyclic) k-binders k-solved k-trail) unit)
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
      (if (null? xs) #u (begin (k-unify (car xs) (car ys) kinds solved trail) (k-unify-lists (cdr xs) (cdr ys) kinds solved trail)))))
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
    (let* ((bo (k-binders-of t)) (kinds (extract bo 1)) (inner (extract bo 2)) (solved (the k-solved (new nil))))
      (begin
        (k-unify inner expected kinds solved (the k-trail (new nil)))
        (k-default-regions kinds solved)
        (let ((m (k-finish kinds solved a b t)))
          (begin (k-check-bounds kinds m a b) (k-check-finite-sizes kinds m inner a b) (let ((inst (k-subst inner m))) (begin (k-no-knot inst a b) inst))))))))
(define k-plambda-matches? (subr (maxeff (read @globals) (read @t)) (kx k-ty) bool)
  (lambda (x et)
    (tagcase x
      (x-plambda (binders body a b)
        (tagcase et (ty-poly (bs want) (and (= (k-length bs) (k-length binders)) (k-same-kinds? bs binders))) (else y #f)))
      (else y #f))))
(define k-same-labels? (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 symbol) (2 kx)) acyclic) k-parts) bool)
  (lambda (fs ps)
    (cond ((null? fs) (null? ps))
          ((null? ps) #f)
          (else (and (symbol=? (extract (car fs) 1) (extract (car ps) 1)) (k-same-labels? (cdr fs) (cdr ps)))))))

;;; ------------------------------------------------------------ tagcase

(define-type k-arms (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) acyclic))
(define k-all-fit? (subr (maxeff kstate spin) (k-ids int) bool)
  (lambda (types t) (cond ((null? types) #t) ((k-subtype (car types) t) (k-all-fit? (cdr types) t)) (else #f))))
;; The first of `candidates` every one of `types` fits, or -1.
(define k-upper-bound (subr (maxeff kstate spin) (k-ids k-ids) int)
  (lambda (candidates types)
    (cond ((null? candidates) -1)
          ((k-all-fit? types (car candidates)) (car candidates))
          (else (k-upper-bound (cdr candidates) types)))))
(define k-part-names (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts) (listof string acyclic))
  (lambda (ps) (if (null? ps) nil (cons (symbol->string (extract (car ps) 1)) (k-part-names (cdr ps))))))
(define k-arm-named? (subr (maxeff (read @globals) (read @t)) (k-arms symbol) bool)
  (lambda (arms l) (cond ((null? arms) #f) ((symbol=? (extract (car arms) 1) l) #t) (else (k-arm-named? (cdr arms) l)))))
(define k-variants-not-named (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-parts k-arms) k-parts)
  (lambda (vs arms)
    (cond ((null? vs) nil)
          ((k-arm-named? arms (extract (car vs) 1)) (k-variants-not-named (cdr vs) arms))
          (else (cons (car vs) (k-variants-not-named (cdr vs) arms))))))
(define k-cannot-take-apart (subr (maxeff checks spin) (symbol int k-names kx) k-bindings)
  (lambda (tag t names body)
    (k-fail (k-cat5 (k-quote (symbol->string tag)) " carries a " (k-show-ty t) ", which cannot be taken apart into "
                    (string-append (int->string (k-length names)) " name(s)"))
            (k-start body) (k-end body))))
(define k-zip-fields (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names k-parts) k-bindings)
  (lambda (ns fs) (if (null? ns) nil (cons (cons (car ns) (extract (car fs) 2)) (k-zip-fields (cdr ns) (cdr fs))))))
;; The atoms of `e` in neither `bound` nor `own`.
(define k-beyond (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-eff k-eff k-eff) k-eff)
  (lambda (e bound own)
    (cond ((null? e) nil)
          ((or (k-covered? bound (car e)) (k-contains? own (car e))) (k-beyond (cdr e) bound own))
          (else (cons (car e) (k-beyond (cdr e) bound own))))))
(define k-none-reach? (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (k-names k-names k-region) bool)
  (lambda (vs tv r)
    (cond ((null? vs) #t)
          ((k-has-name? tv (car vs)) (k-none-reach? (cdr vs) tv r))
          (else (let ((t (k-lookup (car vs))))
                  (and (or (< t 0) (not (k-has-region-in? (k-regions-in t) r))) (k-none-reach? (cdr vs) tv r)))))))
;; Whether the only way `body` can name anything in region `r` is the
;; variable `tag`, if it is one.
(define k-reaches-only? (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t) spin) (kx kx k-region) bool)
  (lambda (body tag r)
    (let ((tv (the k-names (tagcase tag (x-var (s a b) (cons s nil)) (else y nil)))))
      (k-none-reach? (k-free-vars body) tv r))))

;;; ------------------------------------------------------------ synthesis

(define k-has-comefrom? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (tagcase (car e) (a-comefrom (r) #t) (else y #f)) (k-has-comefrom? (cdr e))))))
;; `(letrena r …)`'s or `(letreap r …)`'s body, of type `t` and effect `e`,
;; closed: its value
;; may not mention `r`, and no continuation captured in it may outlive it;
;; what it does to `r` is masked, as nothing outside can name `r`.
(define k-close-region (subr (maxeff checks spin) (kx string int int k-eff int int) k-te)
  (lambda (x form r t e a b)
    (let ((name (k-cat3 form " " (symbol->string (k-dvar-name r)))))
      (if (k-has-region-in? (k-regions-in t) (r-var r))
          (k-fail (k-cat4 "the value of `" name "` would outlive its region: its type is " (k-show-ty t)) a b)
          (let ((masked (k-mask x e t)))
            (if (k-has-comefrom? masked)
                (k-fail (k-cat4 "a continuation captured in `" name "` could outlive its region: its effect is "
                                (k-show-effect masked))
                        a b)
                (k-te t masked)))))))

;; Whether an effect writes region `r`.
(define k-eff-writes? (subr (maxeff (read @globals) (read @t) spin) (k-eff k-region) bool)
  (lambda (e r)
    (and (not (null? e))
         (or (tagcase (car e) (a-write (x) (k-region=? x r)) (else y #f)) (k-eff-writes? (cdr e) r)))))
;; A generative type's representation writing one of its parameters writes
;; whatever it was given: cautiously, any region given any. Whether some
;; effect in a walk wrote a parameter, and whether some generative type was
;; given the region.
(define k-wrote-param (ref bool @t) (new #f))
(define k-given (ref bool @t) (new #f))
(define k-eff-writes-param? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e) (a-write (x) (k-gen-region? x)) (a-var (v) (k-gen-param? v)) (else y #f))
             (k-eff-writes-param? (cdr e))))))
(define k-eff-writes-noting? (subr (maxeff kstate spin) (k-eff k-region) bool)
  (lambda (e r)
    (begin
      (if (k-eff-writes-param? e) (set k-wrote-param #t) #u)
      (k-eff-writes? e r))))
(define k-note-given (subr (maxeff kstate spin) ((listof k-desc acyclic) k-region) unit)
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
              (ty-subr (e ps x cv) (or (k-eff-writes-noting? e r) (or (k-writes-list ps r seen) (k-writes-in x r seen))))
              (ty-tag (a h e x) (or (k-eff-writes-noting? e r) (or (k-writes-in a r seen) (k-writes-in h r seen))))
              (ty-comp (b a e x) (or (k-eff-writes-noting? e r) (or (k-writes-in a r seen) (k-writes-in b r seen))))
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
                       (or (k-writes-in (extract (k-gen-of g) 4) r seen) (k-writes-list (k-desc-types ds) r seen))))
              (else x #f))))))
  (k-writes-list (subr (maxeff kstate spin) (k-ids k-region int) bool)
    (lambda (ts r seen) (and (not (null? ts)) (or (k-writes-in (car ts) r seen) (k-writes-list (cdr ts) r seen)))))
  (k-writes-parts (subr (maxeff kstate spin) (k-parts k-region int) bool)
    (lambda (ps r seen) (and (not (null? ps)) (or (k-writes-in (extract (car ps) 2) r seen) (k-writes-parts (cdr ps) r seen))))))

(define k-any-frozen? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (k-frozen-atom? (car e)) (k-any-frozen? (cdr e))))))
(define k-writes-frozen? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (and (k-frozen-atom? (car e)) (= (k-atom-rank (car e)) 1)) (k-writes-frozen? (cdr e))))))
;; `e` without its reads, allocations and awaits on `const`, which are pure.
(define k-drop-frozen (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-eff) k-eff)
  (lambda (e)
    (cond ((null? e) nil)
          ;; Only data frozen in the heap, which never ends; what is done to
          ;; data frozen into a place stays, until masking removes it.
          ((and (k-frozen-atom? (car e)) (let ((k (k-atom-rank (car e)))) (or (= k 0) (or (= k 2) (= k 5))))
                (tagcase (k-atom-region (car e)) (r-frozen (p f) (< p 0)) (else y #f)))
           (k-drop-frozen (cdr e)))
          (else (cons (car e) (k-drop-frozen (cdr e)))))))
;; `x`'s effect `e`, noted.
(define k-note-effect (subr (maxeff (read @globals) (read @t) (write @t) (alloc @t)) (kx k-eff) unit)
  (lambda (x e) (set k-effect-notes (the k-facts (cons (product (1 (k-start x)) (2 (k-end x)) (3 (k-summary e))) (get k-effect-notes))))))
;; `e`, the effect of `x`, with what it does to frozen data taken out; or an
;; error, if it writes it.
(define k-frozen (subr checks (kx k-eff) k-eff)
  (lambda (x e)
    (cond ((not (k-any-frozen? e)) e)
          ((k-writes-frozen? e) (k-fail "this writes frozen data, whose region is `const`" (k-start x) (k-end x)))
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

;; Whether a procedure of type `t` could be given itself: a cycle in `t`
;; runs through a parameter of a procedure (or the argument of a
;; continuation). A type that is merely recursive, as a list is, does not let
;; anything loop. `path`: the nodes on the way down, newest first, each with
;; whether it was reached through a parameter.
(define-type k-cpath (listof (pairof int bool @t) acyclic))
(define k-on-path? (subr (maxeff (read @globals) (read @t)) (k-cpath int) bool)
  (lambda (path t) (and (not (null? path)) (or (= (car (car path)) t) (k-on-path? (cdr path) t)))))
;; Whether a node newer than `t` on the path was reached through a parameter.
(define k-newer-param? (subr (maxeff (read @globals) (read @t)) (k-cpath int) bool)
  (lambda (path t) (and (not (= (car (car path)) t)) (or (cdr (car path)) (k-newer-param? (cdr path) t)))))
(define-rec
  (k-cyclic-from? (subr (maxeff kstate spin) (int bool k-cpath) bool)
    (lambda (t by path)
      (let ((t (k-resolve t)))
        (cond ((k-on-path? path t) (or by (k-newer-param? path t)))
              ;; Too deep to follow: it may loop, the cautious answer.
              ((> (k-length path) 64) #t)
              (else
               (let ((p (the k-cpath (cons (cons t by) path))))
                 (tagcase (k-get t)
                   (ty-subr (e ps r cv) (or (k-cyclic-list? ps #t p) (k-cyclic-from? r #f p)))
                   (ty-comp (x a e r) (or (k-cyclic-from? x #t p) (k-cyclic-from? a #f p)))
                   (ty-tag (a h e r) (or (k-cyclic-from? a #f p) (k-cyclic-from? h #f p)))
                   (ty-poly (bs x) (k-cyclic-from? x #f p))
                   (ty-ref (a r) (k-cyclic-from? a #f p))
                   (ty-array (a r) (k-cyclic-from? a #f p))
                   (ty-icell (a r) (k-cyclic-from? a #f p))
                   (ty-markkey (a r) (k-cyclic-from? a #f p))
                   (ty-pair (a b r) (or (k-cyclic-from? a #f p) (k-cyclic-from? b #f p)))
                   (ty-bloblet (fs z r) (k-cyclic-list? fs #f p))
                   (ty-product (ps) (k-cyclic-parts? ps p))
                   (ty-sum (ps) (k-cyclic-parts? ps p))
                   ;; Through its representation; what it was given,
                   ;; cautiously, as if taken as a parameter.
                   (ty-named (g ds) (or (k-cyclic-from? (extract (k-gen-of g) 4) #f p) (k-cyclic-list? (k-desc-types ds) #t p)))
                   (ty-nlist (e z r) (k-cyclic-from? e #f p))
                   (else x #f))))))))
  (k-cyclic-list? (subr (maxeff kstate spin) (k-ids bool k-cpath) bool)
    (lambda (ts by path) (and (not (null? ts)) (or (k-cyclic-from? (car ts) by path) (k-cyclic-list? (cdr ts) by path)))))
  (k-cyclic-parts? (subr (maxeff kstate spin) (k-parts k-cpath) bool)
    (lambda (ps path) (and (not (null? ps)) (or (k-cyclic-from? (extract (car ps) 2) #f path) (k-cyclic-parts? (cdr ps) path))))))
(define k-cyclic? (subr (maxeff kstate spin) (int) bool)
  (lambda (t) (k-cyclic-from? t #f nil)))
;; `f` under any projections and ascriptions.
(define k-under (subr (read @globals) (kx) kx)
  (lambda (f) (tagcase f (x-proj (body ds a b) (k-under body)) (x-the (t body a b) (k-under body)) (else y f))))
;; Whether `k` is named in `x` only as the operator of calls, evaluated as
;; `x` is: not under a `lambda` (which could be called later) or a prompt
;; (whose captures could be composed later).
(define-rec
  (k-only-called? (subr (maxeff (read @globals) (read @t) (alloc @t)) (kx symbol) bool)
    (lambda (x k)
      (tagcase x
        (x-var (s a b) (not (symbol=? s k)))
        (x-const (t v a b) #t)
        (x-app (f args a b)
          (and (or (tagcase f (x-var (s fa fb) (symbol=? s k)) (else y #f)) (k-only-called? f k))
               (k-only-called-list? args k)))
        (x-lambda (ps body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-plambda (bs body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-rlambda (r l a b) (not (k-has-name? (k-free-vars x) k)))
        (x-letrec (bs body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-prompt (t body h a b) (not (k-has-name? (k-free-vars x) k)))
        (x-let (bs body a b)
          (and (k-only-called-lets? bs k) (or (k-has-name? (k-let-names bs nil) k) (k-only-called? body k))))
        (x-letregion (m r i body a b) (or (symbol=? (k-dvar-name r) k) (k-only-called? body k)))
        (x-tagcase (s arms els a b)
          (and (k-only-called? s k)
               (k-only-called-arms? arms k)
               (or (null? els) (symbol=? (extract (car els) 1) k) (k-only-called? (extract (car els) 2) k))))
        (x-proj (body ds a b) (k-only-called? body k))
        (x-the (t body a b) (k-only-called? body k))
        (x-convention (c body a b) (k-only-called? body k))
        (x-extract (body l a b) (k-only-called? body k))
        (x-sum (l body a b) (k-only-called? body k))
        (x-if (p c d a b) (and (k-only-called? p k) (k-only-called? c k) (k-only-called? d k)))
        (x-begin (xs a b) (k-only-called-list? xs k))
        (x-bloblet (o i xs a b) (k-only-called-list? xs k))
        (x-product (fs a b) (k-only-called-lets? fs k)))))
  (k-only-called-list? (subr (maxeff (read @globals) (read @t) (alloc @t)) (kxs symbol) bool)
    (lambda (xs k) (or (null? xs) (and (k-only-called? (car xs) k) (k-only-called-list? (cdr xs) k)))))
  (k-only-called-lets? (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 kx)) acyclic) symbol) bool)
    (lambda (bs k) (or (null? bs) (and (k-only-called? (extract (car bs) 2) k) (k-only-called-lets? (cdr bs) k)))))
  (k-only-called-arms? (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-arms symbol) bool)
    (lambda (arms k)
      (or (null? arms)
          (and (or (k-has-name? (extract (car arms) 3) k) (k-only-called? (extract (car arms) 4) k))
               (k-only-called-arms? (cdr arms) k))))))
;; Whether the receiver of `cwcc` at type `ft` may capture a continuation:
;; its latent effect has a `comefrom`. Unknown counts as may.
(define k-receiver-captures? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) bool)
  (lambda (ft)
    (let ((c (k-as-subr ft)))
      (or (null? c) (null? (extract (car c) 2))
          (let ((r (k-as-subr (k-resolve (car (extract (car c) 2))))))
            (or (null? r)
                (letrec ((any (subr (read @globals) (k-eff) bool)
                              (lambda (e) (and (not (null? e)) (or (tagcase (car e) (a-comefrom (x) #t) (else y #f)) (any (cdr e)))))))
                  (any (extract (car r) 1)))))))))
;; Whether `r`, given to `cwcc`, is a `lambda` whose continuation can only
;; be called while `cwcc` runs, so can only leave it
;; (`docs/research/soundness-findings.md`, F3).
(define k-escape-only? (subr (maxeff (read @globals) (read @t) (alloc @t)) (kx) bool)
  (lambda (r)
    (tagcase r
      (x-the (t body a b) (k-escape-only? body))
      (x-lambda (ps body a b) (and (not (null? ps)) (null? (cdr ps)) (k-only-called? body (extract (car ps) 1))))
      (else y #f))))
;; The name `f` is, under any projections and ascriptions, if a variable.
(define k-callee-name (subr (maxeff (read @globals) (alloc @t)) (kx) (listof symbol acyclic))
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b) (k-callee-name body))
      (x-the (t body a b) (k-callee-name body))
      (x-var (n a b) (the (listof symbol acyclic) (cons n nil)))
      (else y (the (listof symbol acyclic) nil)))))
;; Whether `f` names a known procedure.
(define k-known-callee? (subr (maxeff kstate spin) (kx) bool)
  (lambda (f)
    (let ((s (k-callee-name f)))
      (and (not (null? s)) (let ((t (k-lookup (car s)))) (and (>= t 0) (k-known? (car s))))))))
;; Whether a call of `f` (instantiated to `ft`) may run for an unbounded
;; time beyond what its latent effect says: a call, in a recursive group's
;; lambdas, of the group; or a call through a recursive type of anything but
;; known code (self-application loops with no store at all). A knot through
;; the store needs nothing here: `k-no-knot` makes its type say `spin`.
(define k-may-spin? (subr (maxeff kstate spin) (kx int kxs) bool)
  (lambda (f ft args)
    (let* ((s (k-callee-name f))
           (t (if (null? s) -1 (k-lookup (car s)))))
      (cond ;; A continuation called after `cwcc` has returned comes back to
            ;; it again, as often as it is called: only one that can only
            ;; leave needs no `spin`.
            ;; And the receiver must capture no continuation, which could
            ;; hold a call of `k` and be run after `cwcc` returns (F9): a
            ;; `comefrom` in its latent effect, `cwcc`'s `e` as solved.
            ((and (>= t 0) (string=? (symbol->string (car s)) "cwcc") (k-named-has? (get k-std) (car s) t))
             (or (k-receiver-captures? ft)
                 (not (and (not (null? args)) (null? (cdr args)) (k-escape-only? (car args))))))
            ((and (>= t 0) (k-named-has? (get k-recursive) (car s) t)) #t)
            ((and (>= t 0) (or (k-known? (car s)) (k-named-has? (get k-std) (car s) t))) #f)
            ((k-lambda? (k-under f)) #f)
            (else (k-cyclic? ft))))))
