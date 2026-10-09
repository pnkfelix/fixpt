;;; The checker, in FX-26: the binders of a `poly` instantiated, solved by
;;; matching: their defaults (`pure`, a fresh region), the bounds regions
;;; must keep, and what size binders may be. After `check-bounds.fx`;
;;; `check-infer.fx` uses it (split from that file, `TODO.md` §68).

;; Its types (`check-infer-types.fx`, its file's after it), loaded before the
;; module so that they are not among its values; the module names what it
;; uses of them.
(define check-infer-types (load-module "fx26:check-infer-types.fx"))
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-binders-module (module
(define-type k-solved (select check-infer-types k-solved))
(define-type k-bound-body (select check-infer-types k-bound-body))
(define-type k-counts (select check-infer-types k-counts))

(define k-append-binders (subr kmakes (k-binders k-binders) k-binders)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (k-append-binders (cdr xs) ys)))))
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
;; Whether `k-finitize` rebuilds a node: a pair, product, sum, bloblet or
;; union.
(define k-finitizes? (subr pure (k-ty) bool)
  (lambda (n)
    (tagcase n
      (ty-pair (a b r nl) #t) (ty-product (ps) #t) (ty-sum (ps) #t) (ty-bloblet (fs z r) #t)
      (ty-union (ms) #t) (else y #f))))
(define-rec
  (k-finitize (subr (maxeff kstate spin) (int k-smemo) int)
    (lambda (t memo)
      (let* ((t (k-resolve t)) (done (table-ref memo t -1)))
        (cond ((>= done 0) done)
              ((not (k-finitizes? (k-get t))) t)
              (else
               (let ((slot (k-slot)))
                 (begin
                   (table-set! memo t slot)
                   (let ((new (k-finitize-node t memo)))
                     (begin (k-set-link slot (k-ty-new new)) slot)))))))))
  ;; Node `t`, its parts made acyclic, and its region if frozen.
  (k-finitize-node (subr (maxeff kstate spin) (int k-smemo) k-ty)
    (lambda (t memo)
      (tagcase (k-get t)
        (ty-pair (a b r nl)
          (let* ((a2 (k-finitize a memo)) (b2 (k-finitize b memo)))
            (ty-pair a2 b2 (k-fin-region r) nl)))
        (ty-product (ps) (ty-product (k-finitize-parts ps memo)))
        (ty-sum (ps) (ty-sum (k-finitize-parts ps memo)))
        (ty-bloblet (fs z r) (ty-bloblet (k-finitize-list fs memo) z (k-fin-region r)))
        (ty-union (ms) (ty-union (k-finitize-list ms memo)))
        (else y (k-get t)))))
  (k-finitize-parts (subr (maxeff kstate spin) (k-parts k-smemo) k-parts)
    (lambda (ps memo)
      (if (null? ps)
          nil
          (let* ((x (k-finitize (extract (car ps) 2) memo))
                 (rest (k-finitize-parts (cdr ps) memo)))
            (cons (product (1 (extract (car ps) 1)) (2 x)) rest)))))
  (k-finitize-list (subr (maxeff kstate spin) (k-ids k-smemo) k-ids)
    (lambda (ts memo)
      (if (null? ts)
          nil
          (let* ((x (k-finitize (car ts) memo)) (rest (k-finitize-list (cdr ts) memo)))
            (cons x rest))))))
(define k-finitized (subr (maxeff kstate spin) (int) int)
  (lambda (t) (k-finitize t (k-new-smemo))))
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
                ;; What a description function is given, it may use either way.
                (ty-app (f ds) (k-size-walk-descs ds v seen))
                (ty-subr (e ps r cv)
                  (+ (k-size-walk-list ps (- 0 pol) v seen) (k-size-walk r pol v seen)))
                (ty-poly (bs body) (k-size-walk body pol v seen))
                (ty-pair (x y r nl)
                  (let ((p (tagcase r (r-frozen (q f) pol) (else w 0))))
                    (+ (k-size-walk x p v seen) (k-size-walk y p v seen))))
                (ty-bloblet (fs z r) (k-size-walk-list fs (if z pol 0) v seen))
                (ty-product (ps) (k-size-walk-parts ps pol v seen))
                (ty-sum (ps) (k-size-walk-parts ps pol v seen))
                (ty-union (ms) (k-size-walk-list ms pol v seen))
                (ty-ref (x r) (k-size-walk x 0 v seen))
                (ty-array (x r) (k-size-walk x 0 v seen))
                (ty-icell (x r) (k-size-walk x 0 v seen))
                (ty-markkey (x r) (k-size-walk x 0 v seen))
                (ty-tag (x y e r) (+ (k-size-walk x 0 v seen) (k-size-walk y 0 v seen)))
                (ty-comp (x y e r) (+ (k-size-walk x 0 v seen) (k-size-walk y 0 v seen)))
                (ty-module (abs ds vs)
                  (+ (k-size-walk-parts ds 0 v seen) (k-size-walk-parts vs pol v seen)))
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
    (let ((vs (k-unescaped t (k-named-since saved (get k-skolems) nil) a b)))
      (begin (set k-skolems saved)
             (k-check-forgettable t vs a b)
             (if (null? vs) t (k-subst t (k-finite-map vs nil)))))))))

(define k-binders-of (with check-binders-module k-binders-of))
(define k-binding-depth (with check-binders-module k-binding-depth))
(define k-certified-has? (with check-binders-module k-certified-has?))
(define k-check-bounds (with check-binders-module k-check-bounds))
(define k-default-regions (with check-binders-module k-default-regions))
(define k-fin-region (with check-binders-module k-fin-region))
(define k-finite-size-ok? (with check-binders-module k-finite-size-ok?))
(define k-finitized (with check-binders-module k-finitized))
(define k-forget-nats (with check-binders-module k-forget-nats))
(define k-named-since (with check-binders-module k-named-since))
(define k-one-var? (with check-binders-module k-one-var?))
(define k-open? (with check-binders-module k-open?))
(define k-sc-one-arg? (with check-binders-module k-sc-one-arg?))
(define k-solve (with check-binders-module k-solve))
(define k-unknown? (with check-binders-module k-unknown?))
