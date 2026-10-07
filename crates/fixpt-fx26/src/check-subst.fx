;;; The checker, in FX-26: substitution, of types for type variables and of
;;; regions and effects for theirs (`k-subst` and its group). Before the
;;; types' reader, which applies type functions with it. After
;;; `check-syntax.fx`; part of the checker, `check-types.fx` first.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-subst-module (module
;; Pairs of integers.
(define-type k-pairs (listof (pairof int int @t) acyclic))
;; The same, of the parser's trees.
(define-type exp-params (listof (productof (1 symbol) (2 syns-a)) acyclic))
;; Looking at the checker's tables (`kreads`), and building more in their
;; region.
(define-effect kmakes (maxeff kreads (alloc @t)))
(define k-gen-map (subr (maxeff (read @globals) (alloc @t)) (k-binders k-descs) k-map)
  (lambda (bs ds)
    (if (null? bs)
        nil
        (the k-map (cons (cons (extract (car bs) 1) (car ds)) (k-gen-map (cdr bs) (cdr ds)))))))
(define k-subst-conv (subr kreads (k-conv k-map) k-conv)
  (lambda (c m)
    (tagcase c
      (cv-var (v)
        (let ((f (k-map-find m v)))
          (if (null? f) c (tagcase (cdr (car f)) (dc (x) x) (else y c)))))
      (else y c))))
(define k-subst-region (subr kreads (k-region k-map) k-region)
  (lambda (r m)
    (tagcase r
      (r-var (v)
        (let ((f (k-map-find m v)))
          (if (null? f) r (tagcase (cdr (car f)) (dr (x) x) (else y r)))))
      ;; Frozen data's place too.
      (r-frozen (p fin)
        (let ((f (if (< p 0) (the k-map nil) (k-map-find m p))))
          (if (null? f)
              r
              (tagcase (cdr (car f))
                (dr (x)
                  (tagcase x (r-var (q) (r-frozen q fin)) (r-heap () (r-frozen -1 fin)) (else z r)))
                (else y r)))))
      (else y r))))
;; Atom `a`, not a variable, substituted into: none if it reads, allocates
;; or awaits at data frozen into the heap, which is pure (`k-frozen`), so
;; that a region variable instantiated at `acyclic` or `const` leaves none.
(define k-subst-atom (subr (maxeff kmakes spin) (k-atom k-map) k-eff)
  (lambda (a m)
    (let* ((r (k-subst-region (k-atom-region a) m))
           (heap-frozen (tagcase r (r-frozen (p f) (< p 0)) (else y #f)))
           (pure-there (tagcase a (a-read (x) #t) (a-alloc (x) #t) (a-await (x) #t) (else y #f))))
      (if (and heap-frozen pure-there) nil (k-one (k-atom-with a r))))))
(define k-subst-effect (subr (maxeff kmakes spin) (k-eff k-map) k-eff)
  (lambda (e m)
    (if (null? e)
        nil
        (let* ((a (car e))
               (rest (k-subst-effect (cdr e) m))
               (piece (tagcase a
                        (a-var (v)
                          (let ((f (k-map-find m v)))
                            (if (null? f)
                                (k-one a)
                                (tagcase (cdr (car f)) (de (x) x) (else y (k-one a))))))
                        (a-app (v ds) (k-subst-eff-app v (k-subst-eargs ds m) m))
                        (else y (k-subst-atom a m)))))
          (k-union piece rest)))))
;; What an effect function is given, substituted into.
(define k-subst-eargs (subr (maxeff kmakes spin) (k-descs k-map) k-descs)
  (lambda (ds m)
    (if (null? ds)
        nil
        (let* ((d (tagcase (car ds)
                    (dr (r) (dr (k-subst-region r m)))
                    (de (e) (de (k-subst-effect e m)))
                    (dz (z) (dz (k-subst-size z m)))
                    (dc (c) (dc (k-subst-conv c m)))
                    (else y (car ds))))
               (rest (k-subst-eargs (cdr ds) m)))
          (the k-descs (cons d rest))))))
;; Effect function `v` applied to `ds`, given what `v` is substituted by:
;; reduced, if it is a `dlambda` now (`check-kinds.fx`).
(define k-subst-eff-app (subr (maxeff kmakes spin) (int k-descs k-map) k-eff)
  (lambda (v ds m)
    (let ((f (k-map-find m v)))
      (if (null? f)
          (k-one (a-app v ds))
          (tagcase (cdr (car f))
            (df (g)
              (tagcase (k-get g)
                (ty-var (w) (k-one (a-app w ds)))
                (ty-lam (bs body)
                  (tagcase body
                    (de (e)
                      (if (= (k-length bs) (k-length ds))
                          (k-subst-effect e (k-gen-map bs ds))
                          (k-one (a-app v ds))))
                    (else z (k-one (a-app v ds)))))
                (else z (k-one (a-app v ds)))))
            (else y (k-one (a-app v ds))))))))
;; What an application reduced gives as a type: a type, or else the
;; application `t` as it was.
(define k-applied-type (subr pure (k-desc int) int)
  (lambda (d t) (tagcase d (dt (x) x) (else y t))))
(define k-memo-find (subr kreads (k-pairs int) int)
  (lambda (ms t)
    (cond ((null? ms) -1)
          ((= (car (car ms)) t) (cdr (car ms)))
          (else (k-memo-find (cdr ms) t)))))
(define k-subst-memo (subr (maxeff kstate spin) (int k-map (ref k-pairs @t)) int)
  (lambda (t m memo)
    (let* ((t (k-resolve t))
           (kept (and (>= (get k-subst-keep) 0) (= (k-keep-at t) (get k-subst-keep))))
           (done (if kept t (k-memo-find (get memo) t))))
      (if (>= done 0)
          done
          (tagcase (k-get t)
            (ty-base (s) t)
            (ty-void () t)
            (ty-link (x) t)
            (ty-var (v)
              (let ((f (k-map-find m v)))
                (if (null? f) t (tagcase (cdr (car f)) (dt (x) x) (df (x) x) (else y t)))))
            (ty-select (mod n) (k-select-of mod n t))
            (ty-param (k n) (k-param-sel-of k n t))
            ;; A function applied, given what it is substituted by:
            ;; reduced, if it is a `dlambda` now (`check-kinds.fx`).
            (ty-app (g ds)
              (let ((slot (k-slot)))
                (begin
                  (set memo (cons (cons t slot) (get memo)))
                  (let* ((g2 (k-subst-memo g m memo)) (ds2 (k-subst-descs ds m memo)))
                    (begin (k-set-link slot (k-applied-type (k-apply-fun g2 ds2) t)) slot)))))
            (else y
              (let ((slot (k-slot)))
                (begin
                  (set memo (cons (cons t slot) (get memo)))
                  (let ((id (k-ty-new (k-subst-node t m memo))))
                    (begin (k-set-link slot id) slot))))))))))
;; Node `t`, of a type other than a variable, with its parts substituted.
(define k-subst-node (subr (maxeff kstate spin) (int k-map (ref k-pairs @t)) k-ty)
  (lambda (t m memo)
    (letrec ((sub (subr (maxeff kstate spin) (int) int)
                  (lambda (x) (k-subst-memo x m memo)))
             (subs (subr (maxeff kstate spin) (k-ids) k-ids)
                   (lambda (xs) (k-subst-list xs m memo)))
             (reg (subr kreads (k-region) k-region)
                  (lambda (r) (k-subst-region r m))))
      (tagcase (k-get t)
        (ty-subr (e ps r cv)
          (let* ((e2 (k-subst-effect e m)) (ps2 (subs ps)) (r2 (sub r)))
            (ty-subr e2 ps2 r2 (k-subst-conv cv m))))
        (ty-poly (bs body) (ty-poly bs (sub body)))
        (ty-ref (a r) (ty-ref (sub a) (reg r)))
        (ty-array (a r) (ty-array (sub a) (reg r)))
        (ty-icell (a r) (ty-icell (sub a) (reg r)))
        (ty-place (r) (ty-place (reg r)))
        (ty-pair (a b r) (let* ((a2 (sub a)) (b2 (sub b))) (ty-pair a2 b2 (reg r))))
        (ty-tag (a h e r)
          (let* ((a2 (sub a)) (h2 (sub h))) (ty-tag a2 h2 (k-subst-effect e m) (reg r))))
        (ty-comp (b a e r)
          (let* ((b2 (sub b)) (a2 (sub a))) (ty-comp b2 a2 (k-subst-effect e m) (reg r))))
        (ty-markkey (a r) (ty-markkey (sub a) (reg r)))
        (ty-product (ps) (ty-product (k-subst-parts ps m memo)))
        (ty-sum (ps) (ty-sum (k-subst-parts ps m memo)))
        (ty-bloblet (fs z r) (ty-bloblet (subs fs) z (reg r)))
        (ty-named (g ds) (ty-named g (k-subst-descs ds m memo)))
        (ty-lam (bs body) (ty-lam bs (car (k-subst-descs (the k-descs (cons body nil)) m memo))))
        (ty-nlist (e z r) (ty-nlist (sub e) (k-subst-size z m) (reg r)))
        (ty-nat (z) (ty-nat (k-subst-size z m)))
        (ty-module (abs ds vs)
          (let* ((ds2 (k-subst-parts ds m memo)) (vs2 (k-subst-parts vs m memo)))
            (ty-module abs ds2 vs2)))
        (else z (k-get t))))))
(define k-subst-descs (subr (maxeff kstate spin) (k-descs k-map (ref k-pairs @t)) k-descs)
  (lambda (ds m memo)
    (if (null? ds)
        nil
        (let* ((d (tagcase (car ds)
                    (dt (x) (dt (k-subst-memo x m memo)))
                    (dr (r) (dr (k-subst-region r m)))
                    (de (e) (de (k-subst-effect e m)))
                    (dz (z) (dz (k-subst-size z m)))
                    (dc (c) (dc (k-subst-conv c m)))
                    (df (x) (df (k-subst-memo x m memo)))))
               (rest (k-subst-descs (cdr ds) m memo)))
          (cons d rest)))))
(define k-subst-list (subr (maxeff kstate spin) (k-ids k-map (ref k-pairs @t)) k-ids)
  (lambda (ts m memo)
    (if (null? ts)
        nil
        (let* ((x (k-subst-memo (car ts) m memo)) (rest (k-subst-list (cdr ts) m memo)))
          (cons x rest)))))
(define k-subst-parts (subr (maxeff kstate spin) (k-parts k-map (ref k-pairs @t)) k-parts)
  (lambda (ps m memo)
    (if (null? ps)
        nil
        (let* ((x (k-subst-memo (extract (car ps) 2) m memo))
               (rest (k-subst-parts (cdr ps) m memo)))
          (cons (product (1 (extract (car ps) 1)) (2 x)) rest)))))
;; `t` with each binder in `m` replaced. Recursive types are copied as
;; cycles: each node gets its slot before its children are built.
;; A substitution of its own (a `dlambda` reduced inside another) keeps
;; nothing of another's.
(define k-subst (subr (maxeff kstate spin) (int k-map) int)
  (lambda (t m)
    (let* ((keep (get k-subst-keep))
           (off (set k-subst-keep -1))
           (r (k-subst-memo t m (the (ref k-pairs @t) (new nil)))))
      (begin (set k-subst-keep keep) r))))
;; The description of kind `k` that names binder `v`.
(define k-binder-desc (subr (maxeff kstate spin) (int int) k-desc)
  (lambda (k v)
    (case k ((0 3) (dr (r-var v)))
            ((1) (de (k-one (a-var v))))
            ((5) (dz (k-size-var v)))
            ((6) (dc (cv-var v)))
            (else
             (cond ((>= k 100) (df (k-ty-new (ty-var v))))
                   (else (dt (k-ty-new (ty-var v)))))))))
(define-rec
    ;; Description `d` substituted into.
    (k-subst-desc (subr (maxeff kstate spin) (k-desc k-map) k-desc)
      (lambda (d m)
        (car (k-subst-descs (the k-descs (cons d nil)) m (the (ref k-pairs @t) (new nil))))))
    ;; Function `f` applied to `ds`: what a `dlambda` reduces to, or an
    ;; application that cannot be reduced. `ds` fit `f`'s kind, which the
    ;; caller has made sure of.
    (k-apply-fun (subr (maxeff kstate spin) (int k-descs) k-desc)
      (lambda (f ds)
        (tagcase (k-get f)
          (ty-lam (bs body)
            (if (= (k-length bs) (k-length ds))
                (k-subst-desc body (k-gen-map bs ds))
                (k-apply-stuck f ds)))
          (else y (k-apply-stuck f ds))))))
;; `f` applied to `ds`, which cannot be reduced: an effect, an atom of its
;; own; a function; or a type.
(define k-apply-stuck (subr (maxeff kstate spin) (int k-descs) k-desc)
  (lambda (f ds)
    (let ((r (k-arrow-result (k-fun-kind f))))
      (cond ((= r 1)
             (tagcase (k-get f)
               (ty-var (v) (de (k-one (a-app v (k-eargs ds)))))
               (else y (de nil))))
            ((k-arrow-kind? r) (df (k-ty-new (ty-app f ds))))
            (else (dt (k-ty-new (ty-app f ds))))))))
;; What an effect function is given, of `ds`: no types.
(define k-eargs (subr (read @globals) (k-descs) k-descs)
  (lambda (ds)
    (cond ((null? ds) nil)
          ((tagcase (car ds) (dt (t) #t) (df (f) #t) (else y #f)) (k-eargs (cdr ds)))
          (else (the k-descs (cons (car ds) (k-eargs (cdr ds))))))))))

(define-type k-pairs (select check-subst-module k-pairs))
(define-type exp-params (select check-subst-module exp-params))
(define-effect kmakes (select check-subst-module kmakes))
(define k-gen-map (with check-subst-module k-gen-map))
(define k-subst-region (with check-subst-module k-subst-region))
(define k-memo-find (with check-subst-module k-memo-find))
(define k-subst-memo (with check-subst-module k-subst-memo))
(define k-subst-descs (with check-subst-module k-subst-descs))
(define k-subst (with check-subst-module k-subst))
(define k-binder-desc (with check-subst-module k-binder-desc))
(define k-apply-fun (with check-subst-module k-apply-fun))
(define k-subst-desc (with check-subst-module k-subst-desc))
