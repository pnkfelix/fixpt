;;; One generic value type for every datatype: a sum-of-products view as
;;; data, as GHC.Generics' U1, K1, M1, :+: and :*:, but untyped. Each type
;;; gives only its `from` (what `deriving Generic` writes); geq, gsize and
;;; gshow are written once, over gv, and every walk of gv is pure.
(define-datatype gv (g-unit) (g-int int) (g-con symbol gv) (g-inl gv) (g-inr gv) (g-pair gv gv))
;; What building a gv reads: its constructors, which are globals.
(define-effect mk-gv (read (globals g-int g-con g-inl g-inr g-pair)))
(define geq (subr pure (gv gv) bool)
  (letrec ((geq (subr pure (gv gv) bool)
             (lambda (x y)
               (tagcase x
                 (g-unit () (tagcase y (g-unit () #t) (else _ #f)))
                 (g-int (n) (tagcase y (g-int (m) (= n m)) (else _ #f)))
                 (g-con (c u) (tagcase y (g-con (d v) (and (symbol=? c d) (geq u v))) (else _ #f)))
                 (g-inl (u) (tagcase y (g-inl (v) (geq u v)) (else _ #f)))
                 (g-inr (u) (tagcase y (g-inr (v) (geq u v)) (else _ #f)))
                 (g-pair (u1 u2) (tagcase y (g-pair (v1 v2) (and (geq u1 v1) (geq u2 v2))) (else _ #f)))))))
    geq))
(define gsize (subr pure (gv) int)            ; the number of ints
  (letrec ((gsize (subr pure (gv) int)
             (lambda (x)
               (tagcase x
                 (g-unit () 0) (g-int (n) 1) (g-con (c u) (gsize u))
                 (g-inl (u) (gsize u)) (g-inr (u) (gsize u))
                 (g-pair (u v) (+ (gsize u) (gsize v)))))))
    gsize))
;; SYB's everywhere (mkT f): apply f at every int, whatever the type.
(define gmap-int (subr mk-gv ((subr pure (int) int) gv) gv)
  (lambda (f x)
    (letrec ((go (subr mk-gv (gv) gv)
               (lambda (x)
                 (tagcase x
                   (g-unit () x) (g-int (n) (g-int (f n))) (g-con (c u) (g-con c (go u)))
                   (g-inl (u) (g-inl (go u))) (g-inr (u) (g-inr (go u)))
                   (g-pair (u v) (g-pair (go u) (go v)))))))
      (go x))))

;; Per type: the conversions. `from` is total; `to` is not, since gv
;; does not say which type it came from, so it must answer something.
(define-datatype tree (leaf int) (node tree tree))
(define tree->gv (subr mk-gv (tree) gv)
  (letrec ((from (subr mk-gv (tree) gv)
             (lambda (t)
               (tagcase t
                 (leaf (n) (g-inl (g-con 'leaf (g-int n))))
                 (node (l r) (g-inr (g-con 'node (g-pair (from l) (from r)))))))))
    from))
(define gv->tree (subr (read (globals leaf node)) (gv) tree)
  (letrec ((to (subr (read (globals leaf node)) (gv) tree)
             (lambda (x)
               (tagcase x
                 (g-inl (u) (tagcase u (g-con (c v) (tagcase v (g-int (n) (leaf n)) (else _ (leaf 0))))
                                       (else _ (leaf 0))))
                 (g-inr (u) (tagcase u (g-con (c v) (tagcase v (g-pair (l r) (node (to l) (to r)))
                                                             (else _ (leaf 0))))
                                       (else _ (leaf 0))))
                 (else _ (leaf 0))))))          ; not a tree's view: invent one
    to))

(define t1 tree (node (leaf 1) (node (leaf 2) (leaf 3))))
(geq (tree->gv t1) (tree->gv t1))
(gsize (tree->gv t1))
(gv->tree (gmap-int (lambda (n) (* n 10)) (tree->gv t1)))  ; a tree again
(geq (gmap-int (lambda (n) (* n 10)) (tree->gv t1))
     (tree->gv (node (leaf 10) (node (leaf 20) (leaf 30)))))
