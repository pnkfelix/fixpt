;;; A type representation that is a dictionary of operations, built from
;;; combinators (Hinze's "Generics for the masses"; MLton's Generic):
;;; one rep-pair serves every product, one rep-sum every sum.
(define-effect walk (maxeff spin (read @globals)))
(define-type (rep (t type))
  (productof (eq (subr walk (t t) bool)) (show (subr walk (t) datum)) (size (subr walk (t) int))))
(define rep-int (rep int)
  (product (eq (lambda (x y) (= x y))) (show (lambda (x) (datum-int x))) (size (lambda (x) 1))))
;; (a b) as a datum list.
(define d2 (subr pure (datum datum) datum)
  (lambda (a b) (datum-cons a (datum-cons b (datum-list (the (listof datum @l) nil))))))
(define rep-pair
  (poly ((a type) (b type)) (subr pure ((rep a) (rep b)) (rep (productof (1 a) (2 b)))))
  (lambda (ra rb)
    (product
     (eq (lambda (x y) (and ((extract ra eq) (extract x 1) (extract y 1))
                            ((extract rb eq) (extract x 2) (extract y 2)))))
     (show (lambda (x) (d2 ((extract ra show) (extract x 1)) ((extract rb show) (extract x 2)))))
     (size (lambda (x) (+ ((extract ra size) (extract x 1)) ((extract rb size) (extract x 2))))))))
(define rep-sum
  (poly ((a type) (b type)) (subr pure ((rep a) (rep b)) (rep (sumof (inl a) (inr b)))))
  (lambda (ra rb)
    (product
     (eq (lambda (x y)
           (tagcase x
             (inl u (tagcase y (inl v ((extract ra eq) u v)) (inr v #f)))
             (inr u (tagcase y (inl v #f) (inr v ((extract rb eq) u v)))))))
     (show (lambda (x) (tagcase x (inl u ((extract ra show) u)) (inr u ((extract rb show) u)))))
     (size (lambda (x) (tagcase x (inl u ((extract ra size) u)) (inr u ((extract rb size) u))))))))
;; A constructor's name, for show (GHC.Generics' M1 metadata).
(define rep-con
  (poly ((a type)) (subr pure (symbol (rep a)) (rep a)))
  (lambda (name ra)
    (product (eq (extract ra eq))
             (show (lambda (x) (d2 (datum-symbol (symbol->string name)) ((extract ra show) x))))
             (size (extract ra size)))))
;; A user type enters through a conversion into the generic view: the
;; `from` half of an embedding-projection pair (Cheney and Hinze).
(define rep-iso
  (poly ((a type) (b type)) (subr pure ((subr pure (a) b) (rep b)) (rep a)))
  (lambda (from rb)
    (product (eq (lambda (x y) ((extract rb eq) (from x) (from y))))
             (show (lambda (x) ((extract rb show) (from x))))
             (size (lambda (x) ((extract rb size) (from x)))))))
;; Recursion (MLton's Y): a rep that asks for itself only when used.
(define rep-delay
  (poly ((a type)) (subr pure ((subr walk () (rep a))) (rep a)))
  (lambda (get)
    (product (eq (lambda (x y) ((extract (get) eq) x y)))
             (show (lambda (x) ((extract (get) show) x)))
             (size (lambda (x) ((extract (get) size) x))))))

(define-datatype tree (leaf int) (node tree tree))
(define tree-view
  (subr pure (tree) (sumof (inl int) (inr (productof (1 tree) (2 tree)))))
  (lambda (t) (tagcase t (leaf (n) (sum inl n))
                         (node (l r) (sum inr (product (1 l) (2 r)))))))
(define rep-tree (subr walk () (rep tree))
  (lambda ()
    (rep-iso tree-view
             (rep-sum (rep-con 'leaf rep-int)
                      (rep-con 'node (rep-pair (rep-delay rep-tree) (rep-delay rep-tree)))))))

;; The generic operations: take the rep, then the value.
(define t1 tree (node (leaf 1) (node (leaf 2) (leaf 3))))
((extract (rep-tree) eq) t1 t1)
((extract (rep-tree) show) t1)
((extract (rep-tree) size) t1)
;; The same combinators, at a type with no declaration at all.
((extract (rep-pair rep-int (rep-sum rep-int rep-int)) show)
 (product (1 7) (2 (sum inr 8))))
