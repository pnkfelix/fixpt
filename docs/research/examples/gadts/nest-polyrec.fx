;;; FX-26 today: a nested (non-regular) datatype, and polymorphic recursion
;;; over it. `(nest a)` holds an `a`, then a `(nest (pair a a))`: 1, 2, 4, …
;;; elements. It must be generative (N1): its structure never closes into
;;; a cycle. `count` calls itself at a different type, `(productof (l a) (r
;;; a))`, which its declared `poly` signature allows, as a signature does in
;;; Haskell; a GADT `eval` needs the same.
;;;   data Nest a = None | More a (Nest (a, a))
;;;   count :: (a -> Int) -> Nest a -> Int
(define-type (pair (a type)) (productof (l a) (r a)))
(define-generative (nest (a type))
  (sumof (none unit) (more (productof (hd a) (tl (nest (pair a)))))))
(define* count (poly ((a type)) (subr spin ((subr pure (a) int) (nest a)) int))
  (lambda (f n)
    (tagcase (down-nest n)
      (none u 0)
      (more (hd tl)
        (+ (f hd)
           (count (lambda ((p (pair a))) (+ (f (extract p l)) (f (extract p r))))
                  tl))))))
(define empty (nest (pair (pair int))) (up-nest (sum none #u)))
(define n2 (nest (pair int)) (up-nest (sum more (product (hd (product (l 2) (r 3))) (tl empty)))))
(define n3 (nest int) (up-nest (sum more (product (hd 1) (tl n2)))))
(count (lambda ((x int)) 1) n3)
