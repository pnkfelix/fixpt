;;; A non-regular lemma: its proof passes itself a coercion for pairs, a
;;; lambda whose parameter says its type.
(define-generative (nest (a type)) (sumof (none unit) (more (productof (hd a) (tl (nest (productof (l a) (r a))))))))
(define* nest-up (proves (poly ((a type) (b type)) (<= (nest a) (nest b)) (<= a b)))
  (lambda (f n)
    (up-nest (tagcase (down-nest n)
               (none u (sum none u))
               (more (hd tl) (sum more (product (hd (f hd))
                                                (tl (nest-up (lambda ((p (productof (l a) (r a)))) (product (l (f (extract p l))) (r (f (extract p r)))))
                                                             tl)))))))))
(define small (nest (sumof (x int))) (up-nest (sum none #u)))
(define wide (nest (sumof (x int) (y bool))) small)
