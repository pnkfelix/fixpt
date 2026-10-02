;; => 2
;; Several abstract types at once; a description naming them.
(define pair
  (module
    (define-generative a int)
    (define-generative b int)
    (define-type both (productof (x a) (y b)))
    (define make both (product (x (up-a 1)) (y (up-b 1))))
    (define total (subr pure (both) int)
      (lambda (p) (+ (down-a (extract p x)) (down-b (extract p y)))))))
(define-type pairs
  (moduleof (abs (a b) type) (desc both (productof (x a) (y b)))
            (val make both) (val total (subr pure (both) int))))
(define use (subr pure (pairs) int) (lambda (m) (with m (total make))))
(use pair)
