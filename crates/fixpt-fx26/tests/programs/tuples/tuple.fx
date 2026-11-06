;; => ("1" "a" "aa")
;; `(tupleof T …)` is `(productof (1 T) …)`, `(tuple e …)` `(product (1 e) …)`.
(define-type pt (tupleof int string))
(define p pt (tuple 1 "a"))
(define q (productof (1 int) (2 string)) p)
(list (int->string (extract q 1)) (extract p 2)
      (tagcase (sum #:pt p) (#:pt (n s) (string-append s s))))
