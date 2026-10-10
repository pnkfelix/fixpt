;; => 15
;; `with` shadows description functions applied too: in `(with m …)`,
;; `(f d …)` for an `f` `m` gives is `m`'s; one `m` does not give is what it
;; is outside, each application its own; and the innermost `with`'s first.
(define-type (two (a type)) (productof (1 a) (2 a)))
(define-type (box (a type)) (productof (1 a)))
(define m (module (define-type (two (a type)) (productof (1 a) (2 a) (3 a)))
                  (define-type (one (a type)) (productof (1 a)))))
(define k (module (define-type (two (a type)) (productof (1 bool) (2 a)))))
(define p (with m (the (two int) (product (1 1) (2 2) (3 3)))))
(define q (with m (the (pairof (box int) (box bool) heap) (cons (product (1 1)) (product (1 #t))))))
(define r (with m (with k (the (two int) (product (1 #t) (2 1))))))
(define s (with m (the (one int) (product (1 8)))))
(+ (+ (extract p 3) (extract s 1))
   (+ (extract (car q) 1) (if (extract (cdr q) 1) (+ (extract r 2) 2) 0)))
