;;; FX-26 today: a "functor-like" `map` over more than one container shape,
;;; without a kind `type -> type`. `box` is a *closed* union of two shapes
;;; (an option and a pair), each carrying one `a`; `map-box` is written once,
;;; by `tagcase`, and works on either shape. This is not open the way a real
;;; `Functor` class is -- adding a third shape means editing `box` and
;;; `map-box` together, not writing an independent instance elsewhere -- but
;;; it needs no new kind, no type-level application, and no inference beyond
;;; what FX-26 already does. See docs/research/higher-kinds.md, "A lighter
;;; interim", for the limits of this pattern.
(define-type (maybe (a type)) (sumof (none unit) (some a)))
(define-type (pair (a type)) (productof (fst a) (snd a)))
(define-type (box (a type)) (sumof (as-maybe (maybe a)) (as-pair (pair a))))

(define map-box
  (poly ((a type) (b type))
    (subr pure ((subr pure (a) b) (box a)) (box b)))
  (lambda (f bx)
    (tagcase bx
      (as-maybe m
        (sum as-maybe
          (tagcase m
            (none u (sum none u))
            (some x (sum some (f x))))))
      (as-pair p
        (sum as-pair
          (product (fst (f (extract p fst))) (snd (f (extract p snd)))))))))

(define b1 (box int) (sum as-maybe (sum some 5)))
(define b2 (box int) (sum as-pair (product (fst 1) (snd 2))))
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(define r1 (box int) (map-box inc b1))
(define r2 (box int) (map-box inc b2))
r2
