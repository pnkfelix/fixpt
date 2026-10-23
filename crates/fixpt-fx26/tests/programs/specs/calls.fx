; Verified
;;; The call rule: what `abs` ensures is assumed after each call, so the
;;; sum is no less than 0; `clamp`'s `requires` is proved where it is
;;; called, and its `ensures` assumed after (`above`), or, called in tail
;;; position, entails the caller's (`bounded`).
(define abs (subr pure ((x int)) int (ensures r (<= 0 r)))
  (lambda (x) (if (< x 0) (- 0 x) x)))
(define clamp (subr pure ((lo int) (hi int) (x int)) int
                (requires (<= lo hi))
                (ensures r (and (<= lo r) (<= r hi))))
  (lambda (lo hi x) (if (< x lo) lo (if (< hi x) hi x))))
(define both (subr (read (globals abs)) ((x int) (y int)) int (ensures r (<= 0 r)))
  (lambda (x y) (+ (abs x) (abs y))))
(define bounded (subr (read (globals clamp)) ((x int)) int (ensures r (and (<= 0 r) (<= r 100))))
  (lambda (x) (clamp 0 100 x)))
(define above (subr (read (globals clamp)) ((x int)) int (ensures r (and (<= 1 r) (<= r 101))))
  (lambda (x) (+ 1 (clamp 0 100 x))))
(+ (bounded 7) (above (both -3 4)))
