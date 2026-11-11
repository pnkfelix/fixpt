;; => 4
;; A module inside named with its own `modnames`, all its names: `z` left
;; out of the one outside.
(define outer
  (module (define inner (module (define a int 1) (define b int 2))) (define y int 3)
          (define z int 4)))
(define s (modnames (modnames inner a b) y) outer)
(+ (with s y) (let ((i (with s inner))) (with i a)))
