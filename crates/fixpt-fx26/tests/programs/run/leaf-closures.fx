;;; A procedure that only makes a closure, as its value, is a leaf: no
;;; frame; where the free space has no room, its slow path makes a frame of
;;; its own around the call-out. Many made, so collections come.
(define* adder (subr pure (int) (subr pure (int) int)) (lambda (y) (lambda ((x int)) (+ y x))))
(define* go (subr spin (int int) int)
  (lambda (i acc) (if (= i 0) acc (go (- i 1) (+ acc ((adder i) 1))))))
(go 3000 0)
