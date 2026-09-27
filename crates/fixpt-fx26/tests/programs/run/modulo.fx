;;; `modulo` of every combination of signs, and of multiples: the result
;;; takes the divisor's sign, as Scheme's does (register code does it in
;;; machine code, and must agree).
(define mods (subr (alloc @l) (int int) (listof int @l))
  (lambda (a b)
    (the (listof int @l)
      (cons (modulo a b) (cons (modulo (- 0 a) b) (cons (modulo a (- 0 b)) (cons (modulo (- 0 a) (- 0 b)) nil)))))))

(the (listof (listof int @l) @l) (cons (mods 7 3) (cons (mods 6 3) (cons (mods 1 5) (cons (mods 0 4) nil)))))
