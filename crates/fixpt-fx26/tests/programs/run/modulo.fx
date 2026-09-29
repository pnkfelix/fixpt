;;; `modulo` of every combination of signs, and of multiples: the result
;;; takes the divisor's sign, as Scheme's does (register code does it in
;;; machine code, and must agree).
(define mods (subr pure (int int) (listof int acyclic))
  (lambda (a b)
    (let ((-a (- 0 a))
          (-b (- 0 b)))
      (list (modulo a b) (modulo -a b) (modulo a -b) (modulo -a -b)))))

(list (mods 7 3) (mods 6 3) (mods 1 5) (mods 0 4))
