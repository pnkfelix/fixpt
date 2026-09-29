;;; Variadic procedures, FX-87's: `(vsubr E T R)`, made by `vlambda`, which
;;; binds the list of the arguments, called with any number of `T`s, and
;;; by `apply` on a list.
(define* total (subr spin ((listof int acyclic)) int)
  (lambda (xs) (if (null? xs) 0 (+ (car xs) (total (cdr xs))))))
(define add-up (vsubr (maxeff spin (read (globals total))) int int) (vlambda xs (total xs)))
(define first-or-none (vsubr pure string string)
  (vlambda (ss string) (if (null? ss) "none" (car ss))))
;; cons-chain: apply over a list in @heap
(let ((five-six (the (listof int @heap) (cons 5 (cons 6 nil)))))
  (+ (* 100 (add-up 1 2 3 4)) (+ (add-up) (apply add-up five-six))))
