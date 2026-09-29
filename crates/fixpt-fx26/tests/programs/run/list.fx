;;; `list`: a fresh list of its arguments, `(listof T acyclic)`; as a value,
;;; a `vsubr`, which `apply` spreads a list over.
(define* total (subr spin ((listof int acyclic)) int)
  (lambda (xs) (if (null? xs) 0 (+ (car xs) (total (cdr xs))))))
(define make (vsubr pure int (listof int acyclic)) list)
(define spread (subr (read @heap) ((listof int @heap)) (listof int acyclic))
  (lambda (xs) (apply list xs)))
(define words (listof string acyclic) (list "a" "b"))
(+ (* 100 (total (list 1 2 3 4 5 6 7 8 9 10)))
   ;; cons-chain: apply over a list in @heap
   (+ (* 10 (total (make 1 2))) (+ (total (list)) (total (spread (cons 4 (cons 5 nil)))))))
