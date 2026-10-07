;; => (1)
;; Recursion through a constructor, `pairof` (with `nil`: a list), and a
;; type function's application: a type for any function, the identity too.
(define-type (fix2 (f (=> (type) type))) (union nil (pairof int (f (fix2 f)) @heap)))
(the (fix2 (dlambda ((t type)) t)) (cons 1 nil))
