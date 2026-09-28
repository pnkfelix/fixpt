;;; A generative type over a convention: its arguments are compared as they
;;; are, and no conversion is inserted inside one.
(define-generative (handler (c conv)) (subr (conv c) pure (int) int))
(define h (handler fx) (up-handler (convention fx (lambda ((x int)) (+ x 1)))))
((down-handler h) 3)
(define k (handler cellular) h)
