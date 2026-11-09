;; => 2
;; Recursion over what an ellipsis gives: `or` of any number of parts.
(define-syntax my-or
  (expr ...)
  (syntax-rules ()
    ((_) #f)
    ((_ e) e)
    ((_ e r ...) (let ((t e)) (if (= t 0) (my-or r ...) t)))))
(my-or 0 2 3)
