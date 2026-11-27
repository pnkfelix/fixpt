;; => 3
;; Three levels, labelled at each: groups of rows of labelled cells; each
;; group bound to its count of rows.
(define-syntax rows3
  (macro (_ ((g @ bvar (r @ bvar c @ expr ...) ...) ...) body @ expr) expr
    (bind (g ...) in body))
  (syntax-rules
    ((_ ((g (r c ...) ...) ...) body)
     (let ((g (length (list (list c ...) ...))) ...)
       body))))
(rows3 ((x (p 1 2) (q 3)) (y (s 4 5 6))) (+ x y))
