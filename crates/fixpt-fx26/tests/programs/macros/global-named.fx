;; ! a template may name the program's own globals only once
(define helper 3)
(define-syntax use-helper
  ()
  ((_) helper))
