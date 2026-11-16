;; ! inferred: (macro (_ . (oneof (() expr) (((data data) data ...) data))) expr)
;; A refused signature inferred, shown in shapes and facts: the operands one of two shapes.
(define-syntax my-let*
  (syntax-rules
    ((_ () body) body)
    ((_ ((x e) rest ...) body) (let ((x e)) (list body (my-let* (rest ...) body))))))
(my-let* ((a 1) (b 2)) 3)
