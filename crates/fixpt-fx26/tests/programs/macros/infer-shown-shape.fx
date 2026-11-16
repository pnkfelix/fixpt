;; ! (letrec-shape ((m1 (union (end ()) (more ((p1 @ bvar expr) p2 @ . m1) (bind p1 in p2)))))
;; A refused signature inferred, shown in shapes and facts: a `mu` a `letrec-shape`'s shape, its
;; union's members `end` and `more`, its labels `p1`, `p2`, the pattern not saying them there.
(define-syntax my-let*
  (syntax-rules
    ((_ () body) body)
    ((_ ((x e) . rest) body) (list body (let ((x e)) (my-let* rest body))))))
(my-let* ((a 1) (b 2)) 3)
