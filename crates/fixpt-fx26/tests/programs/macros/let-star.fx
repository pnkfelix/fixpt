;; => 7
;; `let*` as a macro, by recursion through its syntax type (Herman's
;; let*-cl): each clause's expression sees those before it.
(define-syntax my-let*
  ;; As named: (union nil (exports ((x bvar) (e expr) (cs (in clauses x))) (cage cs x)))
  ;; for the clauses, and the body in their scope: (body (in expr cs)).
  ((mu c (union (export () (cage))
                (export ((bvar expr) . (import c (rho (AA var))))
                        (cage (at D) (rho (AA var))))))
   (import expr (cage (at A))))
  (syntax-rules ()
    ((_ () body) body)
    ((_ ((x e) . rest) body) (let ((x e)) (my-let* rest body)))))
(my-let* ((a 1) (b (+ a 1)) (c (+ a (+ b 1)))) (+ a (+ b c)))
