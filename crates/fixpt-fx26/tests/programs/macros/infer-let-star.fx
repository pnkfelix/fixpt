;; => 7
;; `let*` by recursion, its signature inferred: the clauses a `mu` of the
;; patterns' two shapes, each clause's expression in the scope of those
;; before it, the body in the ribcage they export (Herman's let*-cl).
(define-syntax my-let*
  (syntax-rules ()
    ((_ () body) body)
    ((_ ((x e) . rest) body) (let ((x e)) (my-let* rest body)))))
(my-let* ((a 1) (b (+ a 1)) (c (+ a (+ b 1)))) (+ a (+ b c)))
