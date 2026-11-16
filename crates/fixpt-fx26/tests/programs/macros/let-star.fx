;; => 7
;; `let*` as a macro, by recursion through its syntax type (Herman's
;; let*-cl): each clause's expression sees those before it.
(define-syntax my-let*
  (macro (letrec-shape ((clauses
                          (union (end ())
                                 (clause ((x @ bvar e @ expr) rest @ . clauses)
                                   (bind x in rest)
                                   (export* x rest)))))
           (_ cs @ clauses body @ expr))
         expr
    (bind cs in body))
  (syntax-rules
    ((_ () body) body)
    ((_ ((x e) . rest) body) (let ((x e)) (my-let* rest body)))))
(my-let* ((a 1) (b (+ a 1)) (c (+ a (+ b 1)))) (+ a (+ b c)))
