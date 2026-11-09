;; => 7
;; `define-syntax-rec`: macros that use each other, their signatures
;; inferred together; `my-let*`'s scopes through `step`'s.
(define-syntax-rec
  (my-let* (syntax-rules ()
             ((_ () body) body)
             ((_ ((x e) . rest) body) (let ((x e)) (step rest body)))))
  (step (syntax-rules ()
          ((_ cs body) (my-let* cs body)))))
(my-let* ((a 1) (b (+ a 1)) (c (+ a (+ b 1)))) (+ a (+ b c)))
