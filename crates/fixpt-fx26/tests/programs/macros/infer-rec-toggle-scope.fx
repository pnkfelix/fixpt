;; ! unbound variable `b`
;; An expression of the list is not in the scope of the binders after it.
(define-syntax-rec
  (bnd (syntax-rules ()
         ((_ () body) body)
         ((_ ((x e) . rest) body) (let ((x e)) (seq rest body)))))
  (seq (syntax-rules ()
         ((_ () body) body)
         ((_ (e . rest) body) (begin e (bnd rest body))))))
(bnd ((a 1) b (b 2) 0) b)
