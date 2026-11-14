;; => 3
;; Even and odd: two macros that hand a list back and forth, its elements
;; binders and expressions in turn, each in the scope of the binders before
;; it; whether an element binds said by which macro holds it, not by its
;; shape (`typed-macros.md`, "Rejected: a signature per clause").
(define-syntax-rec
  (bnd (syntax-rules ()
         ((_ () body) body)
         ((_ ((x e) . rest) body) (let ((x e)) (seq rest body)))))
  (seq (syntax-rules ()
         ((_ () body) body)
         ((_ (e . rest) body) (begin e (bnd rest body))))))
(bnd ((a 1) (+ a 0) (b (+ a 1)) (+ b 0)) (+ a b))
