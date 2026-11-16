;; => 3
;; As `rec-alternating.fx`, `bnd`'s signature inferred.
(define-syntax-rec
  (bnd (syntax-rules
         ((_ () body) body)
         ((_ ((x e) . rest) body) (let ((x e)) (seq rest body)))))
  (seq (macro ((mu s (oneof (export () (cage))
                           (export (expr . (oneof (export () (cage))
                                                  (export ((bvar expr) . (import s (rho (AA var))))
                                                          (cage (at D) (rho (AA var))))))
                                   (cage (at D)))))
               (import expr (cage (at A))))
              expr)
       (syntax-rules
         ((_ () body) body)
         ((_ (e . rest) body) (begin e (bnd rest body))))))
(bnd ((a 1) (+ a 0) (b (+ a 1)) (+ b 0)) (+ a b))
