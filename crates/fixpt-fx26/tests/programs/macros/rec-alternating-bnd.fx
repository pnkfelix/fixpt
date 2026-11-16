;; => 3
;; As `rec-alternating.fx`, `seq`'s signature inferred.
(define-syntax-rec
  (bnd (macro ((mu b (oneof (export () (cage))
                           (export ((bvar expr)
                                    . (import (oneof (export () (cage))
                                                     (export (expr . b) (cage (at D))))
                                              (rho (AA var))))
                                   (cage (at D) (rho (AA var))))))
               (import expr (cage (at A))))
              expr)
       (syntax-rules
         ((_ () body) body)
         ((_ ((x e) . rest) body) (let ((x e)) (seq rest body)))))
  (seq (syntax-rules
         ((_ () body) body)
         ((_ (e . rest) body) (begin e (bnd rest body))))))
(bnd ((a 1) (+ a 0) (b (+ a 1)) (+ b 0)) (+ a b))
