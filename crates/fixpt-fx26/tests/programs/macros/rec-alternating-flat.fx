;; ! `rest` is placed where its syntax type is not one the form takes there
;; The list's binders said one rib, `(rho (AA var) (D rib))`: but each is in
;; the scope of what comes after it, which may bind its name again, a
;; ribcage (`rec-alternating.fx`), as `seq`'s signature, inferred, says.
(define-syntax-rec
  (bnd (macro ((mu b (oneof (export () (rho))
                           (export ((bvar expr)
                                    . (import (oneof (export () (rho))
                                                     (export (expr . b) (rho (D rib))))
                                              (rho (AA var))))
                                   (rho (AA var) (D rib)))))
               (import expr (rho (A rib))))
              expr)
       (syntax-rules
         ((_ () body) body)
         ((_ ((x e) . rest) body) (let ((x e)) (seq rest body)))))
  (seq (syntax-rules
         ((_ () body) body)
         ((_ (e . rest) body) (begin e (bnd rest body))))))
