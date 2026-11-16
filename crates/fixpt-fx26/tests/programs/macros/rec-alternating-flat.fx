;; ! `rest` is placed where its syntax type is not one the form takes there
;; The list's binders said one rib, `(rho (AA var) (D rib))`: but each is in
;; the scope of what comes after it, which may bind its name again, a
;; ribcage (`rec-alternating.fx`), as `seq`'s signature, inferred, says.
(define-syntax-rec
  (bnd (macro (letrec-shape ((binds (union (end ())
                                          (bnd ((x @ bvar e @ expr) rest @ . exprs)
                                            (bind x in rest)
                                            (export x rest))))
                             (exprs (union (end ())
                                           (seq (expr rest @ . binds) (export rest)))))
                (_ cs @ binds body @ expr))
              expr
         (bind cs in body))
       (syntax-rules
         ((_ () body) body)
         ((_ ((x e) . rest) body) (let ((x e)) (seq rest body)))))
  (seq (syntax-rules
         ((_ () body) body)
         ((_ (e . rest) body) (begin e (bnd rest body))))))
