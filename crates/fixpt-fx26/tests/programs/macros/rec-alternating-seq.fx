;; => 3
;; As `rec-alternating.fx`, `bnd`'s signature inferred.
(define-syntax-rec
  (bnd (syntax-rules
         ((_ () body) body)
         ((_ ((x e) . rest) body) (let ((x e)) (seq rest body)))))
  (seq (macro (letrec-shape ((binds (union (end ())
                                          (bnd ((x @ bvar e @ expr) rest @ . exprs)
                                            (bind x in rest)
                                            (export* x rest))))
                             (exprs (union (end ())
                                           (seq (expr rest @ . binds) (export* rest)))))
                (_ cs @ exprs body @ expr))
              expr
         (bind cs in body))
       (syntax-rules
         ((_ () body) body)
         ((_ (e . rest) body) (begin e (bnd rest body))))))
(bnd ((a 1) (+ a 0) (b (+ a 1)) (+ b 0)) (+ a b))
