;; => 3
;; Two macros of one list, its binders and expressions alternating, each
;; macro's signature the list from its own end (`bnd`'s a binder first,
;; `seq`'s an expression): each binder in the scope of what comes after it,
;; which may bind its name again, so the list exports a ribcage (TODO §272:
;; a signature written with one rib was refused, rightly).
(define-syntax-rec
  (bnd (macro (letrec-shape ((binds (union (end ())
                                          (bnd ((x @ bvar e @ expr) rest @ . exprs)
                                            (bind x in rest)
                                            (export* x rest))))
                             (exprs (union (end ())
                                           (seq (expr rest @ . binds) (export* rest)))))
                (_ cs @ binds body @ expr))
              expr
         (bind cs in body))
       (syntax-rules
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
