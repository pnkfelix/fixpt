;; => 3
;; Two macros of one list, its binders and expressions alternating, each
;; macro's signature the list from its own end (`bnd`'s a binder first,
;; `seq`'s an expression): each binder in the scope of what comes after it,
;; which may bind its name again, so the list exports a ribcage (TODO §272:
;; a signature written with one rib was refused, rightly).
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
