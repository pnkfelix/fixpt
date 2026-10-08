;; Datatypes mentioning a type selected from a module made in this one, at
;; its region: shown by their names, as a global module's would be.
(module-parameters ((r region)))
(define a ((proj (load-module "names-inner.fx") r)))
(define-type s (select a s))
(define-datatype e (ev s) (eapp e e))
(define-datatype t (td e) (tx int))
