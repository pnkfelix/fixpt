;; The same, not in a `hide`: refused, as no importer of this file sees its
;; parameter.
(module-parameters
  ((m-base (load-moduleof "base.fx") #:unqualified)
   (m-lib (load-moduleof "lib.fx" m-base) #:unqualified)))
(import-with-syntax m-lib (only make-thing))
(define one (make-thing (product (n 1))))
