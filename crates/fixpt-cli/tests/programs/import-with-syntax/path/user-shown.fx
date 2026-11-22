;; The same, not in a `hide`: refused, as no importer of this file sees its
;; parameter.
(module-parameters ((env (load-moduleof "env.fx"))))
(import-with-syntax env::m-lib (only make-thing))
(define one (make-thing (product (n 1))))
