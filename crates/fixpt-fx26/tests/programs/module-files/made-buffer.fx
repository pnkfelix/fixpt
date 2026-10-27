;; A function of a scheduler (`made-core.fx`) to the module it makes, the
;; scheduler's type the module that file makes (`load-moduleof`).
(plambda ((ed region) (world effect))
  (lambda ((core (load-moduleof "made-core.fx" ed world)))
    (module
      (define-type buffer (productof (owner (select core counter)) (t (select core ticket))))
      (define make (subr (maxeff (alloc ed) (read ed) (write ed)) (int) buffer)
        (lambda (n) (product (owner ((with core spawn) n)) (t ((with core issue))))))
      (define size (subr (read ed) (buffer) int)
        (lambda (b) ((with core peek) (extract b owner)))))))
