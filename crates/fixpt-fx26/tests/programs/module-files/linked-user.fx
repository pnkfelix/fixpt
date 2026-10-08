;; A module made of the module it uses, typed by its signature: `make`. Its
;; first items name what it uses, `(define cat3 (with dep cat3))`: the
;; `with` binds `dep`'s `cat3`, not this one (`TODO.md` §68).
(define sigs (load-module "linked-sigs.fx"))
(define-type dep-sig (select sigs dep-sig))
(define make
  (lambda ((dep dep-sig))
    (module
      (define cat3 (with dep cat3))
      (define* twice (subr spin (int) int) (lambda (n) (if (< n 1) 0 (+ 2 (twice (- n 1))))))
      (define shout (subr pure (string) string) (lambda (s) (cat3 s "!" "")))
      (define v int (twice (with dep limit))))))
