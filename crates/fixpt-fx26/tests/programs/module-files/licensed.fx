;; A module file of a region parameter whose entry point touches only that
;; region: licensed whichever region it is given (`licence.rs`).
(module-parameters ((r region)))
(define count (ref int r) (new 0))
(define feed (subr (maxeff (read r) (write r)) (int) int)
  (lambda (n) (begin (set count (+ (get count) n)) (get count))))
