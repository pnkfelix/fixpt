;; => 2
;; A module made over a region (the front end's `@k`, as a parameter): a
;; region-polymorphic procedure that makes it, its state in that region.
(define-type cells
  (poly ((k region))
    (subr (alloc k) ()
      (moduleof (val read-it (subr (read k) () int))
                (val bump (subr (maxeff (read k) (write k)) () unit))))))
(define make-cell cells
  (plambda ((k region))
    (lambda ()
      (module
        (define cell (ref int k) (new 0))
        (define read-it (subr (read k) () int) (lambda () (get cell)))
        (define bump (subr (maxeff (read k) (write k)) () unit)
          (lambda () (set cell (+ (get cell) 1))))))))
(let ((c ((proj make-cell @mine))))
  (with c (begin (bump) (bump) (read-it))))
