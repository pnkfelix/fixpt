;; ! whose results are procedures that may keep what the call allocates: one value would be both
;; No cell in the results' types: a writer and a reader of it, in a product,
;; whose fields are met one by one. The writer's `ab` view and the reader's
;; `ac` one would be of one cell.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define-type (rw (t type))
  (productof (w (subr (write @h) (t) unit)) (r (subr (read @h) () t))))
(define mk (allof (subr (alloc @h) (ab) (rw ab)) (subr (alloc @h) (ac) (rw ac)))
  (lambda (x)
    (let ((c ((proj new @h) x)))
      (product (w (lambda (v) (set c v))) (r (lambda () (get c)))))))
(define p (mk (sum a 1)))
(define as-ab (rw ab) p)
(define as-ac (rw ac) p)
((extract as-ab w) (sum b 2))
(tagcase ((extract as-ac r)) (a i (+ i 100)) (c k (+ k 200)))
