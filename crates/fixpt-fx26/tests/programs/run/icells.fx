;;; Mutual recursion with its knot made explicit: I-cells, each written once
;;; and read after (docs/research/recursion-and-initialization.md).

;; At the top level, the cells are in a region the program names, so the
;; reads show: `(await @k)`.
(define-type parity-test
  (subr (maxeff (await @k) spin (read (globals even-cell odd-cell))) (int) bool))
(define even-cell (icell parity-test @k) (make-icell))
(define odd-cell (icell parity-test @k) (make-icell))
(icell-put! even-cell (lambda ((n int)) (if (= n 0) #t ((icell-get odd-cell) (- n 1)))))
(icell-put! odd-cell (lambda ((n int)) (if (= n 0) #f ((icell-get even-cell) (- n 1)))))

;; Inside a procedure, nothing outside names the cells' region, so masking
;; removes every effect on it: the knot is explicit, and `parity` is pure.
(define parity (subr spin (int) bool)
  (lambda (n)
    (let ((ev (the (icell (subr (maxeff (await @p) spin) (int) bool) @p) (make-icell)))
          (od (the (icell (subr (maxeff (await @p) spin) (int) bool) @p) (make-icell))))
      (begin
        (icell-put! ev (lambda ((k int)) (if (= k 0) #t ((icell-get od) (- k 1)))))
        (icell-put! od (lambda ((k int)) (if (= k 0) #f ((icell-get ev) (- k 1)))))
        ((icell-get ev) n)))))

(list ((icell-get even-cell) 10) ((icell-get odd-cell) 10) (parity 7) (parity 1000))
