;;; The algebraic path problem (Carré; Dolan's "Fun with semirings"):
;;; one closure algorithm, a semiring as a dictionary, and the instance
;;; chooses the problem. For idempotent semirings in which every element's
;;; star is the unit (booleans, min-plus over non-negative weights), the
;;; closure is Floyd-Warshall-Kleene's triple loop. The matrix is copied
;;; into a region, closed in place, and frozen: `pure` but for `spin`
;;; (the loops are bounded by n, which size-change cannot see).
(define-type (semiring (t type))
  (productof (zero t) (one t) (plus (subr pure (t t) t)) (times (subr pure (t t) t))))
;; A matrix built in order and never written is `acyclic`; one closed
;; in place, by writes, leaves its `letfreeze` at `const`.
(define-type (built (t type)) (arrayof (arrayof t acyclic) acyclic))
(define-type (matrix (t type)) (arrayof (arrayof t const) const))
(define closure
  (poly ((t type))
    (subr spin ((semiring t) (built t)) (matrix t)))
  (lambda (s m)
    (let ((n (array-length m)) (plus (extract s plus)) (times (extract s times)))
      (letfreeze r
        (let ((d (the (arrayof (arrayof t r) r) (make-array n (the (arrayof t r) (make-array 0 (extract s zero)))))))
          (letrec ((copy (subr (maxeff (read r) (write r) (alloc r) spin) (int) unit)
                     (lambda (i)
                       (if (= i n) #u
                           (let ((row (the (arrayof t r) (make-array n (extract s zero)))))
                             (letrec ((cols (subr (maxeff (write r) spin) (int) unit)
                                        (lambda (j)
                                          (if (= j n) #u
                                              (begin (array-set! row j (if (= i j) (plus (extract s one) (array-ref (array-ref m i) j))
                                                                           (array-ref (array-ref m i) j)))
                                                     (cols (+ j 1)))))))
                               (begin (cols 0) (array-set! d i row) (copy (+ i 1))))))))
                   ;; d[i][j] := d[i][j] + d[i][k] * d[k][j], for each k, i, j.
                   (relax (subr (maxeff (read r) (write r) spin) (int int int) unit)
                     (lambda (k i j)
                       (cond ((= k n) #u)
                             ((= i n) (relax (+ k 1) 0 0))
                             ((= j n) (relax k (+ i 1) 0))
                             (else
                              (let ((dij (array-ref (array-ref d i) j))
                                    (via (times (array-ref (array-ref d i) k) (array-ref (array-ref d k) j))))
                                (begin (array-set! (array-ref d i) j (plus dij via))
                                       (relax k i (+ j 1)))))))))
            (begin (copy 0) (relax 0 0 0) d)))))))
;; Two instances, one algorithm: reachability and shortest paths.
(define bool-sr (semiring bool)
  (product (zero #f) (one #t) (plus (lambda (a b) (or a b))) (times (lambda (a b) (and a b)))))
;; Min-plus, with 1000000 standing for no path.
(define min-plus (semiring int)
  (product (zero 1000000) (one 0)
           (plus (lambda (a b) (if (< a b) a b)))
           (times (lambda (a b) (if (or (= a 1000000) (= b 1000000)) 1000000 (+ a b))))))
(define inf int 1000000)
;; 0 -2-> 1 -3-> 2 -1-> 0, and 0 -9-> 2.
(define frozen-row
  (poly ((t type)) (subr pure ((listof t acyclic)) (arrayof t acyclic)))
  (lambda (xs) (letfreeze r (the (arrayof t r) (list->array xs)))))
(define w (built int)
  (letfreeze r
    (the (arrayof (arrayof int acyclic) r)
      (list->array (list ((proj frozen-row int) (list inf 2 9))
                         ((proj frozen-row int) (list inf inf 3))
                         ((proj frozen-row int) (list 1 inf inf)))))))
(define reach (built bool)
  (letfreeze r
    (the (arrayof (arrayof bool acyclic) r)
      (list->array (list ((proj frozen-row bool) (list #f #t #t))
                         ((proj frozen-row bool) (list #f #f #t))
                         ((proj frozen-row bool) (list #t #f #f)))))))
(define dist (matrix int) ((proj closure int) min-plus w))
(define r2 (matrix bool) ((proj closure bool) bool-sr reach))
(list (array->list (array-ref dist 0)) (array->list (array-ref dist 2))
      (if (array-ref (array-ref r2 2) 1) (list 1) (list 0)))
