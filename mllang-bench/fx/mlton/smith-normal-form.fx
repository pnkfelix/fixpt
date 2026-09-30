;;; SMITH-NORMAL-FORM -- the Smith normal form of a 35 x 35 integer matrix
;;; of digits, by row and column operations on exact integers, the last
;;; of which has 46 digits.
;;;
;;; Written by Henry Cejtin (henry@sourcelight.com).
;;; From MLton's benchmark suite (benchmark/tests/smith-normal-form.sml,
;;; commit aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's
;;; driver was not fetched): (doit 1), 1 run of `snf`.
;;; Answer: -1027954043102083189860753402541358641712697245, the last
;;; diagonal entry of the normal form, which the original checks for
;;; (raising Fail "bug" if it differs); a Python transcription of the same
;;; algorithm gives it too, after 2452 row and column operations.
;;;
;;; What changed:
;;; - IntInf.int is `int`, exact at any size; `IntInf.quot` is `quotient`
;;;   and `IntInf.fromInt` the identity. The matrices are of ints, not of
;;;   any `'entry`, so `Matrix.map` is given an int's function.
;;; - Matrix's own checks of indexes (`raise index`, `raise sizeError`)
;;;   are left out: an array's bounds are checked anyway, and none fails.
;;;   `toString` and `show`, never called, are left out, and so is `dd`'s
;;;   print of each position ("dd: pos = ..."). `doit` returns the last
;;;   `snf`'s entry, where the original compares it and returns ().
;;; - Tuples of arguments are separate parameters; `dd`'s mutually
;;;   recursive local functions are one `letrec`, `colLoop` beside
;;;   `rowLoop` rather than inside it.

(define-effect mx (maxeff (read @m) (write @m) (alloc @m) spin))

;; ---- structure Matrix

(define-type entries (arrayof int @m))
(define-type matrix (productof (height int) (width int) (mat entries)))
(define-type getter (subr (read @m) (int) int))
(define-type setter (subr (write @m) (int int) unit))
(define-type binop (subr pure (int int) int))

;; What a matrix's generator does: here, look in `table`.
(define-type generator (subr (maxeff spin (read (globals nth table))) (int int) int))

(define* make (subr mx (int int generator) matrix)
  (lambda (height width generator)
    (let ((a (the entries (make-array (* height width) 0))))
      (letrec ((fill (subr (maxeff mx (read (globals nth table))) (int) unit)
                 (lambda (z)
                   (if (< z (* height width))
                       (begin (array-set! a z (generator (quotient z width) (modulo z width)))
                              (fill (+ z 1)))
                       #u))))
        (begin (fill 0) (product (height height) (width width) (mat a)))))))

(define* fetch (subr (read @m) (matrix int int) int)
  (lambda (m row col) (array-ref (extract m mat) (+ col (* (extract m width) row)))))

(define* fetch-row (subr pure (matrix int) getter)
  (lambda (m row)
    (let ((offset (* (extract m width) row)) (a (extract m mat)))
      (lambda (col) (array-ref a (+ col offset))))))

(define* fetch-col (subr pure (matrix int) getter)
  (lambda (m col)
    (let ((width (extract m width)) (a (extract m mat)))
      (lambda (row) (array-ref a (+ col (* width row)))))))

(define* store-row (subr pure (matrix int) setter)
  (lambda (m row)
    (let ((offset (* (extract m width) row)) (a (extract m mat)))
      (lambda (col entry) (array-set! a (+ col offset) entry)))))

(define* store-col (subr pure (matrix int) setter)
  (lambda (m col)
    (let ((width (extract m width)) (a (extract m mat)))
      (lambda (row entry) (array-set! a (+ col (* width row)) entry)))))

(define* swap-loop (subr (maxeff (read @m) (write @m) spin) (getter setter getter setter int) unit)
  (lambda (from1 to1 from2 to2 limit)
    (letrec ((loop (subr (maxeff (read @m) (write @m) spin) (int) unit)
               (lambda (i)
                 (if (= i limit)
                     #u
                     (let ((tmp (from1 i)))
                       (begin (to1 i (from2 i)) (to2 i tmp) (loop (+ i 1))))))))
      (loop 0))))

(define* row-swap (subr (maxeff (read @m) (write @m) spin) (matrix int int) unit)
  (lambda (m row1 row2)
    (if (= row1 row2)
        #u
        (swap-loop (fetch-row m row1) (store-row m row1) (fetch-row m row2) (store-row m row2)
                   (extract m width)))))

(define* col-swap (subr (maxeff (read @m) (write @m) spin) (matrix int int) unit)
  (lambda (m col1 col2)
    (if (= col1 col2)
        #u
        (swap-loop (fetch-col m col1) (store-col m col1) (fetch-col m col2) (store-col m col2)
                   (extract m height)))))

(define* op-loop (subr (maxeff (read @m) (write @m) spin) (getter getter setter int binop) unit)
  (lambda (from1 from2 to2 limit f)
    (letrec ((loop (subr (maxeff (read @m) (write @m) spin) (int) unit)
               (lambda (i)
                 (if (= i limit)
                     #u
                     (begin (to2 i (f (from1 i) (from2 i))) (loop (+ i 1)))))))
      (loop 0))))

(define* row-op (subr (maxeff (read @m) (write @m) spin) (matrix int int binop) unit)
  (lambda (m row1 row2 f)
    (op-loop (fetch-row m row1) (fetch-row m row2) (store-row m row2) (extract m width) f)))

(define* col-op (subr (maxeff (read @m) (write @m) spin) (matrix int int binop) unit)
  (lambda (m col1 col2 f)
    (op-loop (fetch-col m col1) (fetch-col m col2) (store-col m col2) (extract m height) f)))

;; Matrix.map; Matrix.copy is map of the identity, as Array.tabulate
;; copies.
(define* mmap (subr mx (matrix (subr pure (int) int)) matrix)
  (lambda (m f)
    (let* ((from (extract m mat))
           (a (the entries (make-array (array-length from) 0))))
      (letrec ((fill (subr mx (int) unit)
                 (lambda (i)
                   (if (< i (array-length from))
                       (begin (array-set! a i (f (array-ref from i))) (fill (+ i 1)))
                       #u))))
        (begin (fill 0) (product (height (extract m height)) (width (extract m width)) (mat a)))))))

(define* copy (subr mx (matrix) matrix) (lambda (m) (mmap m (lambda (x) x))))

;; ---- Smith normal form

(define zero int 0)

(define* abs (subr pure (int) int) (lambda (a) (if (< a 0) (- 0 a) a)))

(define* smaller (subr pure (int int) bool)
  (lambda (a b) (and (not (= a zero)) (or (= b zero) (< (abs a) (abs b))))))

;; What `dd`'s local functions read.
(define-effect dd-eff
  (maxeff mx (read (globals abs col-op col-swap fetch-col fetch-row op-loop row-op row-swap
                            smaller store-col store-row swap-loop zero))))

(define* dd (subr mx (matrix int) unit)
  (lambda (mat pos)
    (let ((height (extract mat height)) (width (extract mat width))
          (mat-col (fetch-col mat pos)) (mat-row (fetch-row mat pos)))
      (letrec ((swap-row-loop
                (subr dd-eff (int int int int) unit)
                (lambda (best best-row best-col row)
                  (if (>= row height)
                      (begin (row-swap mat pos best-row) (col-swap mat pos best-col))
                      (let ((mat-row (fetch-row mat row)))
                        (letrec ((swap-col-loop
                                  (subr dd-eff (int int int int) unit)
                                  (lambda (best best-row best-col col)
                                    (if (>= col width)
                                        (swap-row-loop best best-row best-col (+ row 1))
                                        (let ((next (mat-row col)))
                                          (if (smaller next best)
                                              (swap-col-loop next row col (+ col 1))
                                              (swap-col-loop best best-row best-col (+ col 1))))))))
                          (swap-col-loop best best-row best-col pos))))))
               (row-loop
                (subr dd-eff (int) unit)
                (lambda (row)
                  (if (< row height)
                      (if (= (mat-col row) zero)
                          (row-loop (+ row 1))
                          (begin
                            (row-op mat pos row
                                    (let ((x (- 0 (quotient (mat-col row) (mat-col pos)))))
                                      (lambda (lhs rhs) (+ (* lhs x) rhs))))
                            (if (= (mat-col row) zero) (row-loop (+ row 1)) (hit-pos-again))))
                      (col-loop (+ pos 1)))))
               (col-loop
                (subr dd-eff (int) unit)
                (lambda (col)
                  (if (< col width)
                      (if (= (mat-row col) zero)
                          (col-loop (+ col 1))
                          (begin
                            (col-op mat pos col
                                    (let ((x (- 0 (quotient (mat-row col) (mat-row pos)))))
                                      (lambda (lhs rhs) (+ (* lhs x) rhs))))
                            (if (= (mat-row col) zero) (col-loop (+ col 1)) (hit-pos-again))))
                      #u)))
               (hit-pos-again
                (subr dd-eff () unit)
                (lambda () (begin (swap-row-loop zero pos pos pos) (row-loop (+ pos 1))))))
        (hit-pos-again)))))

(define* snf-loop (subr mx (matrix int int) matrix)
  (lambda (mat range pos)
    (if (= pos range) mat (begin (dd mat pos) (snf-loop mat range (+ pos 1))))))

(define* smith-normal-form (subr mx (matrix) matrix)
  (lambda (mat)
    (let ((height (extract mat height)) (width (extract mat width)))
      (snf-loop (copy mat) (if (< width height) width height) 0))))

;; List.nth
(define nth (poly ((a type)) (subr spin ((listof a acyclic) int) a))
  (plambda ((a type))
    (lambda (l i)
      (letrec ((loop (subr spin ((listof a acyclic) int) a)
                 (lambda (l i) (if (= i 0) (car l) (loop (cdr l) (- i 1))))))
        (loop l i)))))

(define table (listof (listof int acyclic) acyclic)
  (list (list  8 -3  1  3  6  9 -2  4 -9 -9  2  3  8 -1  3 -5  4 -3 -5 -6  8  1  4 -5  7
              -4 -4 -7  7  1  4 -3  8  4 -4 -8  5 -9  3 -4  1  9 -8 -6 -2  8 -9 -5 -3 -3)
        (list  0  8 -6 -2 -3  4  5 -2  7 -7 -6 -7 -3 -4  9  7 -3  3  0  3  3 -8 -8  2  3
               8  3 -2 -4  3 -6 -6 -2  6  5 -1 -3  1  8 -8  2  1 -7 -7 -7 -3 -6  6 -4 -9)
        (list  0 -5  8 -9  2  4  2  7 -4  9 -3  6 -2  3 -3  0 -9  5  8 -1  2 -8  3  4 -6
               5 -6 -5 -8  0 -5  3 -2 -5  8  7 -1  1 -1  7  6  3  6  5  6  8  7  9  7 -3)
        (list  5  4  7  2  3 -9  7 -7  3 -8  7  5  5 -2 -6 -3  6  5  3 -1 -1  4  5 -5  5
               9  9  3  8 -3 -1  9 -9  6 -7  7  4  6 -8 -9  0 -3 -2 -7  1 -2 -6  7  7  7)
        (list  2  9  9  3 -4  0  9  2  5  3 -5 -3 -1  1  8 -6  2 -4 -8 -7 -8  4  5  8 -1
              -1  7  2  5  5 -4 -7 -3 -7  6 -4 -5 -8 -5 -9 -8  5 -5 -5  0  8  8  6  4 -1)
        (list  5  5  1 -7  3 -5  4  9  3  4  4 -5  7 -1  7  4 -7  7 -7 -2  9 -9  0 -4 -4
               0  2  6  3 -1  6  6  8 -6 -4 -9  3 -2 -5  5 -3  2 -1 -6  9  3 -3 -8 -9  7)
        (list  7  1  2  7  6  5 -6 -3 -4 -8  0  9  6  1  2 -5  4  4  4 -6 -7 -9 -6  2 -4
               5 -2  1  0  1 -8  7 -7 -5  4  1 -5  4 -4 -2 -3  1  1  3  4 -4 -5  9  8 -2)
        (list  6  2 -1 -8  4 -7  7 -3 -2 -5  3  0  3 -9  3  3  9 -1  4  8 -9  6 -5  9  5
              -1 -1 -9  7 -2  3  9  8  9  2  7  7  6 -1 -1 -2 -2 -7  3 -6  0 -9  4  3  7)
        (list  0 -6 -3 -7 -1  5 -2  8 -5 -3 -8  7 -2 -2  0 -8  4  8  9 -5 -4 -8 -1  7  1
               1  6 -9 -4  0  8  4  3 -7  6  0  1  8  6 -1 -1 -7  9 -9 -5 -2 -2 -1  1  0)
        (list -4  9  6 -3 -2 -6 -3  4  8 -8  1 -5  9  7  9  7 -9 -6  6  1 -3  3 -3 -7  1
               7 -7  0 -2  7 -4 -6  0  1 -3 -5 -9 -7  8  4  9 -8 -8 -7 -6  7  6 -3 -8  5)
        (list  6  7 -5 -9  6  1  8  4 -2  7 -7 -1 -9  1 -6 -5  4  9  6  0 -8 -3  1 -3  8
              -3  2  9 -3 -9 -1 -3  4  3  2 -9 -5 -3  8 -4  8  5 -4  7  6 -8  7  6 -5  5)
        (list  1  7 -8 -9 -7 -3  8  9 -7 -1 -7  4  0  0  1 -5  9 -8 -1 -2  3  5  9 -9  5
               4 -9  1 -4 -2  3 -4  8 -6 -4 -8 -5 -5  4 -2 -4 -1 -9 -5  2 -9  2 -9 -2 -3)
        (list -5 -4 -4  9  2  7 -2  6  7  2 -9  4  2  7  8 -9  2  5  3  9  6  3  0 -7 -6
              -7  6 -2  9 -3 -6  9 -9  2  2 -6 -1  4 -3  3  0  6 -3  4  9  9 -6  5  5 -5)
        (list  5 -7  8 -4  8  8 -4 -9  6  0 -3  6  0  8  8 -6 -2  5  4 -1 -8  1 -3 -1  2
               3 -9 -9 -5  1  8 -5 -3  0 -4 -9  0 -6  3 -1 -7  0  8  9 -6 -1 -9  1 -6  2)
        (list  7 -5 -1  5 -2  7  0 -7 -1  8  8 -3  9 -5  7 -8 -8 -4  3  2 -1  8 -2  1  2
               5  0 -6  7  3  3  7 -5  5 -1  1  0 -8  1  0  0 -4  6  9 -5 -6  3 -5  8  5)
        (list -4 -2  3 -3 -1  2 -2 -1 -9 -5  1  0  0  2  9 -3 -9  2  9  3  8 -3  4  8  8
               3 -3 -1 -4  4 -6 -9  5 -2  1  3 -7 -5 -6 -5 -8  4 -8 -3  5  0  7 -9  6  2)
        (list  5  1  4 -3 -1 -9  5 -8 -8  6  1  1 -2  7  5  6 -4  2 -7  0 -7 -3 -5  9  3
               4 -6  8 -4  3  6  0  2  3 -6  3  9  4  1 -4  6 -5 -7  0 -1 -8 -3 -9  9  7)
        (list  2 -6 -1  8  4 -3 -1 -6 -2 -8 -2 -1 -1 -5 -9 -8  9 -9  5  1  9 -1 -6  9 -7
               2  8 -7  4 -9  7  6 -2  1 -2 -7  8  0  5  0 -5 -7 -6  0  4  0  3 -8  5  4)
        (list -2  9 -9 -6  1 -8  8  4 -6  8  1 -3 -7  8 -5  2 -8  1  3 -2  6  6  6  1  0
               0 -7  7 -3 -3  0 -4  3 -7 -6  7  5  9 -5  7 -8  2  3 -8 -7  6 -5 -5 -8 -9)
        (list -7 -4  4  1 -1 -3 -8  3  7  9  8  3  0  4  4 -1 -5  4  2  2  0  6 -6  2 -9
               8 -9  3 -2  2  6  6  1  7  1  0 -8  2  3 -3  8  9  5  5 -6  4 -7 -4 -2 -3)
        (list -5  8  6  1 -6 -6  6  1  1 -3 -9 -6  2 -7  2 -1  6 -6  0  2 -7  8 -8  4  9
              -3  9 -7 -9 -6 -4 -4 -5  8  2 -5 -4 -3  5  2  1 -3 -3 -7 -9  3  7 -7  3 -8)
        (list -4 -7 -2  2 -4 -2  6 -3 -1 -4  0 -5  9  7 -6 -9  7 -9 -6  2 -3  1  5 -9  4
              -5  4 -9  1 -2 -2  4  0  4 -8 -8  3 -1 -5 -4 -9 -7  7  6  3 -9  6  4 -4 -7)
        (list -9  6  6 -5 -1 -7  4 -9  4 -1  6 -4  7  2  8  7  3  1 -7  7  7  9  8 -9  7
               2  1  2 -8  4  5  6  7  2 -7  6  8  4 -9  7 -5  6  9 -1  9  2  0  9  3  6)
        (list  4 -3  8  0 -2 -2  2 -3  8  3  1 -8 -5 -2  5  6  8  0 -3  4 -2  4 -9 -5  7
               6 -4 -7  2  4 -3 -8 -9  9  8 -9  3 -7  4 -7 -5  4  9  3 -6 -3 -7  4  2 -2)
        (list -8 -8  6 -2 -6  8 -3  3 -1 -7  1  9  1  7 -6  8 -2 -9 -1  3 -4  7  8 -1  9
              -9  6 -3  5  0  2  5 -1 -6 -6  1  8  6 -3 -9 -1  9 -2  9 -8 -7 -3  6 -3 -3)
        (list  5 -2  3  0 -9 -8 -6  1  8  0  1  2 -8 -2  0 -9 -8  0  5 -3 -4  5  6 -2 -5
               0 -9  9 -9 -5  9  9 -5 -2  4  3  8 -8 -7  5 -3 -2  2  3  9  7 -1  0  4 -1)
        (list -4  5 -5  7  8  9  7 -3  1  9 -7 -1  8 -5 -1  2 -8  1  0  9 -8 -1  6 -1  9
              -8  7  4 -8  7  0 -6  2  3  7  4 -3 -5  9 -3  0  6 -9  2  4 -8  6 -7  9  1)
        (list  7  0 -9  6  8  2  2  5 -6 -6  9 -5  9  2  2 -8  0 -6 -9 -6 -4 -9  8 -2  9
               7 -5 -1  7  2 -7  7 -1 -3  6  6  1 -4  0 -1 -6 -5  6 -7 -3 -2  8  2 -9  8)
        (list  8 -7 -9 -6  9 -7 -7  6 -8  9  5 -4  1 -7 -8 -6 -3  8 -8  1 -8  6  9 -3 -7
               7  1  6  1  0  8 -5 -8  8 -9  0  4  4  3 -4  6 -3 -9  0  4 -4 -5 -9 -5 -8)
        (list -3 -2  8  1 -1 -1 -4  3  7 -2 -9  9 -8 -9  6 -4  7 -1 -5 -3 -9  0 -3  0  7
               9  1 -2  7 -9 -6  3  3 -4 -7 -3 -4 -8 -2 -3 -9 -2 -6  3 -6 -4  7 -5 -8 -1)
        (list -9 -9 -2 -9 -9  9  6  6  7  5 -1 -2  1  5  2 -3 -4  1 -6  0 -3 -9 -1  7  0
              -9  5 -2 -2  5  3  4 -1  6 -6  3 -6  7 -1  5 -8 -4 -2 -2 -6 -5 -6  3 -1  4)
        (list  7  7  8  7  6  1 -2  5 -6  9  4  8  5  0 -4 -2 -2 -5 -2 -6  9 -8 -2 -5 -9
               3 -6 -3 -4 -5 -2  6  1  6 -5  0 -3 -2  4 -6  1  6 -1  3 -9  2 -3  1  5 -6)
        (list  6  4 -7  3 -7  9  1 -7 -8  0 -6  8  4  1  9  6  8  3  0  9  0  4  9 -7 -7
               1  5  1 -5  6  9  2  4  1 -9  8  4  5  8  3  2 -9 -6 -9  9 -9  7 -6 -4  3)
        (list -3 -9 -4  2  3  9 -9  8 -9  9 -4 -9 -5  5  0  7  3 -5 -8  2 -3  0 -9 -3  1
               9  4  5 -1  8  0 -4 -2  9 -4 -1  3  5  9 -1  1  4 -8 -2 -3  5  1  5 -6  7)
        (list  9 -3  2 -9  3  4  0  7 -5  9  0 -6  7 -2  3 -7  2 -5 -2  6  3 -9 -5 -9  5
               2 -5 -3  8 -5  6  2  9 -7 -7 -7 -6  9 -3  6  0  6 -6 -9  4 -3 -9  0 -4 -9)
        (list -4 -8  8 -7  7  0 -6 -6  8 -9 -4  5 -3 -1  7 -5 -6 -1  8  6 -2  1 -1  5 -9
               1 -1 -7 -6 -6 -6 -4  6  3 -5 -5 -6  2  3 -6 -8 -3  8 -2 -5 -4 -3  1  4 -4)
        (list  4 -6  2  6  2 -8  8  5  8 -2  0 -6 -1 -6 -2  2  6 -9 -7 -6 -4 -4 -7 -2  8
               6  3 -7 -6  8  2  3  4  5  3  4 -6  8  8 -1  4 -5  6  2  8 -3 -9 -2  6  7)
        (list  3 -4  0 -3 -5  0 -2 -6 -2  8  5 -9 -4 -8 -6  0  8  9  1 -2  8  2 -2  8  9
               3  3  5 -9 -3 -2  7  2  9  0  4  8 -9  0 -6  9 -9  9 -4  8 -8 -8  2 -3  2)
        (list -1  3 -9 -8 -7  6 -6  3  0  5 -5  1  2 -2 -3  7  7  3 -4 -2 -9 -5 -1  9  6
               8  2  8  7 -3  4  6  6  0 -2  2 -7 -7  6 -3  8  2  1  0  8 -1  3  9  8  6)
        (list  1 -2 -3  6  5  5 -6 -4 -5  1  1  6 -7 -4 -3  4  4 -8 -9  7 -2 -3 -7 -2  1
               2  0  8 -6 -5 -5  7  8  5 -2  3  9  0  5  1  3 -4 -6  1  4 -9 -2  5  4  3)
        (list  3  3  9 -2  6  9  4  9  4 -8  5 -1  3 -2  1 -7 -3  2  2  0 -3  3  8  2  0
              -5  7  1  4 -8  8 -9 -1  1 -9 -4  5  2  2  8  6  1  6 -2  2  7  1 -6 -1 -1)
        (list  4 -2  4 -1 -5 -1  5 -2  3 -4 -5  0  2 -4  6  4 -3  2  2  5 -6 -7 -9 -1 -9
              -9  6  0  6  5  9 -1  3 -3 -8  8 -8  8  4  5 -1 -5  1  0  3 -2  5  6  6  5)
        (list -4  9  6  8 -9  5  5 -3 -7  7  6  8 -8  0  4 -1  9  5 -7  0 -1 -2  3  6  0
               4 -3  1  4  6  4  0  5 -1  7 -7 -6 -8 -3 -6  7 -1 -3 -2 -3 -5  3  1 -8 -9)
        (list -6  4 -5  9  9 -7 -1 -8 -4  2 -6  0 -6 -6  7  6  0  1  7 -7  0 -4 -6 -8 -9
               5 -6 -9  2 -7 -2 -6  9  4 -5  0  4 -4 -5  6  9  1 -6 -5  3 -1  7 -7 -6  7)
        (list -8  7  7 -6  7 -4  8  0 -9 -8 -3  7 -3  3  8 -7 -2 -7  5  5 -5  4  6  2  4
               1  4 -9 -3  8  8 -9 -4 -2  1 -3  1  3  9 -5 -8 -2  7  8  9  2  0  1 -9  6)
        (list -7  1 -9  5 -5 -5  7  6 -5 -9 -6 -8 -6  9  7  9  0 -5  7  7 -6  4  5 -9 -1
              -2 -7  3 -5 -2 -5  5 -3 -4 -2 -8  2 -8  0 -8  0 -8  9  8 -5 -5  1  3  5 -4)
        (list -8 -8  0 -5 -8 -6  3 -6 -4  6  1 -5 -6 -8 -4 -6 -2 -6  6 -4  8  8  4 -5 -1
               0  9 -8 -3 -1 -8  7 -3  0 -7  1 -7 -1 -7  3 -7  3 -4 -8  8 -7 -9 -8  3  2)
        (list  3  6  8 -9  7  1 -9  9  3  8  6  4 -2  1 -8  4 -7 -4 -3  3 -5 -6 -7 -2  0
              -4  5  2  5  6  3 -8  2 -5 -7  6  8 -2 -5 -4  9  9  2 -2 -2  7  4  4 -2  3)
        (list  6  6 -5 -2 -8 -2 -9  0  2  4 -6 -9  9  0 -8 -3 -1 -2 -1  6  8  2 -9  5 -2
               1  7 -6  5  1 -1  4 -4 -7 -6 -3 -8  2  2  5  5 -6  5  3  3  7  4  7 -3 -9)
        (list -9  6 -4  1  3 -8 -8 -8 -1  5  1  1 -1  6  5  1 -1  5 -8  8 -7 -5 -1 -1  6
              -8 -3 -1 -2 -6 -5 -5 -6  0  2  2  7 -1 -5 -7 -1 -3  7  6  0  2  4 -5  0 -4)))

(define* f (subr spin (int int) int)
  (lambda (x y) ((proj nth int) ((proj nth (listof int acyclic)) table x) y)))

;; ---- structure Main

(define* snf (subr mx () int)
  (lambda ()
    (let* ((dim 35)
           (big (mmap (make dim dim f) (lambda (x) x))))
      (fetch (smith-normal-form big) (- dim 1) (- dim 1)))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 1)

(define* doit (subr mx (int int) int)
  (lambda (n entry) (if (= n 0) entry (doit (- n 1) (snf)))))

(doit iterations 0)
