;;; MATRIX -- Obtained from Andrew Wright.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/matrix.scm),
;;; ported to FX-26. Larceny's input: 2500 iterations of (really-go 5 5).
;;; Answer (the last form converts the result to a `datum` to print it):
;;;   (((1 1 1 1 1) (1 1 1 1 -1) (1 1 1 -1 1) (1 1 -1 -1 -1) (1 -1 1 -1 -1) (1 -1 -1 1 1))
;;;    ((1 1 1 1 1) (1 1 1 1 -1) (1 1 1 -1 1) (1 1 -1 1 -1) (1 -1 1 -1 -1) (1 -1 -1 1 1))
;;;    ((1 1 1 1 1) (1 1 1 1 -1) (1 1 1 -1 1) (1 1 -1 1 -1) (1 -1 1 -1 1) (1 -1 -1 1 1))
;;;    ((1 1 1 1 1) (1 1 1 1 -1) (1 1 1 -1 1) (1 1 -1 1 1) (1 -1 1 1 -1) (1 -1 -1 -1 1))
;;;    ((1 1 1 1 1) (1 1 1 1 -1) (1 1 1 -1 1) (1 1 -1 1 1) (1 -1 1 1 1) (1 -1 -1 -1 -1)))
;;;
;;; What the port changes, and why:
;;; - Definitions come in the order they are used (FX-26 sees only earlier
;;;   definitions), and the named lets are local `letrec`s, nested as the
;;;   original nests them.
;;; - `gen-perms` returns #f or a closure answering the messages `now`,
;;;   `brother`, `child` and `puke` with values of different types. Those
;;;   values are one datatype, `pv`: `no-perm` (Scheme's #f), `a-perm` (the
;;;   closure), `r-row` (the row `now` answers) and `r-rows` (what `puke`
;;;   answers). The closure still dispatches on the message symbol; `send`
;;;   calls it and `pv-row` takes the row out of a reply. An unknown message,
;;;   an error in the original, answers `no-perm`.
;;; - `go-folder`'s state is Larceny's list `(bsize blen . blist)`, as pairs
;;;   of an int, an int and a list; blist's elements are matrices, or the
;;;   string "..." after 3000 of them (never reached here), so they are a
;;;   datatype, `entry`, of the two.
;;; - Scheme's `map` is `map` (one list) and `map2` (two), polymorphic,
;;;   written here; `length` of a mutable list is `list-length`; `remainder`
;;;   is written with `quotient`; `expt` and `even?` are written here. `div`
;;;   and `mod` are the R6RS ones the original defines, less their
;;;   `exact-integer?` tests, which are always true of FX-26's integers.
;;; - `make-modular` hands its `maker` results of two types, so it is
;;;   polymorphic in that type, and its callers `proj` it. (Its result, made
;;;   after the effect of computing the inverses, cannot be the polymorphic
;;;   value: FX-26 requires a polymorphic value to be pure.)
;;; - `extended-gcd`'s `n->sgn/abs` returns `(cons -1 (- x))` for a negative
;;;   `x` where it means `(cont -1 (- x))` (a bug that no run reaches: both
;;;   arguments are positive here); the port calls `cont`, since a pair is
;;;   not an int. Its continuation's result is an int, the only use.
;;; - `make-vector` with no fill fills with 0.
;;; - A `case` with no `else` has `(else #f)`; no run reaches it.
;;; - Procedures' types read `@globals` (the effect `M`), since procedures
;;;   passed around call many globals.

(define-effect M (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)))
(define-type row (listof int @heap))
(define-type mat (listof row @heap))

;;; We need R6RS div and mod for this benchmark.

(define remainder (subr pure (int int) int) (lambda (x y) (- x (* (quotient x y) y))))

(define div (subr pure (int int) int)
  (lambda (x y)
    (cond ((>= x 0)
           (quotient x y))
          ((< y 0)
           ; x < 0, y < 0
           (let* ((q (quotient x y))
                  (r (- x (* q y))))
             (if (= r 0)
                 q
                 (+ q 1))))
          (else
           ; x < 0, y > 0
           (let* ((q (quotient x y))
                  (r (- x (* q y))))
             (if (= r 0)
                 q
                 (- q 1)))))))

(define* mod (subr pure (int int) int)
  (lambda (x y)
    (cond ((>= x 0)
           (remainder x y))
          ((< y 0)
           ; x < 0, y < 0
           (let* ((q (quotient x y))
                  (r (- x (* q y))))
             (if (= r 0)
                 0
                 (- r y))))
          (else
           ; x < 0, y > 0
           (let* ((q (quotient x y))
                  (r (- x (* q y))))
             (if (= r 0)
                 0
                 (+ r y)))))))

(define* expt (subr spin (int int) int)
  (lambda (b n) (if (= n 0) 1 (* b (expt b (- n 1))))))

(define even? (subr pure (int) bool) (lambda (n) (= (modulo n 2) 0)))

(define list-length (poly ((t type)) (subr M ((listof t @heap)) int))
  (plambda ((t type))
    (lambda (l)
      (letrec ((lp (subr M ((listof t @heap) int) int)
                 (lambda (l n) (if (null? l) n (lp (cdr l) (+ n 1))))))
        (lp l 0)))))

(define map
  (poly ((a type) (b type)) (subr M ((subr M (a) b) (listof a @heap)) (listof b @heap)))
  (plambda ((a type) (b type))
    (lambda (f l) (if (null? l) nil (cons (f (car l)) (map f (cdr l)))))))

(define map2
  (poly ((a type) (b type) (c type)) (subr M ((subr M (a b) c) (listof a @heap) (listof b @heap)) (listof c @heap)))
  (plambda ((a type) (b type) (c type))
    (lambda (f l1 l2) (if (null? l1) nil (cons (f (car l1) (car l2)) (map2 f (cdr l1) (cdr l2)))))))

; Chez-Scheme compatibility stuff:

(define chez-box (subr (alloc @heap) (row) (listof row @heap)) (lambda (x) (cons x nil)))
(define chez-unbox (subr (read @heap) ((listof row @heap)) row) (lambda (x) (car x)))
(define chez-set-box! (subr (write @heap) ((listof row @heap) row) unit) (lambda (x y) (set-car! x y)))

;; What a permutation object (below) is, and answers.
(define-datatype pv (no-perm) (a-perm (subr M (symbol) pv)) (r-row row) (r-rows mat))

(define send (subr M (pv symbol) pv)
  (lambda (o msg) (tagcase o (a-perm (p) (p msg)) (else x (no-perm)))))
(define perm? (subr pure (pv) bool)
  (lambda (o) (tagcase o (no-perm () #f) (else x #t))))
(define pv-row (subr pure (pv) row)
  (lambda (o) (tagcase o (r-row (r) r) (else x nil))))

(define* fold (subr M (mat (subr M (row mat) mat) mat) mat)
  (lambda (lst folder state)
    (letrec ((_-*- (subr M (mat mat) mat)
               (lambda (lst state)
                 (if (null? lst)
                     state
                     (_-*- (cdr lst)
                           (folder (car lst)
                                   state))))))
      (_-*- lst state))))

(define* miota (subr M (int) row)
  (lambda (len)
    (letrec ((_-*- (subr M (int) row)
               (lambda (i)
                 (if (= i len)
                     nil
                     (cons i
                           (_-*- (+ i 1)))))))
      (_-*- 0))))

(define* proc->vector (subr M (int (subr M (int) int)) (arrayof int @heap))
  (lambda (size proc)
    (let ((res (the (arrayof int @heap) (make-array size 0))))
      (letrec ((do-loop (subr M (int) unit)
                 (lambda (i)
                   (if (= i size)
                       #u
                       (begin (array-set! res i (proc i))
                              (do-loop (+ i 1)))))))
        (begin (do-loop 0)
               res)))))

(define* gen-perms (subr M (mat) pv)
  (lambda (objects)
    (letrec ((_-*- (subr M (mat mat) pv)
               (lambda (zulu-future past)
                 (if (null? zulu-future)
                     (no-perm)
                     (a-perm
                      (lambda ((msg symbol))
                        (cond ((symbol=? msg 'now)
                               (r-row (car zulu-future)))
                              ((symbol=? msg 'brother)
                               (_-*- (cdr zulu-future)
                                     (cons (car zulu-future)
                                           past)))
                              ((symbol=? msg 'child)
                               (gen-perms
                                (fold past cons (cdr zulu-future))))
                              ((symbol=? msg 'puke)
                               (r-rows (cons (car zulu-future)
                                             (fold past cons (cdr zulu-future)))))
                              (else
                               (no-perm)))))))))
      (_-*- objects nil))))

(define zulu (subr M (row (subr M (int) int) mat (subr M (mat) bool)) bool)
  (let ((cons-if-not-null
         (lambda ((lhs row) (rhs mat))
           (if (null? lhs)
               rhs
               (the mat (cons lhs rhs))))))
    (lambda (old-row new-row-func partitions equal-cont)
      (letrec ((_-*- (subr M (mat row mat) bool)
                 (lambda (p-in old-row rev-p-out)
                   (letrec ((_-split- (subr M (row row row row) bool)
                              (lambda (partition old-row plus minus)
                                (if (null? partition)
                                    (letrec ((_-minus- (subr M (row row) bool)
                                               (lambda (old-row m)
                                                 (if (null? m)
                                                     (let ((rev-p-out
                                                            (cons-if-not-null
                                                             minus
                                                             (cons-if-not-null
                                                              plus
                                                              rev-p-out)))
                                                           (p-in
                                                            (cdr p-in)))
                                                       (if (null? p-in)
                                                           (equal-cont (reverse rev-p-out))
                                                           (_-*- p-in old-row rev-p-out)))
                                                     (or (= 1 (car old-row))
                                                         (_-minus- (cdr old-row)
                                                                   (cdr m)))))))
                                      (_-minus- old-row minus))
                                    (let ((next
                                           (car partition)))
                                      (let ((v (new-row-func next)))
                                        (cond ((= v 1)
                                               (and (= 1 (car old-row))
                                                    (_-split- (cdr partition)
                                                              (cdr old-row)
                                                              (cons next plus)
                                                              minus)))
                                              ((= v -1)
                                               (_-split- (cdr partition)
                                                         old-row
                                                         plus
                                                         (cons next minus)))
                                              (else #f))))))))
                     (_-split- (car p-in) old-row nil nil)))))
        (_-*- partitions old-row nil)))))

(define* zebra (subr M (pv (subr M (row) (subr M (int) int)) (subr M (row) (subr M (int) int)) mat int) bool)
  (lambda (row-perm row->func+ row->func- mat number-of-cols)
    (letrec ((_-*- (subr M (pv mat mat) bool)
               (lambda (row-perm mat partitions)
                 (or (not (perm? row-perm))
                     (and
                      (zulu (car mat)
                            (row->func+ (pv-row (send row-perm 'now)))
                            partitions
                            (lambda ((new-partitions mat))
                              (_-*- (send row-perm 'child)
                                    (cdr mat)
                                    new-partitions)))
                      (zulu (car mat)
                            (row->func- (pv-row (send row-perm 'now)))
                            partitions
                            (lambda ((new-partitions mat))
                              (_-*- (send row-perm 'child)
                                    (cdr mat)
                                    new-partitions)))
                      (let ((new-row-perm
                             (send row-perm 'brother)))
                        (or (not (perm? new-row-perm))
                            (_-*- new-row-perm
                                  mat
                                  partitions))))))))
      (_-*- row-perm mat (cons (miota number-of-cols) nil)))))

(define* zunda (subr M (pv mat) bool)
  (lambda (first-row-perm mat)
    (let* ((first-row
            (pv-row (send first-row-perm 'now)))
           (number-of-cols
            (list-length first-row))
           (make-row->func
            (lambda ((if-equal int) (if-different int))
              (lambda ((row row))
                (let ((vec
                       (the (arrayof int @heap) (make-array number-of-cols 0))))
                  (letrec ((do-loop (subr M (int row row) unit)
                             (lambda (i first row)
                               (if (= i number-of-cols)
                                   #u
                                   (begin
                                     (array-set! vec
                                                 i
                                                 (if (= (car first) (car row))
                                                     if-equal
                                                     if-different))
                                     (do-loop (+ i 1) (cdr first) (cdr row)))))))
                    (begin
                      (do-loop 0 first-row row)
                      (lambda ((i int))
                        (array-ref vec i))))))))
           (mat
            (cdr mat)))
      (zebra (send first-row-perm 'child)
             (make-row->func 1 -1)
             (make-row->func -1 1)
             mat
             number-of-cols))))

; Test that a matrix with entries in {+1, -1} is maximal among the matricies
; obtainable by
;       re-ordering the rows
;       re-ordering the columns
;       negating any subset of the columns
;       negating any subset of the rows
; Where we compare two matricies by lexicographically comparing the first row,
; then the next to last, etc., and we compare a row by lexicographically
; comparing the first entry, the second entry, etc., and we compare two
; entries by +1 > -1.
; Note, this scheme obeys the useful fact that if (append mat1 mat2) is
; maximal, then so is mat1.  Thus, we can build up maximal matricies
; row by row.
;
; Once you have chosen the row re-ordering so that you know which row goes
; last, the set of columns to negate is fixed (since the last row must be
; all +1's).
;
; Note, the column ordering is really totally determined as follows:
;       all columns for which the second row is +1 must come before all
;               columns for which the second row is -1.
;       among columns for which the second row is +1, all columns for which
;               the third row is +1 come before those for which the third is
;               -1, and similarly for columns in which the second row is -1.
;       etc
; Thus, each succeeding row sorts columns withing refinings equivalence
; classes.
;
; Maximal? assumes that mat has atleast one row, and that the first row
; is all +1's.
(define* maximal? (subr M (mat) bool)
  (lambda (mat)
    (letrec ((pick-first-row (subr M (pv) bool)
               (lambda (first-row-perm)
                 (if (perm? first-row-perm)
                     (and (zunda first-row-perm mat)
                          (pick-first-row (send first-row-perm 'brother)))
                     #t))))
      (pick-first-row (gen-perms mat)))))

(define* all? (subr M ((subr M (row) bool) mat) bool)
  (lambda (ok? lst)
    (letrec ((_-*- (subr M (mat) bool)
               (lambda (lst)
                 (or (null? lst)
                     (and (ok? (car lst))
                          (_-*- (cdr lst)))))))
      (_-*- lst))))

; Extended Euclidean algorithm.
; (extended-gcd a b cont) computes the gcd of a and b, and expresses it
; as a linear combination of a and b.  It returns calling cont via
;       (cont gcd a-coef b-coef)
; where gcd is the GCD and is equal to a-coef * a + b-coef * b.
(define extended-gcd (subr M (int int (subr M (int int int) int)) int)
  (let ((n->sgn/abs
         (lambda ((x int) (cont (subr M (int int) int)))
           (if (>= x 0)
               (cont 1 x)
               (cont -1 (- 0 x))))))
    (lambda (a b cont)
      (n->sgn/abs a
                  (lambda ((p-a int) (p int))
                    (n->sgn/abs b
                                (lambda ((q-b int) (q int))
                                  (letrec ((_-*- (subr M (int int int int int int) int)
                                             (lambda (p p-a p-b q q-a q-b)
                                               (if (= q 0)
                                                   (cont p p-a p-b)
                                                   (let ((mult
                                                          (div p q)))
                                                     (_-*- q
                                                           q-a
                                                           q-b
                                                           (- p (* mult q))
                                                           (- p-a (* mult q-a))
                                                           (- p-b (* mult q-b))))))))
                                    (_-*- p p-a 0 q 0 q-b)))))))))

;; The operations on the base field, as `make-modular` hands them to a maker.
(define-type (maker (t type))
  (subr M (int int (subr M (int) bool) (subr M (int int) int) (subr M (int) int) (subr M (int int) int) (subr M (int) int)) t))

; Given a prime number P, return a procedure which, given a `maker' procedure,
; calls it on the operations for the field Z/PZ.
(define make-modular (poly ((t type)) (subr M (int) (subr M ((maker t)) t)))
  (plambda ((t type)) (lambda (modulus)
    (let* ((reduce
            (lambda ((x int))
              (mod x modulus)))
           (coef-zero?
            (lambda ((x int))
              (= (reduce x) 0)))
           (coef-+
            (lambda ((x int) (y int))
              (reduce (+ x y))))
           (coef-negate
            (lambda ((x int))
              (reduce (- 0 x))))
           (coef-*
            (lambda ((x int) (y int))
              (reduce (* x y))))
           (coef-recip
            (let ((inverses
                   (proc->vector (- modulus 1)
                                 (lambda ((i int))
                                   (extended-gcd (+ i 1)
                                                 modulus
                                                 (lambda ((gcd int) (inverse int) (ignore int))
                                                   inverse))))))
              ; Coef-recip.
              (lambda ((x int))
                (let ((x
                       (reduce x)))
                  (array-ref inverses (- x 1)))))))
      (lambda ((maker (maker t)))
        (maker 0    ; coef-zero
               1            ; coef-one
               coef-zero?
               coef-+
               coef-negate
               coef-*
               coef-recip))))))

; Given elements and operations on the base field, return a procedure which
; computes the row-reduced version of a matrix over that field.  The result
; is a list of rows where the first non-zero entry in each row is a 1 (in
; the coefficient field) and occurs to the right of all the leading non-zero
; entries of previous rows.  In particular, the number of rows is the rank
; of the original matrix, and they have the same row-space.
; The items related to the base field which are needed are:
;       coef-zero       additive identity
;       coef-one        multiplicative identity
;       coef-zero?      test for additive identity
;       coef-+          addition (two args)
;       coef-negate     additive inverse
;       coef-*          multiplication (two args)
;       coef-recip      multiplicative inverse
; Note, matricies are stored as lists of rows (i.e., lists of lists).
(define make-row-reduce (maker (subr M (mat) mat))
  (lambda (coef-zero coef-one coef-zero? coef-+ coef-negate coef-* coef-recip)
    (lambda ((mat mat))
      (letrec ((_-*- (subr M (mat) mat)
                 (lambda (mat)
                   (if (or (null? mat)
                           (null? (car mat)))
                       nil
                       (letrec ((_-**- (subr M (mat mat) mat)
                                  (lambda (in out)
                                    (if (null? in)
                                        (map
                                         (lambda ((x row))
                                           (the row (cons coef-zero x)))
                                         (_-*- out))
                                        (let* ((prow
                                                (car in))
                                               (pivot
                                                (car prow))
                                               (prest
                                                (cdr prow))
                                               (in
                                                (cdr in)))
                                          (if (coef-zero? pivot)
                                              (_-**- in
                                                     (cons prest out))
                                              (let ((zap-row
                                                     (map
                                                      (let ((mult
                                                             (coef-recip pivot)))
                                                        (lambda ((x int))
                                                          (coef-* mult x)))
                                                      prest)))
                                                (cons (cons coef-one zap-row)
                                                      (map
                                                       (lambda ((x row))
                                                         (the row (cons coef-zero x)))
                                                       (_-*-
                                                        (fold in
                                                              (lambda ((row row) (mat mat))
                                                                (cons
                                                                 (let ((first-col
                                                                        (car row))
                                                                       (rest-row
                                                                        (cdr row)))
                                                                   (if (coef-zero? first-col)
                                                                       rest-row
                                                                       (map2
                                                                        (let ((mult
                                                                               (coef-negate first-col)))
                                                                          (lambda ((f int) (z int))
                                                                            (coef-+ f
                                                                                    (coef-* mult z))))
                                                                        rest-row
                                                                        zap-row)))
                                                                 mat))
                                                              out)))))))))))
                         (_-**- mat nil))))))
        (_-*- mat)))))

; Given elements and operations on the base field, return a procedure which
; when given a matrix and a vector tests to see if the vector is in the
; row-space of the matrix.  This returned function is curried.
; The items related to the base field which are needed are:
;       coef-zero       additive identity
;       coef-one        multiplicative identity
;       coef-zero?      test for additive identity
;       coef-+          addition (two args)
;       coef-negate     additive inverse
;       coef-*          multiplication (two args)
;       coef-recip      multiplicative inverse
; Note, matricies are stored as lists of rows (i.e., lists of lists).
(define make-in-row-space? (maker (subr M (mat) (subr M (row) bool)))
  (lambda (coef-zero coef-one coef-zero? coef-+ coef-negate coef-* coef-recip)
    (let ((row-reduce
           (make-row-reduce coef-zero
                            coef-one
                            coef-zero?
                            coef-+
                            coef-negate
                            coef-*
                            coef-recip)))
      (lambda ((mat mat))
        (let ((mat
               (row-reduce mat)))
          (lambda ((row row))
            (letrec ((_-*- (subr M (row mat) bool)
                       (lambda (row mat)
                         (if (null? row)
                             #t
                             (let ((r-first
                                    (car row))
                                   (r-rest
                                    (cdr row)))
                               (cond ((coef-zero? r-first)
                                      (_-*- r-rest
                                            ((proj map row row) cdr
                                             (if (or (null? mat)
                                                     (coef-zero? (car (car mat))))
                                                 mat
                                                 (cdr mat)))))
                                     ((null? mat)
                                      #f)
                                     (else
                                      (let* ((zap-row
                                              (car mat))
                                             (z-first
                                              (car zap-row))
                                             (z-rest
                                              (cdr zap-row))
                                             (mat
                                              (cdr mat)))
                                        (if (coef-zero? z-first)
                                            #f
                                            (_-*-
                                             (map2
                                              (let ((mult
                                                     (coef-negate r-first)))
                                                (lambda ((r int) (z int))
                                                  (coef-+ r
                                                          (coef-* mult z))))
                                              r-rest
                                              z-rest)
                                             ((proj map row row) cdr mat)))))))))))
              (_-*- row mat))))))))

; Given a prime number, return a procedure which takes integer matricies
; and returns their row-reduced form, modulo the prime.
(define make-modular-row-reduce (subr M (int) (subr M (mat) mat))
  (lambda (modulus)
    (((proj make-modular (subr M (mat) mat)) modulus)
     make-row-reduce)))

(define make-modular-in-row-space? (subr M (int) (subr M (mat) (subr M (row) bool)))
  (lambda (modulus)
    (((proj make-modular (subr M (mat) (subr M (row) bool))) modulus)
     make-in-row-space?)))

; Given a bound, find a prime greater than the bound.
(define* find-prime (subr M (int) int)
  (lambda (bound)
    (let* ((primes
            (the row (cons 2 nil)))
           (last
            (chez-box primes))
           (is-next-prime?
            (lambda ((trial int))
              (letrec ((_-*- (subr M (row) bool)
                         (lambda (primes)
                           (or (null? primes)
                               (let ((p
                                      (car primes)))
                                 (or (< trial (* p p))
                                     (and (not (= (mod trial p) 0))
                                          (_-*- (cdr primes)))))))))
                (_-*- primes)))))
      (if (> 2 bound)
          2
          (letrec ((_-*- (subr M (int) int)
                     (lambda (trial)
                       (if (is-next-prime? trial)
                           (let ((entry
                                  (the row (cons trial nil))))
                             (begin
                               (set-cdr! (chez-unbox last) entry)
                               (chez-set-box! last entry)
                               (if (> trial bound)
                                   trial
                                   (_-*- (+ trial 2)))))
                           (_-*- (+ trial 2))))))
            (_-*- 3))))))

; Given the size of a square matrix consisting only of +1's and -1's,
; return an upper bound on the determinant.
(define* det-upper-bound (subr M (int) int)
  (lambda (size)
    (let ((main-part
           (expt size
                 (div size 2))))
      (if (even? size)
          main-part
          (* main-part
             (letrec ((do-loop (subr M (int) int)
                        (lambda (i) (if (>= (* i i) size) i (do-loop (+ i 1))))))
               (do-loop 0)))))))

; The first fold-over-rows is slower than the second one, but folds
; over rows in lexical order (large to small).
(define* fold-over-rows (subr M (int (subr M (row mat) mat) mat) mat)
  (lambda (number-of-cols folder state)
    (if (= number-of-cols 0)
        (folder nil
                state)
        (fold-over-rows (- number-of-cols 1)
                        (lambda ((tail row) (state mat))
                          (folder (cons -1 tail)
                                  state))
                        (fold-over-rows (- number-of-cols 1)
                                        (lambda ((tail row) (state mat))
                                          (folder (cons 1 tail)
                                                  state))
                                        state)))))

(define-type tests (listof (subr M (row) bool) @heap))

; Fold over subsets of a given size.
(define* fold-over-subs-of-size (subr M (mat int (subr M (mat tests) tests) tests) tests)
  (lambda (universe size folder state)
    (let ((usize
           (list-length universe)))
      (if (< usize size)
          state
          (letrec ((_-*- (subr M (int mat (subr M (mat tests) tests) int tests) tests)
                     (lambda (size universe folder csize state)
                       (cond ((= csize 0)
                              (folder universe state))
                             ((= size 0)
                              (folder nil state))
                             (else
                              (let ((first-u
                                     (car universe))
                                    (rest-u
                                     (cdr universe)))
                                (_-*- size
                                      rest-u
                                      folder
                                      (- csize 1)
                                      (_-*- (- size 1)
                                            rest-u
                                            (lambda ((tail mat) (state tests))
                                              (folder (cons first-u tail)
                                                      state))
                                            csize
                                            state))))))))
            (_-*- size universe folder (- usize size) state))))))

(define* remove-in-order (subr M ((subr M (row) bool) mat) mat)
  (lambda (remove? lst)
    (reverse
     (fold lst
           (lambda ((e row) (lst mat))
             (if (remove? e)
                 lst
                 (cons e lst)))
           nil))))

;; What `go-folder` keeps: the list (bsize blen . blist).
(define-datatype entry (a-mat mat) (ellipsis string))
(define-type state (pairof int (pairof int (listof entry @heap) @heap) @heap))

; Fold over all maximal matrices.
(define* go (subr M (int int (subr M (mat state) state) state) state)
  (lambda (number-of-cols inv-size folder state)
    (let* ((in-row-space?
            (make-modular-in-row-space?
             (find-prime
              (det-upper-bound inv-size))))
           (make-tester
            (lambda ((mat mat))
              (let ((tests
                     (let ((old-mat
                            (cdr mat))
                           (new-row
                            (car mat)))
                       (fold-over-subs-of-size old-mat
                                               (- inv-size 2)
                                               (lambda ((sub mat) (tests tests))
                                                 (cons
                                                  (in-row-space?
                                                   (cons new-row sub))
                                                  tests))
                                               nil))))
                (lambda ((row row))
                  (letrec ((_-*- (subr M (tests) bool)
                             (lambda (tests)
                               (and (not (null? tests))
                                    (or ((car tests) row)
                                        (_-*- (cdr tests)))))))
                    (_-*- tests))))))
           (all-rows  ; all rows starting with +1 in decreasing order
            (fold
             (fold-over-rows (- number-of-cols 1)
                             cons
                             nil)
             (lambda ((row row) (rows mat))
               (cons (cons 1 row)
                     rows))
             nil)))
      (letrec ((_-*- (subr M (int mat mat state) state)
                 (lambda (number-of-rows rev-mat possible-future state)
                   (let ((zulu-future
                          (remove-in-order
                           (if (< number-of-rows inv-size)
                               (in-row-space? rev-mat)
                               (make-tester rev-mat))
                           possible-future)))
                     (if (null? zulu-future)
                         (folder (reverse rev-mat)
                                 state)
                         (letrec ((_-**- (subr M (mat state) state)
                                    (lambda (zulu-future state)
                                      (if (null? zulu-future)
                                          state
                                          (let ((rest-of-future
                                                 (cdr zulu-future)))
                                            (_-**- rest-of-future
                                                   (let* ((first
                                                           (car zulu-future))
                                                          (new-rev-mat
                                                           (the mat (cons first rev-mat))))
                                                     (if (maximal? (reverse new-rev-mat))
                                                         (_-*- (+ number-of-rows 1)
                                                               new-rev-mat
                                                               rest-of-future
                                                               state)
                                                         state))))))))
                           (_-**- zulu-future state)))))))
        (_-*- 1 (cons (car all-rows) nil) (cdr all-rows) state)))))

(define* go-folder (subr M (mat state) state)
  (lambda (mat bsize.blen.blist)
    (let ((bsize
           (car bsize.blen.blist))
          (size
           (list-length mat)))
      (if (< size bsize)
          bsize.blen.blist
          (let ((blen
                 (car (cdr bsize.blen.blist)))
                (blist
                 (cdr (cdr bsize.blen.blist))))
            (if (= size bsize)
                (let ((blen
                       (+ blen 1)))
                  (cons bsize
                        (cons blen
                              (cond ((< blen 3000)
                                     (cons (a-mat mat) blist))
                                    ((= blen 3000)
                                     (cons (ellipsis "...") blist))
                                    (else
                                     blist)))))
                (cons size (cons 1 (cons (a-mat mat) nil)))))))))

(define* really-go (subr M (int int) (listof entry @heap))
  (lambda (number-of-cols inv-size)
    (cdr (cdr
          (go number-of-cols
              inv-size
              go-folder
              (cons -1 (cons -1 nil)))))))

;; The result as a datum, to print as Larceny does.
(define* row->datum (subr M (row) datum)
  (lambda (r) (if (null? r) nil (cons (car r) (row->datum (cdr r))))))
(define* mat->datum (subr M (mat) datum)
  (lambda (m) (if (null? m) nil (cons (row->datum (car m)) (mat->datum (cdr m))))))
(define* entries->datum (subr M ((listof entry @heap)) datum)
  (lambda (es)
    (if (null? es)
        nil
        (cons (tagcase (car es) (a-mat (m) (mat->datum m)) (ellipsis (s) s))
              (entries->datum (cdr es))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 5)
(define input2 int 5)
(define iterations int 2500)

(define* run (subr M (int (listof entry @heap)) (listof entry @heap))
  (lambda (i result) (if (= i 0) result (run (- i 1) (really-go input1 input2)))))
(entries->datum (run iterations nil))
