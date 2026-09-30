;;; RATIO-REGIONS -- Ratio Regions, an image segmentation/contour finding
;;; technique, by a reduction to max flow (preflow-push with periodic
;;; relabeling and a wave-based heuristic for scheduling pushes and lifts).
;;;
;;; Translated from Jeff Siskind's Scheme code by Stephen Weeks
;;; (sweeks@sweeks.com). Jeff Siskind's description: "It is an
;;; implementation of Ratio Regions, an image segmentation/contour finding
;;; technique due to Ingemar Cox, Satish Rao, and Yu Zhong. The algorithm is
;;; a reduction to max flow, an unpublished technique that Satish described
;;; to me. Peter Blicher originally implemented this via a translation to
;;; Andrew Goldberg's generic max-flow code. I've reimplemented it,
;;; specializing the max-flow algorithm to the particular graphs that are
;;; produced by Satish's reduction instead of using Andrew's code. The
;;; max-flow algorithm is preflow-push with periodic relabeling and a
;;; wave-based heuristic for scheduling pushes and lifts due to Sebastien
;;; Roy."
;;;
;;; From MLton's benchmark suite (benchmark/tests/ratio-regions.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. MLton's driver was not fetched; the
;;; input, 30 iterations of `doit 24` (a 24 by 24 image), is this port's.
;;; Answer: 144, the number of pixels inside the min cut (`min_cut`'s
;;; matrix, counted: the original computes it and drops it).
;;;
;;; What changed:
;;; - `rao_ratio_region`'s local procedures, which in SML close over its
;;;   fourteen locals (the capacities, flows, heights, excesses, marks and
;;;   the wave queue), are top-level procedures taking those locals as one
;;;   record, `rr` (what closure conversion makes of them), and
;;;   `preflow_push`'s, which also close over `v`, take `v` too. A closure
;;;   over more than eight variables was then declined by the register
;;;   compiler (no longer, since 2026-09-29: the rest go as a list).
;;; - `rr` is a bloblet read by accessor procedures (`rr-h`, …), not a
;;;   product read by `extract`: a procedure that calls (inlines) one that
;;;   `extract`s from a product parameter is declined by the register
;;;   compiler (reported, with a reproduction). Its constructor, `make-rr`,
;;;   gives `make-bloblet` fifteen operands, which the register compiler
;;;   declined too, until 2026-09-29.
;;; - `'a matrix` (`Matrix of 'a array array`) is the array of arrays
;;;   itself, without the one-constructor box; its operations are
;;;   polymorphic, used at int and bool.
;;; - `print` and `write_char` do nothing, as in the original; `pormat`
;;;   still walks its control string and makes `Int.toString`'s strings.
;;; - `raise Fail` (never raised) aborts to a tag with no prompt: an error.
;;; - The unused `some_n` is left out, and the aliases (`vector_ref`, …)
;;;   are FX-26's own operations.

(define-type ints (listof int @heap))
(define-type (matrix (t type)) (arrayof (arrayof t @heap) @heap))
(define-type point (productof (x int) (y int)))
(define-type points (listof point @heap))

;; An uncaught exception: an abort to a tag no prompt is for.
(define fail-tag (prompt-tag unit string pure @f) (make-continuation-prompt-tag))
(define* fail (subr (goto @f) (string) void)
  (lambda (s) (abort-current-continuation fail-tag s)))

(define-effect rreff (maxeff (read @heap) (write @heap) (alloc @heap) spin (goto @f) (read @globals)))

(define print (subr pure (string) unit) (lambda (s) #u))
(define write-char (subr pure (char) unit) (lambda (c) #u))

(define* doo (subr rreff (int (subr rreff (int) unit)) unit)
  (lambda (max f)
    (letrec ((loop (subr rreff (int) unit)
               (lambda (i) (if (>= i max) #u (begin (f i) (loop (+ i 1)))))))
      (loop 0))))

(define zero (subr pure (int) bool) (lambda (x) (= x 0)))
(define negative (subr pure (int) bool) (lambda (x) (< x 0)))
(define positive (subr pure (int) bool) (lambda (x) (> x 0)))
(define int-min (subr pure (int int) int) (lambda (x y) (if (< x y) x y)))

(define* min (subr rreff (ints) int)
  (lambda (l)
    (if (null? l)
        (fail "min")
        (letrec ((loop (subr rreff (ints int) int)
                   (lambda (l min) (if (null? l) min (loop (cdr l) (int-min min (car l)))))))
          (loop (cdr l) (car l))))))

(define* every-n (subr rreff (int (subr rreff (int) bool)) bool)
  (lambda (n p)
    (letrec ((loop (subr rreff (int) bool) (lambda (i) (or (>= i n) (and (p i) (loop (+ i 1)))))))
      (loop 0))))

(define* some (subr rreff (points (subr rreff (point) bool)) bool)
  (lambda (l p) (and (not (null? l)) (or (p (car l)) (some (cdr l) p)))))

(define* some-vector (subr rreff ((arrayof points @heap) (subr rreff (points) bool)) bool)
  (lambda (v p)
    (letrec ((loop (subr rreff (int) bool)
               (lambda (i) (and (< i (array-length v)) (or (p (array-ref v i)) (loop (+ i 1)))))))
      (loop 0))))

(define* for-each (subr rreff (points (subr rreff (point) unit)) unit)
  (lambda (l f) (if (null? l) #u (begin (f (car l)) (for-each (cdr l) f)))))

(define make-matrix
  (poly ((t type)) (subr (maxeff (write @heap) (alloc @heap) spin) (int int t) (matrix t)))
  (plambda ((t type))
    (lambda ((m int) (n int) (a t))
      (let ((rows (the (matrix t) (make-array m (the (arrayof t @heap) (make-array 0 a))))))
        (letrec ((fill (subr (maxeff (write @heap) (alloc @heap) spin) (int) (matrix t))
                   (lambda (i) (if (>= i m) rows (begin (array-set! rows i (make-array n a)) (fill (+ i 1)))))))
          (fill 0))))))
(define matrix-rows (poly ((t type)) (subr pure ((matrix t)) int))
  (plambda ((t type)) (lambda ((a (matrix t))) (array-length a))))
(define matrix-columns (poly ((t type)) (subr (read @heap) ((matrix t)) int))
  (plambda ((t type)) (lambda ((a (matrix t))) (array-length (array-ref a 0)))))
(define matrix-ref (poly ((t type)) (subr (read @heap) ((matrix t) int int) t))
  (plambda ((t type)) (lambda ((a (matrix t)) (i int) (j int)) (array-ref (array-ref a i) j))))
(define matrix-set (poly ((t type)) (subr (maxeff (read @heap) (write @heap)) ((matrix t) int int t) unit))
  (plambda ((t type)) (lambda ((a (matrix t)) (i int) (j int) (x t)) (array-set! (array-ref a i) j x))))

(define-datatype pormat-value (pint int) (pstring string))
(define-type pvs (listof pormat-value @heap))

(define* pormat (subr rreff (string pvs) unit)
  (lambda (control-string values)
    (letrec ((loop (subr rreff (int pvs) unit)
               (lambda (i values)
                 (if (not (= i (string-length control-string)))
                     (let ((c (string-ref control-string i)))
                       (if (char=? c #\~)
                           (let ((c2 (string-ref control-string (+ i 1)))
                                 (other (lambda () (begin (write-char c) (loop (+ i 1) values)))))
                             (cond ((char=? c2 #\%) (begin (print "\n") (loop (+ i 2) values)))
                                   ((null? values) (other))
                                   ((char=? c2 #\s)
                                    (tagcase (car values)
                                      (pint (n) (begin (print (int->string n)) (loop (+ i 2) (cdr values))))
                                      (else v (other))))
                                   ((char=? c2 #\a)
                                    (tagcase (car values)
                                      (pstring (s) (begin (print s) (loop (+ i 2) (cdr values))))
                                      (else v (other))))
                                   (else (other))))
                           (begin (write-char c) (loop (+ i 1) values))))
                     #u))))
      (loop 0 values))))

;; The vertices are s, t, and (y,x).
;; C_RIGHT[y,x] is the capacity from (y,x) to (y,x+1) which is the same as the
;; capacity from (y,x+1) to (y,x).
;; C_DOWN[y,x] is the capacity from (y,x) to (y+1,x) which is the same as the
;; capacity from (y+1,x) to (y,x).
;; The capacity from s to (y,0), (0,x), (y,Y_1), (0,X_1) is implicitly
;; infinite.
;; The capacity from (x,y) to t is V*W[y,x].
;; F_RIGHT[y,x] is the preflow from (y,x) to (y,x+1) which is the negation of
;; the preflow from (y,x+1) to (y,x).
;; F_DOWN[y,x] is the preflow from (y,x) to (y+1,x) which is the negation of
;; the preflow from (y+1,x) to (y,x).
;; We do not record the preflow from s to (y,X_1), (y,0), (Y_1,x), and (0,x)
;; and from (y,X_1), (y,0), (Y_1,x), and (0,x) to s.
;; F_T[y,x] is the preflow from (y,x) to t.
;; We do not record the preflow from t to (y,x).
;; {C,F}_RIGHT[0:Y_1,0:X_2].
;; {C,F}_DOWN[0:Y_2,0:X_1].
;; F_T[0:Y_1,0:X_1]
;; For now, we will keep all capacities (and thus all preflows) as integers.
;; (CF_RIGHT y x) is the residual capacity from (y,x) to (y,x+1).
;; (CF_LEFT y x) is the residual capacity from (y,x) to (y,x_1).
;; (CF_DOWN y x) is the residual capacity from (y,x) to (y+1,x).
;; (CF_UP y x) is the residual capacity from (y,x) to (y_1,x).
;; We do not compute the residual capacities from s to (y,X_1), (y,0),
;; (Y_1,x), and (0,x) because they are all infinite.
;; We do not compute the residual capacities from (y,X_1), (y,0), (Y_1,x),
;; and (0,x) to s because they will never be used.
;; (CF_T y x) is the residual capacity from (y,x) to t.
;; We do not compute the residual capacity from t to (y,x) because it will
;; be used.
;; (EF_RIGHT? y x) is true if there is an edge from (y,x) to (y,x+1) in the
;; residual network.
;; (EF_LEFT? y x) is true if there is an edge from (y,x) to (y,x_1) in the
;; residual network.
;; (EF_DOWN? y x) is true if there is an edge from (y,x) to (y+1,x) in the
;; residual network.
;; (EF_UP? y x) is true if there is an edge from (y,x) to (y_1,x) in the
;; residual network.
;; (EF_T? y x) is true if there is an edge from (y,x) to t in the
;; residual network.
;; There are always edges in the residual network from s to (y,X_1), (y,0),
;; (Y_1,x), and (0,x).
;; We don't care whether there are edges in the residual network from
;; (y,X_1), (y,0), (Y_1,x), and (0,x) to s because they will never be used.
;; We don't care whether there are edges in the residual network from t to
;; (y,x) because they will never be used.

(define* positive-min (subr pure (int int) int) (lambda (x y) (if (negative x) y (int-min x y))))
(define* positive-minus (subr pure (int int) int) (lambda (x y) (if (negative x) x (- x y))))
(define* positive-plus (subr pure (int int) int) (lambda (x y) (if (negative x) x (+ x y))))

;; `rao_ratio_region`'s locals, which its procedures close over: a
;; bloblet, each field read by a procedure named for it.
(define-type rr
  (bloblet (fields (matrix int) (matrix int) (matrix int) int int (matrix int) (matrix int) (matrix int) (matrix int) (matrix int) (matrix bool) int int (arrayof points @heap)) @heap))
(define rr-c-right (subr (read @heap) (rr) (matrix int)) (lambda (s) (bloblet-ref s 0)))
(define rr-c-down (subr (read @heap) (rr) (matrix int)) (lambda (s) (bloblet-ref s 1)))
(define rr-w (subr (read @heap) (rr) (matrix int)) (lambda (s) (bloblet-ref s 2)))
(define rr-height (subr (read @heap) (rr) int) (lambda (s) (bloblet-ref s 3)))
(define rr-width (subr (read @heap) (rr) int) (lambda (s) (bloblet-ref s 4)))
(define rr-f-right (subr (read @heap) (rr) (matrix int)) (lambda (s) (bloblet-ref s 5)))
(define rr-f-down (subr (read @heap) (rr) (matrix int)) (lambda (s) (bloblet-ref s 6)))
(define rr-f-t (subr (read @heap) (rr) (matrix int)) (lambda (s) (bloblet-ref s 7)))
(define rr-h (subr (read @heap) (rr) (matrix int)) (lambda (s) (bloblet-ref s 8)))
(define rr-e (subr (read @heap) (rr) (matrix int)) (lambda (s) (bloblet-ref s 9)))
(define rr-marked (subr (read @heap) (rr) (matrix bool)) (lambda (s) (bloblet-ref s 10)))
(define rr-m1 (subr (read @heap) (rr) int) (lambda (s) (bloblet-ref s 11)))
(define rr-m2 (subr (read @heap) (rr) int) (lambda (s) (bloblet-ref s 12)))
(define rr-q (subr (read @heap) (rr) (arrayof points @heap)) (lambda (s) (bloblet-ref s 13)))

;; The locals made: fifteen operands to `make-bloblet`, past the eight
;; registers: the rest go as a list in the last.
(define* make-rr (subr rreff ((matrix int) (matrix int) (matrix int) int int) rr)
  (lambda (c-right c-down w height width)
    (the rr (make-bloblet 0 c-right c-down w height width
                          (make-matrix height (- width 1) 0)          ; f_right
                          (make-matrix (- height 1) width 0)          ; f_down
                          (make-matrix height width 0)                ; f_t
                          (make-matrix height width 0)                ; h
                          (make-matrix height width 0)                ; e
                          (make-matrix height width #f)               ; marked
                          (+ (* height width) 2)                      ; m1
                          (+ (* 2 (* height width)) 2)                ; m2
                          (the (arrayof points @heap)                 ; q
                               (make-array (+ (* 2 (* height width)) 3) nil))))))

(define* cf-right (subr rreff (rr int int) int)
  (lambda (s y x) (- (matrix-ref (rr-c-right s) y x) (matrix-ref (rr-f-right s) y x))))
(define* cf-left (subr rreff (rr int int) int)
  (lambda (s y x) (+ (matrix-ref (rr-c-right s) y (- x 1)) (matrix-ref (rr-f-right s) y (- x 1)))))
(define* cf-down (subr rreff (rr int int) int)
  (lambda (s y x) (- (matrix-ref (rr-c-down s) y x) (matrix-ref (rr-f-down s) y x))))
(define* cf-up (subr rreff (rr int int) int)
  (lambda (s y x) (+ (matrix-ref (rr-c-down s) (- y 1) x) (matrix-ref (rr-f-down s) (- y 1) x))))
(define* ef-right (subr rreff (rr int int) bool) (lambda (s y x) (positive (cf-right s y x))))
(define* ef-left (subr rreff (rr int int) bool) (lambda (s y x) (positive (cf-left s y x))))
(define* ef-down (subr rreff (rr int int) bool) (lambda (s y x) (positive (cf-down s y x))))
(define* ef-up (subr rreff (rr int int) bool) (lambda (s y x) (positive (cf-up s y x))))

;;; preflow_push's procedures, over `v` too.

(define* enqueue (subr rreff (rr int int) unit)
  (lambda (s y x)
    (let ((q (rr-q s)) (h (rr-h s)))
      (if (not (matrix-ref (rr-marked s) y x))
          (begin
            (array-set! q (matrix-ref h y x)
                        (the points (cons (product (x x) (y y)) (array-ref q (matrix-ref h y x)))))
            (matrix-set (rr-marked s) y x #t))
          #u))))
(define* cf-t (subr rreff (rr int int int) int)
  (lambda (s v y x) (- (* v (matrix-ref (rr-w s) y x)) (matrix-ref (rr-f-t s) y x))))
(define* ef-t (subr rreff (rr int int int) bool) (lambda (s v y x) (positive (cf-t s v y x))))
(define* can-push-right (subr rreff (rr int int) bool)
  (lambda (s y x)
    (let ((h (rr-h s)))
      (and (< x (- (rr-width s) 1))
           (not (zero (matrix-ref (rr-e s) y x)))
           (ef-right s y x)
           (= (matrix-ref h y x) (+ (matrix-ref h y (+ x 1)) 1))))))
(define* can-push-left (subr rreff (rr int int) bool)
  (lambda (s y x)
    (let ((h (rr-h s)))
      (and (> x 0)
           (not (zero (matrix-ref (rr-e s) y x)))
           (ef-left s y x)
           (= (matrix-ref h y x) (+ (matrix-ref h y (- x 1)) 1))))))
(define* can-push-down (subr rreff (rr int int) bool)
  (lambda (s y x)
    (let ((h (rr-h s)))
      (and (< y (- (rr-height s) 1))
           (not (zero (matrix-ref (rr-e s) y x)))
           (ef-down s y x)
           (= (matrix-ref h y x) (+ (matrix-ref h (+ y 1) x) 1))))))
(define* can-push-up (subr rreff (rr int int) bool)
  (lambda (s y x)
    (let ((h (rr-h s)))
      (and (> y 0)
           (not (zero (matrix-ref (rr-e s) y x)))
           (ef-up s y x)
           (= (matrix-ref h y x) (+ (matrix-ref h (- y 1) x) 1))))))
(define* can-push-t (subr rreff (rr int int int) bool)
  (lambda (s v y x)
    (and (not (zero (matrix-ref (rr-e s) y x)))
         (ef-t s v y x)
         (= (matrix-ref (rr-h s) y x) 1))))
(define* can-lift (subr rreff (rr int int int) bool)
  (lambda (s v y x)
    (let ((h (rr-h s)) (m1 (rr-m1 s)))
      (and (not (zero (matrix-ref (rr-e s) y x)))
           (if (= x (- (rr-width s) 1))
               (<= (matrix-ref h y x) m1)
               (or (not (ef-right s y x))
                   (<= (matrix-ref h y x) (matrix-ref h y (+ x 1)))))
           (if (= x 0)
               (<= (matrix-ref h y x) m1)
               (or (not (ef-left s y x))
                   (<= (matrix-ref h y x) (matrix-ref h y (- x 1)))))
           (if (= y (- (rr-height s) 1))
               (<= (matrix-ref h y x) m1)
               (or (not (ef-down s y x))
                   (<= (matrix-ref h y x) (matrix-ref h (+ y 1) x))))
           (if (= y 0)
               (<= (matrix-ref h y x) m1)
               (or (not (ef-up s y x))
                   (<= (matrix-ref h y x) (matrix-ref h (- y 1) x))))
           (or (not (ef-t s v y x)) (= (matrix-ref h y x) 0))))))
(define* push-right (subr rreff (rr int int) unit)
  (lambda (s y x)
    (let* ((e (rr-e s)) (f-right (rr-f-right s))
           (df-u-v (positive-min (matrix-ref e y x) (cf-right s y x))))
      (begin
        (matrix-set f-right y x (+ (matrix-ref f-right y x) df-u-v))
        (matrix-set e y x (positive-minus (matrix-ref e y x) df-u-v))
        (matrix-set e y (+ x 1) (positive-plus (matrix-ref e y (+ x 1)) df-u-v))
        (enqueue s y (+ x 1))))))
(define* push-left (subr rreff (rr int int) unit)
  (lambda (s y x)
    (let* ((e (rr-e s)) (f-right (rr-f-right s))
           (df-u-v (positive-min (matrix-ref e y x) (cf-left s y x))))
      (begin
        (matrix-set f-right y (- x 1) (- (matrix-ref f-right y (- x 1)) df-u-v))
        (matrix-set e y x (positive-minus (matrix-ref e y x) df-u-v))
        (matrix-set e y (- x 1) (positive-plus (matrix-ref e y (- x 1)) df-u-v))
        (enqueue s y (- x 1))))))
(define* push-down (subr rreff (rr int int) unit)
  (lambda (s y x)
    (let* ((e (rr-e s)) (f-down (rr-f-down s))
           (df-u-v (positive-min (matrix-ref e y x) (cf-down s y x))))
      (begin
        (matrix-set f-down y x (+ (matrix-ref f-down y x) df-u-v))
        (matrix-set e y x (positive-minus (matrix-ref e y x) df-u-v))
        (matrix-set e (+ y 1) x (positive-plus (matrix-ref e (+ y 1) x) df-u-v))
        (enqueue s (+ y 1) x)))))
(define* push-up (subr rreff (rr int int) unit)
  (lambda (s y x)
    (let* ((e (rr-e s)) (f-down (rr-f-down s))
           (df-u-v (positive-min (matrix-ref e y x) (cf-up s y x))))
      (begin
        (matrix-set f-down (- y 1) x (- (matrix-ref f-down (- y 1) x) df-u-v))
        (matrix-set e y x (positive-minus (matrix-ref e y x) df-u-v))
        (matrix-set e (- y 1) x (positive-plus (matrix-ref e (- y 1) x) df-u-v))
        (enqueue s (- y 1) x)))))
(define* push-t (subr rreff (rr int int int) unit)
  (lambda (s v y x)
    (let* ((e (rr-e s)) (f-t (rr-f-t s))
           (df-u-v (positive-min (matrix-ref e y x) (cf-t s v y x))))
      (begin
        (matrix-set f-t y x (+ (matrix-ref f-t y x) df-u-v))
        (matrix-set e y x (positive-minus (matrix-ref e y x) df-u-v))))))
(define* lift (subr rreff (rr int int int) unit)
  (lambda (s v y x)
    (let ((h (rr-h s)) (m1 (rr-m1 s)) (m2 (rr-m2 s)))
      (matrix-set h y x
        (+ 1 (min (list (if (= x (- (rr-width s) 1))
                            m1
                            (if (ef-right s y x) (matrix-ref h y (+ x 1)) m2))
                        (if (= x 0)
                            m1
                            (if (ef-left s y x) (matrix-ref h y (- x 1)) m2))
                        (if (= y (- (rr-height s) 1))
                            m1
                            (if (ef-down s y x) (matrix-ref h (+ y 1) x) m2))
                        (if (= y 0)
                            m1
                            (if (ef-up s y x) (matrix-ref h (- y 1) x) m2))
                        (if (ef-t s v y x) 0 m2))))))))

(define-datatype queue (qnil) (qcons point (ref queue @heap)))

(define* relabel (subr rreff (rr int) unit)
  (lambda (s v)
    (let ((q (the (ref queue @heap) (new (qnil))))
          (tail (the (ref queue @heap) (new (qnil))))
          (h (rr-h s))
          (marked (rr-marked s))
          (height (rr-height s))
          (width (rr-width s)))
      (letrec ((null (subr rreff ((ref queue @heap)) bool)
                 (lambda (q) (tagcase (get q) (qnil () #t) (else c #f))))
               (enqueue (subr rreff (int int int) unit)
                 (lambda (y x value)
                   (if (< value (matrix-ref h y x))
                       (begin
                         (matrix-set h y x value)
                         (if (not (matrix-ref marked y x))
                             (begin
                               (matrix-set marked y x #t)
                               (tagcase (get tail)
                                 (qnil ()
                                   (begin (set tail (qcons (product (x x) (y y)) (new (qnil))))
                                          (set q (get tail))))
                                 (qcons (p cdr)
                                   (begin (set cdr (qcons (product (x x) (y y)) (new (qnil))))
                                          (set tail (get cdr))))))
                             #u))
                       #u)))
               (dequeue (subr rreff () point)
                 (lambda ()
                   (tagcase (get q)
                     (qnil () (fail "dequeue"))
                     (qcons (p rest)
                       (begin
                         (matrix-set marked (extract p y) (extract p x) #f)
                         (set q (get rest))
                         (if (null q) (set tail (qnil)) #u)
                         p)))))
               (loop (subr rreff () unit)
                 (lambda ()
                   (if (not (null q))
                       (begin
                         (let* ((p (dequeue))
                                (x (extract p x))
                                (y (extract p y))
                                (value (+ (matrix-ref h y x) 1)))
                           (begin
                             (if (and (> x 0) (ef-right s y (- x 1))) (enqueue y (- x 1) value) #u)
                             (if (and (< x (- width 1)) (ef-left s y (+ x 1))) (enqueue y (+ x 1) value) #u)
                             (if (and (> y 0) (ef-down s (- y 1) x)) (enqueue (- y 1) x value) #u)
                             (if (and (< y (- height 1)) (ef-up s (+ y 1) x)) (enqueue (+ y 1) x value) #u)))
                         (loop))
                       #u))))
        (begin
          (doo height (lambda ((y int))
                        (doo width (lambda ((x int))
                                     (begin (matrix-set h y x (rr-m1 s))
                                            (matrix-set marked y x #f))))))
          (doo height (lambda ((y int))
                        (doo width (lambda ((x int))
                                     (if (and (ef-t s v y x) (> (matrix-ref h y x) 1))
                                         (enqueue y x 1)
                                         #u)))))
          (loop))))))

(define* plural (subr pure (int string) pormat-value)
  (lambda (n suffix) (pstring (if (= n 1) "" suffix))))

(define* preflow-push (subr rreff (rr int) unit)
  (lambda (s v)
    (let ((height (rr-height s)) (width (rr-width s))
          (e (rr-e s)) (h (rr-h s)) (q (rr-q s)))
      (begin
        (doo height (lambda ((y int))
                      (doo width (lambda ((x int))
                                   (begin (matrix-set e y x 0)
                                          (matrix-set (rr-f-t s) y x 0))))))
        (doo height (lambda ((y int))
                      (doo (- width 1) (lambda ((x int)) (matrix-set (rr-f-right s) y x 0)))))
        (doo (- height 1) (lambda ((y int))
                            (doo width (lambda ((x int)) (matrix-set (rr-f-down s) y x 0)))))
        (doo height (lambda ((y int))
                      (begin (matrix-set e y (- width 1) -1)
                             (matrix-set e y 0 -1))))
        (doo (- width 1) (lambda ((x int))
                           (begin (matrix-set e (- height 1) x -1)
                                  (matrix-set e 0 x -1))))
        (let ((pushes (the (ref int @heap) (new 0)))
              (lifts (the (ref int @heap) (new 0)))
              (relabels (the (ref int @heap) (new 0))))
          (letrec ((report (subr rreff (string int) unit)
                     (lambda (control i)
                       (pormat control
                               (list (pint (get pushes))
                                     (plural (get pushes) "es")
                                     (pint (get lifts))
                                     (plural (get lifts) "s")
                                     (pint (get relabels))
                                     (plural (get relabels) "s")
                                     (pint i)
                                     (plural i "s")))))
                   (loop (subr rreff (int bool) unit)
                     (lambda (i p)
                       (if (and (zero (modulo i 6)) (not p))
                           (begin
                             (relabel s v)
                             (set relabels (+ (get relabels) 1))
                             (if (every-n height (lambda ((y int))
                                                   (every-n width (lambda ((x int))
                                                                    (or (zero (matrix-ref e y x))
                                                                        (= (matrix-ref h y x) (rr-m1 s)))))))
                                 ;; Every vertex with excess capacity is not reachable from the sink in
                                 ;; the inverse residual network. So terminate early because we have
                                 ;; already found a min cut. In this case, the preflows and excess
                                 ;; capacities will not be correct. But the cut is indicated by the
                                 ;; heights. Vertices reachable from the source have height
                                 ;; HEIGHT * WIDTH + 2 while vertices reachable from the sink have
                                 ;; smaller height. Early termination is necessary with relabeling to
                                 ;; prevent an infinite loop. The loop arises because vertices that are
                                 ;; not reachable from the sink in the inverse residual network have
                                 ;; their height reset to HEIGHT * WIDTH + 2 by the relabeling
                                 ;; process. If there are such vertices with excess capacity, this is
                                 ;; not high enough for the excess capacity to be pushed back to the
                                 ;; perimeter. So after relabeling, vertices get lifted to try to push
                                 ;; excess capacity back to the perimeter but then a relabeling happens
                                 ;; to soon and foils this lifting. Terminating when all vertices with
                                 ;; excess capacity are not reachable from the sink in the inverse
                                 ;; residual network eliminates this problem.
                                 (report "~s push~a, ~s lift~a, ~s relabel~a, ~s wave~a, terminated early~%" i)
                                 ;; We need to rebuild the priority queue after relabeling since the
                                 ;; heights might have changed and the priority queue is indexed by
                                 ;; height. This also assumes that a relabel is done before any pushes
                                 ;; or lifts.
                                 (begin
                                   (doo (array-length q) (lambda ((k int)) (array-set! q k (the points nil))))
                                   (doo height (lambda ((y int))
                                                 (doo width (lambda ((x int)) (matrix-set (rr-marked s) y x #f)))))
                                   (doo height (lambda ((y int))
                                                 (doo width (lambda ((x int))
                                                              (if (not (zero (matrix-ref e y x))) (enqueue s y x) #u)))))
                                   (loop i #t))))
                           (if (some-vector q (lambda ((ps points))
                                                (some ps (lambda ((p point))
                                                           (let ((x (extract p x)) (y (extract p y)))
                                                             (or (can-push-right s y x)
                                                                 (can-push-left s y x)
                                                                 (can-push-down s y x)
                                                                 (can-push-up s y x)
                                                                 (can-push-t s v y x)
                                                                 (can-lift s v y x)))))))
                               (begin
                                 (letrec ((loop (subr rreff (int) unit)
                                            (lambda (k)
                                              (if (not (negative k))
                                                  (begin
                                                    (let ((ps (array-ref q k)))
                                                      (begin
                                                        (array-set! q k (the points nil))
                                                        (for-each ps (lambda ((p point))
                                                                       (matrix-set (rr-marked s) (extract p y) (extract p x) #f)))
                                                        (for-each ps (lambda ((p point))
                                                                       (let ((x (extract p x)) (y (extract p y)))
                                                                         (begin
                                                                           (if (can-push-right s y x)
                                                                               (begin (set pushes (+ (get pushes) 1)) (push-right s y x))
                                                                               #u)
                                                                           (if (can-push-left s y x)
                                                                               (begin (set pushes (+ (get pushes) 1)) (push-left s y x))
                                                                               #u)
                                                                           (if (can-push-down s y x)
                                                                               (begin (set pushes (+ (get pushes) 1)) (push-down s y x))
                                                                               #u)
                                                                           (if (can-push-up s y x)
                                                                               (begin (set pushes (+ (get pushes) 1)) (push-up s y x))
                                                                               #u)
                                                                           (if (can-push-t s v y x)
                                                                               (begin (set pushes (+ (get pushes) 1)) (push-t s v y x))
                                                                               #u)
                                                                           (if (can-lift s v y x)
                                                                               (begin (set lifts (+ (get lifts) 1)) (lift s v y x))
                                                                               #u)
                                                                           (if (not (zero (matrix-ref e y x))) (enqueue s y x) #u)))))))
                                                    (loop (- k 1)))
                                                  #u))))
                                   (loop (- (array-length q) 1)))
                                 (loop (+ i 1) #f))
                               ;; This is so MIN_CUT and MIN_CUT_INCLUDES_EVERY_EDGE_TO_T work.
                               (begin
                                 (relabel s v)
                                 (set relabels (+ (get relabels) 1))
                                 (report "~s push~a, ~s lift~a, ~s relabel~a, ~s wave~a~%" i)))))))
            (loop 0 #f)))))))

;; This requires that a relabel was done immediately before returning from
;; PREFLOW_PUSH.
(define* min-cut-includes-every-edge-to-t (subr rreff (rr) bool)
  (lambda (s)
    (every-n (rr-height s) (lambda ((y int))
                                  (every-n (rr-width s) (lambda ((x int))
                                                               (= (matrix-ref (rr-h s) y x) (rr-m1 s))))))))

;; This requires that a relabel was done immediately before returning from
;; PREFLOW_PUSH (Array.tabulate of Array.tabulate).
(define* min-cut (subr rreff (rr) (matrix bool))
  (lambda (s)
    (let* ((height (rr-height s)) (width (rr-width s))
           (cut (the (matrix bool) (make-array height (the (arrayof bool @heap) (make-array 0 #f))))))
      (begin
        (doo height (lambda ((y int))
                      (let ((row (the (arrayof bool @heap) (make-array width #f))))
                        (begin
                          (doo width (lambda ((x int))
                                       (array-set! row x (not (= (matrix-ref (rr-h s) y x) (rr-m1 s))))))
                          (array-set! cut y row)))))
        cut))))

(define* rao-ratio-region (subr rreff ((matrix int) (matrix int) (matrix int) int) (matrix bool))
  (lambda (c-right c-down w lg-max-v)
    (let* ((height (matrix-rows w))
           (width (matrix-columns w))
           (s (make-rr c-right c-down w height width)))
      (letrec ((loop (subr rreff (int int) (matrix bool))
                 (lambda (lg-v v-max)
                   (if (negative lg-v)
                       (begin
                         (pormat "V-MAX=~s~%" (the pvs (cons (pint v-max) nil)))
                         (preflow-push s (+ v-max 1))
                         (min-cut s))
                       (let ((v (+ v-max
                                   (letrec ((loop (subr rreff (int int) int)
                                              (lambda (i c) (if (zero i) c (loop (- i 1) (+ c c))))))
                                     (loop lg-v 1)))))
                         (begin
                           (pormat "LG-V=~s, V-MAX=~s, V=~s~%"
                                   (list (pint lg-v) (pint v-max) (pint v)))
                           (preflow-push s v)
                           (loop (- lg-v 1)
                                 (if (min-cut-includes-every-edge-to-t s) v v-max))))))))
        (loop lg-max-v 0)))))

(define* doit (subr rreff (int) (matrix bool))
  (lambda (n)
    (let* ((height n)
           (width n)
           (lg-max-v 15)
           (c-right (make-matrix height (- width 1) -1))
           (c-down (make-matrix (- height 1) width -1)))
      (begin
        (doo height (lambda ((y int))
                      (doo (- width 1) (lambda ((x int))
                                         (matrix-set c-right y x
                                           (if (and (>= y (quotient height 4))
                                                    (< y (quotient (* 3 height) 4))
                                                    (or (= x (- (quotient width 4) 1))
                                                        (= x (- (quotient (* 3 width) 4) 1))))
                                               1
                                               128))))))
        (doo (- height 1) (lambda ((y int))
                            (doo width (lambda ((x int))
                                         (matrix-set c-down y x
                                           (if (and (>= x (quotient width 4))
                                                    (< x (quotient (* 3 width) 4))
                                                    (or (= y (- (quotient height 4) 1))
                                                        (= y (- (quotient (* 3 height) 4) 1))))
                                               1
                                               128))))))
        (rao-ratio-region c-right c-down (make-matrix height width 1) lg-max-v)))))

;; The pixels inside the cut.
(define* count-cut (subr rreff ((matrix bool)) int)
  (lambda (cut)
    (let ((n (the (ref int @heap) (new 0))))
      (begin
        (doo (array-length cut) (lambda ((y int))
                                  (let ((row (array-ref cut y)))
                                    (doo (array-length row) (lambda ((x int))
                                                              (if (array-ref row x) (set n (+ (get n) 1)) #u))))))
        (get n)))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define input int 24)
(define iterations int 30)

(define* run (subr rreff (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (count-cut (doit input))))))
(run iterations 0)
