;;; GENERATOR -- Generator benchmark.
;;;
;;; Uses an example taken from the SRFI 41 document.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/generator.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (go 250).
;;; Answer: (135 324 351).
;;;
;;; FX-26 has no (scheme generator): `make-iota-generator` and
;;; `make-range-generator` are Larceny's (SRFI 121's reference
;;; implementation, lib/SRFI/srfi/121.body.scm), closures over variables
;;; they assign, here refs. What differs, and why:
;;; - The end of a generator, Scheme's eof object, is a fixnum none of
;;;   these generators yields: the least one. A generator is then a
;;;   procedure of no arguments returning an int, as in Larceny, where the
;;;   eof object is also an immediate; `eof-object?` compares with it.
;;; - The benchmark counts n with `(make-iota-generator +inf.0 1)`, a count
;;;   that never runs out; FX-26 has no flonums, so the count is the
;;;   greatest fixnum, which runs out no sooner than 2^60 values.
;;; - `set!` of the local `count` is a ref, `do` a named loop, and
;;;   `call-with-current-continuation` is `cwcc`.

(define-type gen (subr (maxeff (read @heap) (write @heap) (read (globals eof))) () int))
(define-type ints (listof int @heap))

(define eof int (- -1152921504606846975 1))   ; the least fixnum
(define greatest-fixnum int 1152921504606846975)
(define* eof-object? (subr pure (int) bool) (lambda (x) (= x eof)))

;; make-iota-generator, as make-iota
(define* make-iota-generator (subr (alloc @heap) (int int int) gen)
  (lambda (count0 start0 step)
    (let ((count (the (ref int @heap) (new count0)))
          (start (the (ref int @heap) (new start0))))
      (lambda ()
        (cond
          ((<= (get count) 0)
           eof)
          (else
           (let ((result (get start)))
             (begin
               (set count (- (get count) 1))
               (set start (+ (get start) step))
               result))))))))

;; make-range-generator, of three arguments
(define* make-range-generator (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (int int int) gen)
  (lambda (start0 end step)
    (let ((start (the (ref int @heap) (new start0))))
      (begin
        (set start (- (+ (get start) step) step))
        (lambda () (if (< (get start) end)
                       (let ((v (get start)))
                         (begin
                           (set start (+ (get start) step))
                           v))
                       eof))))))

(define* pythagorean-triples-using-generators (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) ints)
  (lambda (nth)
    (cwcc
     (lambda ((return (subr (goto @k) (ints) void)))
       (let ((count (the (ref int @heap) (new 0)))
             (n-values (make-iota-generator greatest-fixnum 1 1)))
         (letrec ((n-loop (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (goto @k) (read (globals make-range-generator eof-object? eof))) (int) ints)
                    (lambda (n)
                      (if (> (get count) nth)
                          nil
                          (let ((a-values (make-range-generator 1 (+ n 1) 1)))
                            (letrec ((a-loop (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (goto @k) (read (globals make-range-generator eof-object? eof))) (int) unit)
                                       (lambda (a)
                                         (if (eof-object? a)
                                             #u
                                             (let ((b-values (make-range-generator a (+ n 1) 1)))
                                               (letrec ((b-loop (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (goto @k) (read (globals eof-object? eof))) (int) unit)
                                                          (lambda (b)
                                                            (if (eof-object? b)
                                                                #u
                                                                (let ((c (- (- n a) b)))
                                                                  (begin
                                                                    (if (= (+ (* a a) (* b b)) (* c c))
                                                                        (begin (set count (+ (get count) 1))
                                                                               (if (> (get count) nth)
                                                                                   (return (list a b c))
                                                                                   #u))
                                                                        #u)
                                                                    (b-loop (b-values))))))))
                                                 (begin (b-loop (b-values))
                                                        (a-loop (a-values)))))))))
                              (begin (a-loop (a-values))
                                     (n-loop (n-values)))))))))
           (n-loop (n-values))))))))

(define* go (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) ints)
  (lambda (n) (pythagorean-triples-using-generators n)))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 250)
(define iterations int 1)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int ints) ints)
  (lambda (i result) (if (= i 0) result (run (- i 1) (go input1)))))
(run iterations nil)
