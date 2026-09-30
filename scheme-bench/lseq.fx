;;; LSEQ -- Lazy sequence benchmark.
;;;
;;; Uses an example taken from the SRFI 41 document.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/lseq.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (go 250).
;;; Answer: (135 324 351).
;;;
;;; FX-26 has no (scheme generator) or (scheme lseq). `make-iota-generator`
;;; and `make-range-generator` are Larceny's (SRFI 121's reference
;;; implementation, lib/SRFI/srfi/121.body.scm), closures over variables
;;; they assign, here refs; `generator->lseq`, `lseq-car` and `lseq-cdr`
;;; are Larceny's too (SRFI 127's, lib/SRFI/srfi/127.body.scm): an lseq is
;;; a pair whose cdr, until `lseq-cdr` realizes it, is the generator. What
;;; differs, and why:
;;; - An lseq's cdr is a list or a procedure, which `procedure?` tells
;;;   apart; FX-26 has no untagged union, so here it is a sum, `(seq
;;;   rest)` or `(gen g)`. Realizing an element makes a sum as well as its
;;;   pair (the new pair shares its predecessor's `(gen g)`).
;;; - The end of a generator, Scheme's eof object, is a fixnum none of
;;;   these generators yields: the least one. A generator is then a
;;;   procedure of no arguments returning an int, as in Larceny, where the
;;;   eof object is also an immediate; `eof-object?` compares with it.
;;; - The benchmark counts n with `(make-iota-generator +inf.0 1)`, a count
;;;   that never runs out; FX-26 has no flonums, so the count is the
;;;   greatest fixnum, which runs out no sooner than 2^60 values.
;;; - `set!` of the local `count` is a ref, `do` a named loop, and
;;;   `call-with-current-continuation` is `cwcc`.

(define-type gen (subr (maxeff (read @heap) (write @heap) spin (read (globals eof))) () int))
(define-type ints (listof int @heap))
;; An lseq: nil, or a pair whose cdr is the rest, realized, or the
;; generator of the rest.
(define-type lseq (pairof int (sumof (seq lseq) (gen gen)) @heap))
(define-type tail (sumof (seq lseq) (gen gen)))

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

;;; generator->lseq
(define* generator->lseq (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read (globals eof-object? eof))) (gen) lseq)
  (lambda (gen)
    (let ((value (gen)))
      ;; See what starts off the generator:
      ;; if it's already exhausted, the lseq is empty,
      ;; otherwise, return an improper list with one value and the generator
      ;; in the tail, which is how we represent unrealized lseqs
      (if (eof-object? value)
          no-pair
          (cons value (sum gen gen))))))

;;; Car on lseqs is the same as on lists
(define* lseq-car (subr (read @heap) (lseq) int) (lambda (lseq) (car lseq)))

;;; Lseq-cdr expands the generator if it's there, or falls back to regular cdr
(define* lseq-cdr (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read (globals eof-object? eof))) (lseq) lseq)
  (lambda (lseq)
    ;; We assume lseq is a pair, because it is an error if it isn't
    ;; If it's a procedure, we assume it's a generator and invoke it
    (tagcase (cdr lseq)
      (gen g
        (let ((obj (g)))
          (cond
            ;; If the generator is exhausted, replace it with () and return ()
            ((eof-object? obj)
             (begin (set-cdr! lseq (sum seq (the lseq no-pair)))
                    no-pair))
            ;; Otherwise, make a new pair of the value and the generator
            ;; and patch it in to the cdr
            (else (let ((result (the lseq (cons obj (cdr lseq)))))
                    (begin (set-cdr! lseq (sum seq result))
                           result))))))
      ;; If there is no procedure, return the ordinary cdr
      (seq s s))))

(define-effect lseqs (maxeff (read @heap) (write @heap) (alloc @heap) spin (goto @k)
                             (read (globals make-range-generator generator->lseq lseq-car lseq-cdr eof-object? eof))))

(define* pythagorean-triples-using-lazy-sequences (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) ints)
  (lambda (nth)
    (cwcc
     (lambda ((return (subr (goto @k) (ints) void)))
       (let ((count (the (ref int @heap) (new 0)))
             (n-values (generator->lseq (make-iota-generator greatest-fixnum 1 1))))
         (letrec ((n-loop (subr lseqs (int lseq) ints)
                    (lambda (n n-values)
                      (if (> (get count) nth)
                          nil
                          (let ((a-values
                                 (generator->lseq (make-range-generator 1 (+ n 1) 1))))
                            (letrec ((a-loop (subr lseqs (int lseq) unit)
                                       (lambda (a a-values)
                                         (if (null? a-values)
                                             #u
                                             (let ((b-values
                                                    (generator->lseq (make-range-generator a (+ n 1) 1))))
                                               (letrec ((b-loop (subr lseqs (int lseq) unit)
                                                          (lambda (b b-values)
                                                            (if (null? b-values)
                                                                #u
                                                                (let ((c (- (- n a) b)))
                                                                  (begin
                                                                    (if (= (+ (* a a) (* b b)) (* c c))
                                                                        (begin (set count (+ (get count) 1))
                                                                               (if (> (get count) nth)
                                                                                   (return (list a b c))
                                                                                   #u))
                                                                        #u)
                                                                    (b-loop (lseq-car b-values) (lseq-cdr b-values))))))))
                                                 (begin (b-loop (lseq-car b-values) (lseq-cdr b-values))
                                                        (a-loop (lseq-car a-values) (lseq-cdr a-values)))))))))
                              (begin (a-loop (lseq-car a-values) (lseq-cdr a-values))
                                     (n-loop (lseq-car n-values) (lseq-cdr n-values)))))))))
           (n-loop (lseq-car n-values) (lseq-cdr n-values))))))))

(define* go (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) ints)
  (lambda (n) (pythagorean-triples-using-lazy-sequences n)))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 250)
(define iterations int 1)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int ints) ints)
  (lambda (i result) (if (= i 0) result (run (- i 1) (go input1)))))
(run iterations nil)
