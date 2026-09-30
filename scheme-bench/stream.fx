;;; STREAM -- Stream benchmark.
;;;
;;; Uses an example taken from the SRFI 41 document.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/stream.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (go 100).
;;; Answer: (49 168 175).
;;;
;;; FX-26 has no (scheme stream), so SRFI 41's streams are written here,
;;; after Larceny's (Philip L. Bewig's reference implementation,
;;; lib/SRFI/srfi/%3a41.sls): a stream is a promise, a record whose one
;;; mutable field holds a mutable box of a tag, lazy or eager, and a thunk
;;; or a value; `stream-force` forces it as there, sharing the box of the
;;; promise the thunk returns. The macros (`stream-lazy`, `stream-eager`,
;;; `stream-delay`, `stream-cons`, `stream-lambda`, `stream-let`, and
;;; `stream-of` with its `stream-of-aux`) are expanded by hand, as
;;; syntax-rules would. What differs, and why:
;;; - A promise is a ref of a ref of a sum, `(lazy thunk)` or `(eager
;;;   value)`, where Larceny's is a record of a pair `(tag . x)`: `x` is a
;;;   thunk or a value, which FX-26 must tell apart by a tag of its own.
;;;   Copying the promise* box's tag and value into this one is a `set` of
;;;   the sum.
;;; - A stream pare, an immutable record, is a pair here, and the null
;;;   stream's value `(stream . null)` is nil, so `stream-null?`, which
;;;   compares with `eqv?` the forced value and the forced `stream-null`,
;;;   asks `null?` of the forced value.
;;; - One `stream-null` for each element type the benchmark uses (ints and
;;;   lists), since a global is of one type; each is made once, as there.
;;; - `stream?` checks, and the error branches of `stream-car`,
;;;   `stream-cdr`, `stream-range` and `stream-ref`, are left out, the types
;;;   ruling the first out. `stream-car` and `stream-cdr` of the null
;;;   stream still ask `stream-null?` first, and would then fail at `car`
;;;   and `cdr` of nil.
;;; - A thunk is kept in the heap and reads it, so its type says `spin`;
;;;   its type is one for every thunk, so it reads every global some thunk
;;;   reads.

(define-effect thunks (maxeff (read @heap) (write @heap) (alloc @heap) spin
                            (read (globals stream-force stream-null? stream-car stream-cdr stream-range
                                           stream-null-int stream-null-ints))))

(define-type (promise (v type))
  (ref (ref (sumof (lazy (subr thunks () (promise v))) (eager v)) @heap) @heap))
(define-type (pare (t type)) (pairof (promise t) (promise (pare t)) @heap))
(define-type (stream (t type)) (promise (pare t)))
(define-type ints (listof int @heap))

(define* stream-force
  (poly ((v type)) (subr thunks ((promise v)) v))
  (plambda ((v type))
    (lambda (promise)
      (let ((content (get promise)))
        (tagcase (get content)
          (eager x x)
          (lazy th
            (let* ((promise* (th))
                   (content (get promise)))
              (begin
                (tagcase (get content)
                  (eager x #u)
                  (lazy y (begin (set content (get (get promise*)))
                                 (set promise* content))))
                (stream-force promise)))))))))

;; (stream-delay (cons 'stream 'null)), for each element type
(define stream-null-int (stream int)
  (new (new (sum lazy (lambda () (new (new (sum eager (the (pare int) no-pair)))))))))
(define stream-null-ints (stream ints)
  (new (new (sum lazy (lambda () (new (new (sum eager (the (pare ints) no-pair)))))))))

(define* stream-null?
  (poly ((t type)) (subr thunks ((stream t)) bool))
  (plambda ((t type))
    (lambda (obj) (null? (stream-force obj)))))

(define* stream-car
  (poly ((t type)) (subr thunks ((stream t)) t))
  (plambda ((t type))
    (lambda (strm)
      (if (stream-null? strm)
          (stream-force (car (stream-force strm)))    ; (error 'stream-car "null stream")
          (stream-force (car (stream-force strm)))))))

(define* stream-cdr
  (poly ((t type)) (subr thunks ((stream t)) (stream t)))
  (plambda ((t type))
    (lambda (strm)
      (if (stream-null? strm)
          (cdr (stream-force strm))                  ; (error 'stream-cdr "null stream")
          (cdr (stream-force strm))))))

;;; (stream-from first 1)
(define* stream-from (subr thunks (int) (stream int))
  (lambda (first)
    (letrec ((stream-from (subr thunks (int int) (stream int))
               ;; (stream-lambda (first delta)
               ;;   (stream-cons first (stream-from (+ first delta) delta)))
               (lambda (first delta)
                 (new (new (sum lazy (lambda ()
                   (new (new (sum eager (cons (new (new (sum lazy (lambda () (new (new (sum eager first)))))))
                                              (new (new (sum lazy (lambda () (stream-from (+ first delta) delta))))))))))))))))
      (stream-from first 1))))

;;; (stream-range first past)
(define* stream-range (subr thunks (int int) (stream int))
  (lambda (first past)
    (letrec ((stream-range (subr thunks (int int int (subr pure (int int) bool)) (stream int))
               ;; (stream-lambda (first past delta lt?)
               ;;   (if (lt? first past)
               ;;       (stream-cons first (stream-range (+ first delta) past delta lt?))
               ;;       stream-null))
               (lambda (first past delta lt?)
                 (new (new (sum lazy (lambda ()
                   (if (lt? first past)
                       (new (new (sum eager (cons (new (new (sum lazy (lambda () (new (new (sum eager first)))))))
                                                  (new (new (sum lazy (lambda () (stream-range (+ first delta) past delta lt?)))))))))
                       stream-null-int))))))))
      (let ((delta (cond ((< first past) 1) (else -1))))
        (let ((lt? (if (< 0 delta)
                       (lambda ((a int) (b int)) (< a b))
                       (lambda ((a int) (b int)) (> a b)))))
          (stream-range first past delta lt?))))))

(define* stream-ref (subr thunks ((stream ints) int) ints)
  (lambda (strm n)
    (cond ((stream-null? strm) nil)    ; (error 'stream-ref "beyond end of stream")
          ((= n 0) (stream-car strm))
          (else (stream-ref (stream-cdr strm) (- n 1))))))

;;; (stream-of (list a b c)
;;;   (n in (stream-from 1))
;;;   (a in (stream-range 1 n))
;;;   (b in (stream-range a n))
;;;   (c is (- n a b))
;;;   (= (+ (* a a) (* b b)) (* c c)))
;;; expanded: each `in` a `stream-let` loop over its stream, whose null
;;; case is the enclosing loop's next step (for the outermost,
;;; `stream-null`); `is` a `let`; the test an `if` whose false arm is the
;;; loop's next step.
(define* pythagorean-triples-using-streams (subr thunks (int) ints)
  (lambda (n0)
    (stream-ref
     (letrec ((loop1 (subr thunks ((stream int)) (stream ints))
                (lambda (strm1)
                  (new (new (sum lazy (lambda ()
                    (if (stream-null? strm1)
                        stream-null-ints
                        (let ((n (stream-car strm1)))
                          (letrec ((loop2 (subr thunks ((stream int)) (stream ints))
                                     (lambda (strm2)
                                       (new (new (sum lazy (lambda ()
                                         (if (stream-null? strm2)
                                             (loop1 (stream-cdr strm1))
                                             (let ((a (stream-car strm2)))
                                               (letrec ((loop3 (subr thunks ((stream int)) (stream ints))
                                                          (lambda (strm3)
                                                            (new (new (sum lazy (lambda ()
                                                              (if (stream-null? strm3)
                                                                  (loop2 (stream-cdr strm2))
                                                                  (let ((b (stream-car strm3)))
                                                                    (let ((c (- (- n a) b)))
                                                                      (if (= (+ (* a a) (* b b)) (* c c))
                                                                          ;; (stream-cons (list a b c) (loop3 (stream-cdr strm3)))
                                                                          (new (new (sum eager
                                                                            (cons (new (new (sum lazy (lambda ()
                                                                                    (new (new (sum eager (list a b c))))))))
                                                                                  (new (new (sum lazy (lambda () (loop3 (stream-cdr strm3))))))))))
                                                                          (loop3 (stream-cdr strm3)))))))))))))
                                                 (loop3 (stream-range a n))))))))))))
                            (loop2 (stream-range 1 n))))))))))))
       (loop1 (stream-from 1)))
     n0)))

(define* go (subr thunks (int) ints)
  (lambda (n) (pythagorean-triples-using-streams n)))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 100)
(define iterations int 1)

(define* run (subr thunks (int ints) ints)
  (lambda (i result) (if (= i 0) result (run (- i 1) (go input1)))))
(run iterations nil)
