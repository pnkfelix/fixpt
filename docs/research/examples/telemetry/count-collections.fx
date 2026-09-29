;;; Counting collections and words allocated while building a list:
;;; cumulative counters, read before and after, and differenced.
;;; MOCK: the three counters are the proposal, stubbed as reads of one fake
;;; counter at @telemetry, so the types and effects are the proposed ones
;;; and the numbers are not (the real ones are the heap's minor_count,
;;; gc_count and allocated()).
(define-effect observes (maxeff (read @telemetry) (write @telemetry)))
(define fake (ref int @telemetry) (new 0))
(define* minor-collections (subr observes () nat)
  (lambda () (begin (set fake (get fake)) (confirm-nat (get fake) (n n) 0))))
(define* major-collections (subr observes () nat)
  (lambda () (begin (set fake (get fake)) (confirm-nat (get fake) (n n) 0))))
(define* words-allocated (subr observes () nat)
  (lambda () (begin (set fake (get fake)) (confirm-nat (get fake) (n n) 0))))

(define* iota (subr (maxeff (alloc @l) spin) (int (listof int @l)) (listof int @l))
  (lambda (n acc) (if (= n 0) acc (iota (- n 1) (cons n acc)))))

(define-type gc-delta (productof (minor int) (major int) (words int)))

(define* build-and-count (subr (maxeff (alloc @l) spin observes) (int) gc-delta)
  (lambda (n)
    (let* ((m0 (minor-collections)) (j0 (major-collections)) (w0 (words-allocated))
           (xs (iota n nil))
           (w1 (words-allocated)) (j1 (major-collections)) (m1 (minor-collections)))
      (product (minor (- m1 m0)) (major (- j1 j0)) (words (- w1 w0))))))

(extract (build-and-count 100000) minor)   ; 0 with the stubs
