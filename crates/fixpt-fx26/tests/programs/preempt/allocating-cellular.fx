;; => 8997014
;; As `allocating-short.fx`, one process's loop cellular code native code
;; called (`stay-cellular`, `TODO.md` §93), which calls native code each
;; time round: preempted at nearly every poll, in either, its continuation
;; crosses the two machines, and what each kept must be there, moved by
;; the collections the other's work makes, when it goes on.
(define a (icell int @c) (make-icell))
(define b (icell int @c) (make-icell))
(define* add-n (subr pure (int int) int) (lambda (s i) (+ s i)))
(define-type (loop-c (r region)) (subr (maxeff (alloc r) (read (globals add-n)) spin)
                                         (int int int (listof int r)) int))
(define* go-c (poly ((r region)) (loop-c r))
  (plambda ((r region))
    (lambda (i n s acc)
      (begin (stay-cellular #u)
             (if (= i n)
                 (+ s (if (null? acc) 0 7))
                 ((proj go-c r) (+ i 1) n (add-n s i) (cons i acc)))))))
(define p (addr int @p)
  (spawn (box int r) (icell-put! a (+ 0 ((proj go-c r) 0 (receive box) 0 nil)))))
(define q (addr int @p)
  (spawn (box int r)
    (letrec ((go (subr (maxeff (alloc r) spin) (int int int (listof int r)) int)
               (lambda (i n s acc)
                 (if (= i n) (+ s (if (null? acc) 0 7)) (go (+ i 1) n (+ s i) (rcons r i acc))))))
      (icell-put! b (go 0 (receive box) 0 nil)))))
(send p 3000)
(send q 3000)
(+ (icell-get a) (icell-get b))
