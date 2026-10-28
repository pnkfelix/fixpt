; A process waits for a key, a message or a deadline, whichever comes first
; (TODO.md §95): the first task, waiting for its answer, waits for the
; standard input with it. The status is the byte, 255 (-1) at the input's
; end, 1 if the deadline (a second) came first.
(define-type byte-result (oneof (byte u8) (eof unit) (failed io-error)))
(define* code (subr pure (byte-result) int)
  (lambda (b) (tagcase b (byte k (u8->int k)) (eof u -1) (failed e -2))))
(define-effect waits (maxeff (alloc @p) (init @c) (await @c) (io stdin) (io clock) nondet))
(define main (subr (maxeff waits (read (globals code))) () int)
  (lambda ()
    (let* ((answer (the (icell int @c) (make-icell)))
           (waiter
            (the (addr int @p)
              (spawn (box int r)
                (pselect ((receive box) m (icell-put! answer m))
                         ((read-byte) b (icell-put! answer (code b)))
                         ((sleep-until (i64+ (clock) (int->i64 1000000000))) u
                          (icell-put! answer 1)))))))
      (icell-get answer))))
