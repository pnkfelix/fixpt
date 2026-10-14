;; => 42
;; Preemption in cellular code native code called (`TODO.md` §93): the
;; spinner's loop stays cellular (`stay-cellular`), called by its process's
;; native code; it is preempted where the scheduler's prompt is in the
;; native frames out from it, so it does not starve the process that
;; answers. Elsewhere, as `spinner.fx`.
(define answer (icell int @c) (make-icell))
(define* spin-forever (subr spin (int) int)
  (lambda (n) (begin (stay-cellular #u) (spin-forever (+ n 1)))))
(define spinner (addr int @p) (spawn (box int r) (begin (spin-forever (receive box)) #u)))
(define doubler (addr int @p) (spawn (box int r) (icell-put! answer (* 2 (receive box)))))
(send spinner 0)
(send doubler 21)
(icell-get answer)
