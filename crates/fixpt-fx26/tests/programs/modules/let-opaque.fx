;; ! argument 1 is a m..t, where a counter..t is expected
;; A `let`-bound module is opaque: `m` is `counter`, but its type is its own
;; (Sheldon, LFP90 §2.1.4).
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(let ((m counter)) ((with counter value) (with m zero)))
