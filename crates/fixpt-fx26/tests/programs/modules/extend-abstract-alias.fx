;; => 2
;; `extend` of modules by name gives their abstract types as aliases
;; (`TODO.md` §69): `both`'s `t` is `other`'s, `e1`'s where both have one,
;; and `counter`'s values keep `counter..t`, not taken by `other`'s `t`;
;; `plus`'s `e1` uses `counter`'s values.
;; `counter`, with an abstract type of its own.
(define counter
  (module (define-generative t int)
          (define zero t (up-t 0))
          (define next (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
          (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define other (module (define-generative t bool) (define yes t (up-t #t))))
(define both (extend counter other))
(define plus (extend counter (module (define two (next (next zero))))))
(- ((with counter value) ((with plus next) (with plus two)))
   ((with counter value) ((with both next) (with both zero))))
