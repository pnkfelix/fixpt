;; => 3
;; A module included by name gives its abstract types as aliases of its own
;; (`TODO.md` §69): `more`'s `t` is `counter..t`, so `more`'s values and
;; `counter`'s are one another's, both ways, and inside `more` `t` is it.
;; `counter`, with an abstract type of its own.
(define counter
  (module (define-generative t int)
          (define zero t (up-t 0))
          (define next (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
          (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define more
  (module (include counter)
          (define two t (next (next zero)))))
(define to-counter (subr pure ((select more t)) (select counter t)) (lambda (x) x))
(define to-more (subr pure ((select counter t)) (select more t)) (lambda (x) x))
((with counter value) (to-counter ((with more next) (to-more (with more two)))))
