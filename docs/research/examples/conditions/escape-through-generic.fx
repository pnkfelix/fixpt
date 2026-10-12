; Design A through generic code: `sum-over` knows nothing of failing; it is
; polymorphic in its argument's effect `e`, so given `digit` at a handler's
; region its call has `(goto r)` too, and the prompt outside removes it.
; What Java's checked exceptions could not do with a lambda.
;; What a prompt's body may do, which every tag must say (its `D`).
(define-effect bodies (maxeff (read @globals) spin))
(define digit
  (poly ((r region)) (subr (goto r) ((prompt-tag int string bodies r) char) int))
  (plambda ((r region))
    (lambda (t c)
      (if (and (char>=? c #\0) (char<=? c #\9))
          (- (char->integer c) 48)
          ((proj (proj abort-current-continuation r) int string bodies) t "not a digit")))))
;; The sum of `f` of each character of `s` from `i`: generic in what `f` does.
(define* sum-over
  (poly ((e effect)) (subr (maxeff e spin) ((subr e (char) int) string int) int))
  (plambda ((e effect))
    (lambda (f s i)
      (if (>= i (string-length s))
          0
          (+ (f (string-ref s i)) ((proj sum-over e) f s (+ i 1)))))))
;; The digits of `s` summed, or -1 if one is no digit.
(define digit-sum (subr (maxeff (read (globals digit sum-over)) spin) (string) int)
  (lambda (s)
    (letregion r
      (let ((t ((proj (proj make-continuation-prompt-tag r) int string bodies))))
        (prompt t
          (sum-over (lambda ((c char)) ((proj digit r) t c)) s 0)
          (lambda ((why string)) -1))))))
(define main (subr (maxeff (read (globals digit sum-over digit-sum)) spin) () (listof int acyclic))
  (lambda () (list (digit-sum "123") (digit-sum "1x3"))))
(main)
