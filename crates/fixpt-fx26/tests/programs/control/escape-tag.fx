; An escape-only tag (TODO.md §89): made and escaped to as a prompt tag
; is, but never captured, so its prompts bound nothing their bodies do.
; The raiser is polymorphic in the tag's region; the handler makes the
; region and the tag, so the prompt removes the escape's `(goto r)`, and
; `digit-sum` is pure but for its globals and `spin`, through a generic
; `sum-over` whose effect the checker infers. No bound `D` is written.
(define digit
  (poly ((r region)) (subr (goto r) ((escape-tag int string r) char) int))
  (plambda ((r region))
    (lambda (t c)
      (if (and (char>=? c #\0) (char<=? c #\9))
          (- (char->integer c) 48)
          ((proj (proj escape r) int string) t "not a digit")))))
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
      (let ((t ((proj (proj make-escape-tag r) int string))))
        (prompt t
          (sum-over (lambda ((c char)) ((proj digit r) t c)) s 0)
          (lambda ((why string)) -1))))))
(define main (subr (maxeff (read (globals digit sum-over digit-sum)) spin) () (listof int acyclic))
  (lambda () (list (digit-sum "123") (digit-sum "1x3") (digit-sum ""))))
(main)
