; Design B, Common Lisp's: a handler is found in a mark and called where
; the failure is, before anything unwinds. It may give a value to go on
; with (`lenient-sum`: a bad character counts 0), or escape to a prompt,
; a restart (`strict-sum`: -1 for the whole). `digit` is polymorphic in the
; key's region and in the handler's effect `e`, which its own type then has.
(define-effect bodies (maxeff (read (globals digit sum-over)) spin))
(define digit
  (poly ((k region) (e effect))
    (subr (maxeff (read k) e) ((mark-key (subr e (char) int) k) char) int))
  (plambda ((k region) (e effect))
    (lambda (key c)
      (if (and (char>=? c #\0) (char<=? c #\9))
          (- (char->integer c) 48)
          ;; No handler: a panic, as `error` is.
          (((proj (proj first-mark k) (subr e (char) int))
            key
            (lambda ((x char)) (error "no handler for a character that is no digit")))
           c)))))
;; The sum of `f` of each character of `s` from `i`: generic in what `f` does.
(define* sum-over
  (poly ((e effect)) (subr (maxeff e spin) ((subr e (char) int) string int) int))
  (plambda ((e effect))
    (lambda (f s i)
      (if (>= i (string-length s))
          0
          (+ (f (string-ref s i)) ((proj sum-over e) f s (+ i 1)))))))
;; A bad character counts 0: the handler gives a value, and nothing unwinds.
(define lenient-sum (subr (maxeff (read (globals digit sum-over)) spin) (string) int)
  (lambda (s)
    (letregion k
      (let ((key ((proj (proj make-continuation-mark-key k) (subr pure (char) int)))))
        ((proj (proj with-mark k) (subr pure (char) int) int (maxeff (read k) bodies))
         key
         (lambda ((x char)) 0)
         (lambda () (sum-over (lambda ((c char)) ((proj digit k pure) key c)) s 0)))))))
;; A bad character makes the whole -1: the handler escapes to a prompt, a
;; restart. The key is made inside the prompt's body, so that the body's
;; free variables name the tag's region only through the tag.
(define strict-sum (subr (maxeff (read (globals digit sum-over)) spin) (string) int)
  (lambda (s)
    (letregion r
      (let ((t ((proj (proj make-continuation-prompt-tag r) int string bodies))))
        (prompt t
          (letregion k
            (let ((key ((proj (proj make-continuation-mark-key k) (subr (goto r) (char) int)))))
              ((proj (proj with-mark k)
                     (subr (goto r) (char) int) int (maxeff (read k) (goto r) bodies))
               key
               (lambda ((x char))
                 ((proj (proj abort-current-continuation r) int string bodies) t "no digit"))
               (lambda () (sum-over (lambda ((c char)) ((proj digit k (goto r)) key c)) s 0)))))
          (lambda ((why string)) -1))))))
(define main (subr (maxeff (read (globals digit sum-over lenient-sum strict-sum)) spin)
                   () (listof int acyclic))
  (lambda () (list (lenient-sum "1x3") (strict-sum "123") (strict-sum "1x3"))))
(main)
