; Accepted: the standard input read by lines (TODO.md §84), each line, the
; end, or a failure the program sees.
(define-type line-result (sumof (line string) (eof unit) (failed io-error)))
(define* count-lines (subr (maxeff (io stdin) spin) (int) int)
  (lambda (n)
    (tagcase (the line-result (read-line))
      (line s (count-lines (+ n 1)))
      (eof u n)
      (failed e -1))))
