; Accepted: the terminal (TODO.md §95), `(io terminal)`: raw mode and the
; modes before it, each done, `not-a-terminal` or a failure; the size, in
; rows and columns.
(define-type term-result (sumof (done unit) (not-a-terminal unit) (failed io-error)))
(define* raw? (subr (io terminal) () bool)
  (lambda () (tagcase (the term-result (terminal-raw)) (done u #t) (else r #f))))
(define* restored (subr (io terminal) () unit)
  (lambda () (tagcase (the term-result (terminal-restore)) (done u #u) (else r #u))))
(define* columns (subr (io terminal) () int)
  (lambda ()
    (tagcase (terminal-size)
      (size z (extract z columns))
      (not-a-terminal u 80)
      (failed e 80))))
(define* keys (subr (maxeff (io terminal) (io stdin) (read (globals raw? restored))) () int)
  (lambda ()
    (if (raw?)
        (let ((k (tagcase (read-byte) (byte b (u8->int b)) (else r -1)))) (begin (restored) k))
        -1)))
