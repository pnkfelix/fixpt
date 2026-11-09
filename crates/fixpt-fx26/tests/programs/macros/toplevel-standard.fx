;; => 4203
;; A template's standard name is the top level's too: here the program's
;; own `string-length`, which redefines it. `(with #%fx string-length)` is
;; the standard one, whatever the top level does.
(define string-length (subr pure (string) int) (lambda (s) 42))
(define-syntax size-of (expr)
  (syntax-rules ()
    ((_ e) (let ((s e)) (+ (* 100 (string-length s)) ((with #%fx string-length) s))))))
(size-of "abc")
