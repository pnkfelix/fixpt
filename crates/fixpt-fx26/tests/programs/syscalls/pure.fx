;;; A pure syscall (Kayak's): a string's length in UTF-8 bytes, which the
;;; runtime has at hand, so a pure procedure that joins strings stays pure.
(define-syscall utf8-length "kayak:string-utf8-length/1" (subr pure (string) int))
(define* joined-length (subr pure (string string) int)
  (lambda (a b) (+ (utf8-length a) (utf8-length b))))
(syscall-available? utf8-length)
(joined-length "héllo" "→ x")
