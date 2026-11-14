;; ! this use of `ping` is one it was expanded from, unchanged, through `pong`: its expansion would never end
;; A use that comes back through another macro's.
(define-syntax-rec
  (ping (syntax-rules ((_ e) (pong e))))
  (pong (syntax-rules ((_ e) (ping e)))))
(ping 1)
