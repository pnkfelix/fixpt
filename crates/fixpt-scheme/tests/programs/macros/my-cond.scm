(define-syntax my-cond
  (syntax-rules (else)
    ((_) 'none)
    ((_ (else e)) e)
    ((_ (c e) rest ...) (if c e (my-cond rest ...)))))
