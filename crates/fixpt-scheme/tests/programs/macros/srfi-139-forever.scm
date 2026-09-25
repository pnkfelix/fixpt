(define-syntax-parameter abort
  (syntax-rules () ((_ . _) (syntax-error "abort used outside of a loop"))))
(define-syntax forever
  (syntax-rules ()
    ((forever body1 body2 ...)
     (call-with-current-continuation
      (lambda (escape)
        (syntax-parameterize
            ((abort (syntax-rules () ((abort value (... ...)) (escape value (... ...))))))
          (let loop () body1 body2 ... (loop))))))))
(define i 0)
(forever (set! i (+ i 1)) (if (= i 5) (abort i)))
