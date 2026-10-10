;; ! `c..t` is a module's abstract type, not known outside the scope where the module is named
;; A module that includes `c` names `c`'s abstract type, so it cannot leave
;; the scope where `c` is bound (`TODO.md` §69), as `c..t` cannot.
;; `counter`, with an abstract type of its own.
(define counter
  (module (define-generative t int)
          (define zero t (up-t 0))
          (define next (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
          (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define m (let ((c counter)) (module (include c))))
