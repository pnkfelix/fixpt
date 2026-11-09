;; => 7
;; A template's `letrena`: its name made fresh, the place in its types and
;; the value of it alike; the use's `r`, its own.
(define-syntax first-in-arena (expr)
  (syntax-rules ()
    ((_ e) (letrena r (car (the (listof int r) (rcons r e nil)))))))
(let ((r 7)) (first-in-arena r))
