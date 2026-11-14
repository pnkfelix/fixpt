;; ! is expected here
;; A module whose abstract constructor is of one kind does not stand for
;; one of another.
(define-type one (moduleof (abs f (=> (type) type)) (val x int)))
(define-type two (moduleof (abs f (=> (type type) type)) (val x int)))
(define m one (module (define-generative (f (a type)) (listof a @heap) #:seal up-f #:unseal down-f)
  (define x 1)))
(define n two m)
