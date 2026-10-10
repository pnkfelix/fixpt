;; => 8
;; An abstract constructor's kind by its parameters, `(abs (f (a type)) type)`,
;; as `define-generative` writes them: `(abs f (=> (type) type))`.
(define-type sig-lazy
  (moduleof (abs (susp (a type)) type)
            (val delay (poly ((a type)) (subr (alloc @heap) ((subr pure () a)) (susp a))))
            (val force (poly ((a type)) (subr (read @heap) ((susp a)) a)))))
(define-type sig-lazy-arrow
  (moduleof (abs susp (=> (type) type))
            (val delay (poly ((a type)) (subr (alloc @heap) ((subr pure () a)) (susp a))))
            (val force (poly ((a type)) (subr (read @heap) ((susp a)) a)))))
(define lazy sig-lazy
  (module
    (define-generative (susp (a type)) (ref a @heap))
    (define delay (poly ((a type)) (subr (alloc @heap) ((subr pure () a)) (susp a)))
      (plambda ((a type)) (lambda (th) (up-susp (new (th))))))
    (define force (poly ((a type)) (subr (read @heap) ((susp a)) a))
      (plambda ((a type)) (lambda (s) (get (down-susp s)))))))
;; The two spellings are one type.
(define same sig-lazy-arrow lazy)
(with same (+ ((proj force int) ((proj delay int) (lambda () 7))) 1))
