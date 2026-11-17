;; ! `m.a..t` is a module's abstract type, not known outside the scope where the module is named
;; A path's abstract types are its base's binding's, which nothing may
;; leave the scope of still mentioning.
(define make
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0)))))
(let ((m (module (define a (make))))) (with (with m a) zero))
