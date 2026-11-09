;; => (#t #f)
;; A `define-rec` group a use names: each member in the scope of the whole
;; group.
(define-syntax define-parity
  (-> (bvar bvar) defn)
  (syntax-rules ()
    ((_ ev od)
     (define-rec (ev (->* (int) bool) (lambda ((n int)) (if (= n 0) #t (od (- n 1)))))
                 (od (->* (int) bool) (lambda ((n int)) (if (= n 0) #f (ev (- n 1)))))))))
(define-parity ev? od?)
(list (ev? 10) (od? 10))
