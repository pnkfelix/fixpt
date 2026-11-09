;; => 2
;; A type a use names, defined under that name.
(define-syntax define-ints
  (-> (dvar) defn)
  (syntax-rules ()
    ((_ t) (define-type t (listof int)))))
(define-ints ints)
(length (the ints (list 1 2)))
