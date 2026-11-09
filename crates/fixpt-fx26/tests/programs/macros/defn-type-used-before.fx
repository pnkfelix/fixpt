;; => 1
;; A type a use defines, named by a form before the use: types are
;; declared ahead, the use's among them.
(define xs ints (list 1))
(define-syntax define-ints
  (-> (dvar) defn)
  (syntax-rules ()
    ((_ t) (define-type t (listof int)))))
(define-ints ints)
(length xs)
