;; => 3
;; A type the template defines, made fresh: not the top level's `cell`.
(define-type cell bool)
(define-syntax define-cell
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ name) (begin (define-type cell (ref int @heap)) (define name cell (new 3))))))
(define-cell c)
(get c)
