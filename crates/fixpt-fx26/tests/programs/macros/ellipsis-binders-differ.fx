;; ! this part repeats binders and parts that were repeated, or given, different numbers of times
;; Two repeated binders, repeated together, repeated different numbers of
;; times.
(define-syntax pairs
  ((expr ...) (expr ...))
  (syntax-rules ()
    ((_ (a ...) (b ...)) (let ((x a) ...) (let ((y b) ...) (list (+ x y) ...))))))
(pairs (1 2) (3))
