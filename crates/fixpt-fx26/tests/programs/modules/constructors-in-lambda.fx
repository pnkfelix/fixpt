;; => 22
;; Two constructors of one arity, of a datatype a module made in a lambda
;; defines: each its own in register code too. Once both were one word
;; there, as the compilers tell lambdas apart by where their bodies are,
;; and each constructor's body was at the whole `define-datatype`.
(define make
  (lambda ()
    (module
      (define-datatype shape (circle int) (square int))
      (define area (subr pure (shape) int)
        (lambda (s) (tagcase s (circle (r) (* 3 r)) (square (n) (* n n))))))))
(define m (make))
(define circle (with m circle))
(define square (with m square))
(define area (with m area))
(+ (area (circle 2)) (area (square 4)))
