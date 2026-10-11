;; ! `num` is defined twice in this module
;; Two `include`s giving one type name for different types are refused.
(define a (module (define-type num int) (define one num 1)))
(define c (module (define-type num bool) (define t num #t)))
(define bad (module (include a) (include c)))
