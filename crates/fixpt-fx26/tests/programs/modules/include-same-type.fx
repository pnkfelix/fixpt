;; => 3
;; A type name two `include`s both give is one name where it is the same
;; type both times (a types file giving on another's, `TODO.md` §69).
(define a (module (define-type num int) (define one num 1)))
(define b (module (define-type num int) (define two num 2)))
(define m (module (hide (include a) (include b)) (define three num (+ one two))))
(with m three)
