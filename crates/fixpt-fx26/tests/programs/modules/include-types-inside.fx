;; => 2
;; An `include`'s types are in scope inside the module, in its items'
;; declared types and its `define-type`s; and an item is checked against
;; the type it declares (`TODO.md` §69), so `cons` makes its pair where
;; that type says, `@heap`, as it would with no `include`.
(define base (module (define-type num int) (define one num 1)))
(define m (module (include base)
                  (define two num (+ one one))
                  (define-type pair-of-nums (pairof num num @heap))
                  (define p pair-of-nums (cons one two))))
(with m (cdr p))
