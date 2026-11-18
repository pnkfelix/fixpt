;; => m::x
;; A path a macro's use gives where an expression is, after its expansion,
;; is a path; one it takes as a datum, quoted, a symbol (TODO.md §296).
(define m (module (define x 1)))
(define-syntax same (macro (_ expr) expr) (syntax-rules ((_ e) e)))
(define-syntax quoted (macro (_ data) expr) (syntax-rules ((_ d) 'd)))
(if (= (same m::x) 1) (quoted m::x) 'no)
