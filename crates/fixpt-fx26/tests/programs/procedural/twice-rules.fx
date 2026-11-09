;; => (22 101)
;; One macro, three ways (TODO.md §228; `twice-er.fx`, `twice-sc.fx`): `twice`
;; binds a temporary of its own, which the operand's `x` does not see, and
;; `inc` calls the global `helper`, whatever binds `helper` where it is used.
;; By `syntax-rules`, hygiene is the signature's, inferred.
(define helper (subr pure (int) int) (lambda (x) (+ x 1)))
(define-syntax twice (syntax-rules () ((_ e) (let ((x e)) (+ x x)))))
(define-syntax inc (syntax-rules () ((_ e) (helper e))))
(list (let ((x 10)) (twice (+ x 1))) (let ((helper 100)) (inc helper)))
