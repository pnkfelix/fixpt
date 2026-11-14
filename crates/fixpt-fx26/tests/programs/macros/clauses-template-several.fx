;; ! which of this macro's clauses' signatures it fits, each its own binding structure, is not known where the template is checked: not yet
;; A use in a template whose parts are not known, which may fit more than
;; one member: refused, for now.
(define-syntax my-or (clauses () (expr) (expr expr expr ...))
  (syntax-rules () ((_) #f) ((_ e) e) ((_ e f rest ...) (let ((t e)) (if t t (my-or f rest ...))))))
1
