;; ! a macro's clauses are a transformer's: `(syntax-rules (literal …) ((_ . pattern) template) …)`
;; A macro's clauses say how they are read, `syntax-rules`, which another
;; transformer will not share.
(define-syntax my-or (expr expr) ((_ a b) (let ((t a)) (if t t b))))
1
