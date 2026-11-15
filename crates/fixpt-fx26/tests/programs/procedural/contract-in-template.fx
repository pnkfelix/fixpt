;; => 9
;; A procedural macro with a contract in a `syntax-rules` template, which its
;; signature lets the template's alignment take as any macro's.
(define-syntax let1
  (-> ((bvar expr) (import expr (rho (AA var)))) expr)
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((xe (car (cdr form))) (body (car (cdr (cdr form)))))
        `(,(rename 'let) ((,(car xe) ,(car (cdr xe)))) ,body)))))
(define-syntax twice1
  (-> ((bvar expr) (import expr (rho (AA var)))) expr)
  (syntax-rules ((_ (x e) body) (let1 (x e) (+ body 3)))))
(twice1 (y 2) (+ y 4))
