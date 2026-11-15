;; => (7 104)
;; A procedural macro with a contract, written as a `syntax-rules` macro's is
;; (`typed-macros.md`, "Decided: procedural macros checked by their
;; contracts"): its use aligned with it, and its expansion held to it, run
;; again with the binder renamed, `body` in its scope, `e` not.
(define-syntax let1
  ;; As named: ((x bvar) (e expr)) (body (in expr x))
  (-> ((bvar expr) (import expr (rho (AA var)))) expr)
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((xe (car (cdr form))) (body (car (cdr (cdr form)))))
        `(,(rename 'let) ((,(car xe) ,(car (cdr xe)))) ,body)))))
(define x int 100)
(list (let1 (y 3) (+ y 4)) (let1 (x (+ x 1)) (+ x 3)))
