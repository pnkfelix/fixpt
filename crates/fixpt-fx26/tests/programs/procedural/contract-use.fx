;; ! a use of `let1`: `3` is not a name that may be bound
;; A use that does not fit its macro's contract is refused before the
;; transformer runs, as a `syntax-rules` macro's is.
(define-syntax let1
  ((bvar expr) (import expr (rho (AA var))))
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((xe (car (cdr form))) (body (car (cdr (cdr form)))))
        `(,(rename 'let) ((,(car xe) ,(car (cdr xe)))) ,body)))))
(let1 (3 4) 5)
