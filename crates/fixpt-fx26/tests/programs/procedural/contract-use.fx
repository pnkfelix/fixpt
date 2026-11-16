;; ! a use of `let1`: `3` is not a name that may be bound
;; A use that does not fit its macro's contract is refused before the
;; transformer runs, as a `syntax-rules` macro's is.
(define-syntax let1
  (macro (_ (p1 @ bvar expr) p2 @ expr) expr (bind p1 in p2))
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((xe (car (cdr form))) (body (car (cdr (cdr form)))))
        `(,(rename 'let) ((,(car xe) ,(car (cdr xe)))) ,body)))))
(let1 (3 4) 5)
