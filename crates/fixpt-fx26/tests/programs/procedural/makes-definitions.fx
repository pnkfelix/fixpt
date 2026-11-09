;; => 8
;; A procedural macro at the top level may make definitions, which no
;; signature says ahead; and its output may use a `syntax-rules` macro.
(define-syntax let1 (syntax-rules () ((_ x e body) (let ((x e)) body))))
(define-syntax define-const
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'define) ,(car (cdr form)) ,(rename 'int)
         (,(rename 'let1) ,(rename 'v) ,(car (cdr (cdr form))) ,(rename 'v))))))
(define-const seven 7)
(+ seven 1)
