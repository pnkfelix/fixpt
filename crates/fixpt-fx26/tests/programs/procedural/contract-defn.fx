;; => 17
;; A procedural macro whose contract makes definitions, and says its uses
;; define their first part (`typed-macros.md`, "Decided: what a definition
;; macro defines, said in what it makes"): its expansion held to it, a
;; helper of its own an alias; and a `syntax-rules` template that uses it
;; sees the name defined.
(define-syntax define-const
  (macro (bvar expr) (defn (A var)))
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'begin)
         (,(rename 'define) ,(rename 'v) int ,(car (cdr (cdr form))))
         (,(rename 'define) ,(car (cdr form)) int (,(rename '+) ,(rename 'v) 1))))))
(define-syntax define-via
  (macro (bvar) defn)
  (syntax-rules
    ((_ name) (begin (define-const x 4) (define name (+ x 5))))))
(define-const seven 6)
(define-via nine)
(+ seven nine)
