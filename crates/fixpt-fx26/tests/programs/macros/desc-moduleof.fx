;; ! a template's `val` writes its label as a keyword
;; A template's `moduleof`: its labels are keywords, as labels in templates
;; are; a bare name, not the use's, is refused.
(define-syntax bad (expr)
  (syntax-rules ()
    ((_ e) (the (moduleof (val x int)) e))))
1
