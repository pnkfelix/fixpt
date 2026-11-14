;; ! a template's `abs` or `desc` writes its label as a keyword, its binder after it
;; A template's own abstract type, its one name both label and binder:
;; renamed, the label would be lost; kept, a use's type would be captured.
(define-syntax bad (-> (type) type)
  (syntax-rules ((_ e) (moduleof (abs t type) (val #:x (subr pure (e) t))))))
1
