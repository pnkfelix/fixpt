;; ! where a int is expected
;; A template that needs a hole's type, left out, is refused where it is
;; defined: the type is written where it matters.
(define-syntax inc (macro ((expr #:effect pure)) expr) (syntax-rules ((_ e) (+ e 1))))
1
