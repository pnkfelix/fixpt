;; => 5
;; A hole's type left out: the template checked for any type.
(define-syntax same ((expr #:effect pure)) ((_ e) (if #t e e)))
(same 5)
