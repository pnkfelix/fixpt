;; ! has no type or effect, and another part of this macro does
;; Every `expr` part of a macro whose parts are typed is typed, or the
;; template cannot be checked once.
(define-syntax half ((expr #:type int) expr) (syntax-rules () ((_ a b) (+ a b))))
1
