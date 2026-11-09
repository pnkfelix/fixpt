;; ! argument 1 is a bool, where a int is expected
;; A template wrong for its holes' types is refused once, where it is
;; defined, at the hole, though nothing uses it.
(define-syntax bad1 ((expr #:type bool)) (syntax-rules () ((_ c) (+ c 1))))
1
