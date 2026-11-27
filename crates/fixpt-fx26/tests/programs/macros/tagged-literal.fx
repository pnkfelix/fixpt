;; => 7
;; A tagged literal in a macro's use: `#Ltwice"abc"` is
;; `(literal:twice #utf8"abc")`, an expression as a use of any name is.
(define literal:twice (subr pure (utf8) int) (lambda (u) (* 2 (utf8-length u))))
(define-syntax add1 (syntax-rules ((_ e) (+ e 1))))
(add1 #Ltwice"abc")
