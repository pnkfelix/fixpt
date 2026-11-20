;; => 3
;; A `tagcase` arm whose tag a use gives, a `label` part (Heist's
;; should-work note, entry 5): `(t x body)` is a tag's arm, never `(else y
;; body)`, since no use gives a label a reserved word.
(define-type v (sumof (int int) (str string)))
(define-syntax want
  (macro (_ label x @ bvar expr body @ expr) expr (bind x in body))
  (syntax-rules ((_ t x e body) (tagcase e (t x body) (else y 0)))))
(want #:str s (the v (sum str "abc")) (string-length s))
