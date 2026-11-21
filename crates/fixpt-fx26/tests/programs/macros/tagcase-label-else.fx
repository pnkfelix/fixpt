;; ! `else` is a reserved word, not a tag or label
;; A label a use gives is no word the kernel's forms read where a label may
;; be: `else` here would make `want`'s arm `(else s …)`.
(define-type v (sumof (int int) (str string)))
(define-syntax want
  (macro (_ label x @ bvar expr body @ expr) expr (bind x in body))
  (syntax-rules ((_ t x e body) (tagcase e (t x body) (else y 0)))))
(want else s (the v (sum str "abc")) 7)
