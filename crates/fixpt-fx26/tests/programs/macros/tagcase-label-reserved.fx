;; => 7
;; A label a use gives may be a reserved word the kernel's forms do not read
;; where a label may be, `prompt` (a field's or a tag's name, as Heist's
;; `(isearch-but s (prompt p))`): only such a word, `else`, is refused.
(define-type v (sumof (prompt int) (str string)))
(define-syntax want
  (macro (_ label x @ bvar expr body @ expr) expr (bind x in body))
  (syntax-rules ((_ t x e body) (tagcase e (t x body) (else y 0)))))
(want prompt n (the v (sum prompt 7)) n)
