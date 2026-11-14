;; => (same 1)
;; A transformer whose output holds its input quoted: not expanded again,
;; so not a use that comes back to itself.
(define-syntax same (sc-macro-transformer (lambda (form env) `(quote ,form))))
(same 1)
