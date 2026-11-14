;; ! this use of `same` is one it was expanded from, unchanged: its expansion would never end
;; A transformer that returns its input as it is (`TODO.md` §231): the
;; expander would expand the same form forever.
(define-syntax same (sc-macro-transformer (lambda (form env) form)))
(same 1)
