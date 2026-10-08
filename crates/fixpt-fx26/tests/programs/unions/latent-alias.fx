; Accepted: narrowing comes from a test's type, `(bool (then P …) (else Q …))`,
; not from its name: an alias of `int?` at a type proving only its `then`
; narrows as `int?` does there (`TODO.md` §54).
(define is-int (subr pure ((union int string)) (bool (then (shape 0 int)) (else))) int?)
(define* f (subr (read (globals is-int)) ((union int string)) int)
  (lambda (x) (if (is-int x) (+ x 1) 0)))
(f 41)
