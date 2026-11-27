;;; A module file that defines a procedural macro and uses it, which staged
;;; code loads (`procedural.fx`; `TODO.md` §312).
(define-syntax swap-args
  (macro (_ f @ expr a @ expr b @ expr) expr)
  (er-macro-transformer
    (lambda (form rename compare)
      (list (car (cdr form)) (car (cdr (cdr (cdr form)))) (car (cdr (cdr form)))))))
(define diff (subr pure (int int) int) (lambda (a b) (- a b)))
(define ten int (swap-args diff 1 11))
