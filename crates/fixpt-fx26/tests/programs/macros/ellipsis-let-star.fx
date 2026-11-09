;; => 2
;; A template's `let*` by ellipsis: each clause in the scope of those before
;; it, the body of them all; the template's binders fresh in each.
(define-syntax listed*
  (expr ...)
  (syntax-rules ()
    ((_ e ...) (let* ((t e) ...) (list t ...)))))
(car (cdr (listed* 1 2 3)))
