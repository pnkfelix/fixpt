;; => (#f #t #t)
;; Patterns written one by one, `(e)`, and one by ellipsis, `(e r ...)`:
;; one list, `(expr ...)`, so that the template's `(or* r ...)` is one.
(define-syntax or*
  (syntax-rules ()
    ((_) #f)
    ((_ e) e)
    ((_ e r ...) (let ((t e)) (if t t (or* r ...))))))
(list (or* #f) (or* #f #t) (or* #f #f #t))
