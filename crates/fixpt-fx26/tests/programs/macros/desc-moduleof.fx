;; ! a `moduleof` in a template's description: not yet
(define-syntax bad (expr)
  (syntax-rules ()
    ((_ e) (the (moduleof (val x int)) e))))
1
