;; => (#t #f)
;; `define-syntax-rec` with one signature written and one inferred.
(define-syntax-rec
  (ev? (data ...) (syntax-rules () ((_) #t) ((_ x r ...) (od? r ...))))
  (od? (syntax-rules () ((_) #f) ((_ x r ...) (ev? r ...)))))
(list (ev? 1 2) (od? 1 2))
