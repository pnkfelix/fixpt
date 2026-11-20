;; => 1
;; A hidden `define-type` is declared ahead as the module's others are, so
;; one may name a later one (Heist's should-work note, entry 15); and the
;; module's items outside the `hide` name it too, which outside it none may.
(define m
  (module
    (hide (define-type node (productof (v int) (next nodes)))
          (define-type nodes (listof node acyclic)))
    (define one nodes (list (product (v 1) (next nil))))
    (define count (subr pure (nodes) int) (lambda (l) (if (null? l) 0 1)))))
((with m count) (with m one))
