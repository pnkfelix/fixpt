;; => 4
;; `(select #%toplevel:m t)`: the top level's `m`'s `t`, whatever binds `m`
;; where it is written.
(define m (module (define-type t int)))
(let ((m (module (define-type t bool)))) (the (select #%toplevel:m t) 4))
