;; ! `(select k t)`: `k` is a int, not a module
;; `select` takes a component of a module, not of any value.
(define k int 3)
(the (select k t) 1)
