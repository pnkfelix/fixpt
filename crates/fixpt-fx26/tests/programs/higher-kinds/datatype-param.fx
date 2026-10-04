;; => 3
;; A datatype over any container: a rose tree whose children are in `f`.
(define-datatype (rose (f (=> (type) type)) (a type)) (node a (f (rose f a))))
(define-type (lst (t type)) (listof t @heap))
(define leaf (proj node lst int))
(define t (leaf 1 (list (leaf 2 nil) (leaf 3 nil))))
(tagcase t (node (x kids) (tagcase (car (cdr kids)) (node (y more) y))))
