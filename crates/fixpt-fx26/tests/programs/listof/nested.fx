;; => 2
;; In a recursive type, and a list of lists.
(define-type tree (mu t (oneof (listof t) symbol)))
(define rows (listof (listof int)) (list (list 1) (list 2 3)))
(define deep tree (list 'a (list 'b)))
(length (car (cdr rows)))
