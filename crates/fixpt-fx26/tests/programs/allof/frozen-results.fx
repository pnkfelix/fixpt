;; => (1 1)
;; Immutable data made and kept by a closure: a frozen list and a product,
;; made with no `alloc`. One value of both types: the meet stands.
;; `ab` and `ac` share the tag `a`: `(sum a 1)` is both.
(define-type ab (sumof (a int) (b int)))
(define-type ac (sumof (a int) (c int)))
(define mk (allof (subr pure (ab) (subr pure () (listof ab acyclic)))
                  (subr pure (ac) (subr pure () (listof ac acyclic))))
  (lambda (x) (let ((l (list x x)) (p (product (1 x)))) (lambda () (cons (extract p 1) l)))))
(define g (mk (sum a 1)))
(define as-ab (subr pure () (listof ab acyclic)) g)
(define as-ac (subr pure () (listof ac acyclic)) g)
(list (tagcase (car (as-ab)) (a i i) (b j j)) (tagcase (car (as-ac)) (a i i) (c k k)))
