; Rejected: a shadowing name is another binding, not the one checked.
(define f (subr pure ((listof int const) (listof int const)) (listof int acyclic))
  (lambda (xs ys) (if (acyclic? xs) (let ((xs ys)) (certify-acyclic xs)) nil)))
