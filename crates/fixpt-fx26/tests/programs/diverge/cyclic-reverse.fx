;;; A list made cyclic, given to a primitive that walks it: an error, "a
;;; proper list" expected, not a loop that no step limit stops. `reverse`
;;; says no `spin`, so it must end.
(define f (subr (maxeff (read @r) (write @r) (alloc @r)) () (listof int @r))
  (lambda ()
    (let ((xs (the (listof int @r) (cons 1 (cons 2 nil)))))
      (begin (set-cdr! (cdr xs) xs) (reverse xs)))))
(f)
