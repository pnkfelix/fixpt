;;; A list of characters made cyclic, given to `list->string`, which walks
;;; it to count it: an error, "a proper list" expected, not a loop.
(define f (subr (maxeff (read @r) (write @r) (alloc @r)) () string)
  (lambda ()
    (let ((cs (the (listof char @r) (list #\a #\b))))
      (begin (set-cdr! (cdr cs) cs) (list->string cs)))))
(f)
