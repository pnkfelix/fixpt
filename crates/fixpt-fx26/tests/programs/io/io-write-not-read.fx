; Rejected: writing a file is `(io fs-write)`, which a procedure declared to
; only read files does not cover (TODO.md §84).
(define save (subr (maxeff (io fs-read) (alloc @b) (read @b)) (string) bool)
  (lambda (path)
    (tagcase (write-file path (the (bytevectorof @b) (make-bytevector 1 (int->u8 0))))
      (done u #t)
      (failed e #f))))
