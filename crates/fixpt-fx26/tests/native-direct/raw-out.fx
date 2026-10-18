;;; The raw values' pieces' wrappers: the wrappers' ends (`tests/native_direct_x64_raw.rs`),
;;; `{EFF}` their effect.
(define t-bind (subr {EFF} ((listof int @k)) unit)
  (lambda (ls) (if (null? ls) #u (begin (da-bind (car ls)) (t-bind (cdr ls))))))
(define t-out (subr {EFF} ((listof int @k) (listof int @k)) (listof int @k))
  (lambda (pre ls)
    (begin (t-bind ls) (da-e (cons 15 (cons 11 nil))) (da-place-stubs)
      (let* ((cs (da-callouts)) (code (da-finish)))
        (cons (list-length cs) (append cs (append pre code)))))))
(define t-bit (subr pure (bool) int) (lambda (b) (if b 1 0)))
