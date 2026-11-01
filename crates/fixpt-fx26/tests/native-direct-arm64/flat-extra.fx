;;; Wrappers of their own shapes (`native_direct_arm64_flat.rs`), `{EFF}` their effect.
(define t-shape-fast (subr {EFF} (string) (listof int @k))
  (lambda (name)
    (begin (ada-reset 10)
      (let* ((l0 (ada-label)) (known (adf-shape-fast name l0)))
        (t-out (cons (t-bit known) nil) (cons l0 nil))))))
