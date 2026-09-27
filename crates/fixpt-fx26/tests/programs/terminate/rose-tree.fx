; Rejected, though it ends: a limit of the analysis. `each` walks `kids`,
; but `ks` is its own parameter, so nothing says `(car ks)` is a part of
; `t`; `total` must say `spin`, and so must `each`, which calls it.
(define-type rose (sumof (leaf int) (node (listof rose finite))))
(define total (subr pure (rose) int)
  (lambda (t)
    (tagcase t
      (leaf n n)
      (node kids
        (letrec ((each (subr pure ((listof rose finite) int) int)
                   (lambda (ks acc) (if (null? ks) acc (each (cdr ks) (+ acc (total (car ks))))))))
          (each kids 0))))))
