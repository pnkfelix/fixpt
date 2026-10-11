;;; Shift counts past a fixnum (kayak's report, 2026-10-11): a fixed-width
;;; shift takes any count modulo its width, a bignum's too; `arithmetic-shift`
;;; by one is 0 or -1 to the right, 0 of 0. Each count passed in, so that no
;;; compiler folds it: natively a bignum's pointer's bits were taken for it.
(define-type ints (listof int @heap))
(define* counts (subr (alloc @heap) (int int int) ints)
  (lambda (big odd neg)
    (list (u32->int (u32-shl (int->u32 1) big)) (u32->int (u32-shl (int->u32 1) odd))
          (u32->int (u32-shl (int->u32 1) neg)) (u64->int (u64-shl (int->u64 1) big))
          (u64->int (u64-shl (int->u64 1) odd)) (u64->int (u64-shl (int->u64 1) neg))
          (i64->int (i64-shr (int->i64 -8) odd)) (i64->int (i64-shr (int->i64 -8) neg))
          (i32->int (i32-shl (int->i32 3) odd)) (u64->int (u64-shr (int->u64 1024) odd))
          (arithmetic-shift 5 (- 0 big)) (arithmetic-shift -5 (- 0 big)) (arithmetic-shift 0 big))))
(define* shift-counts (subr (alloc @heap) (int) ints)
  (lambda (z)
    (counts (+ 1152921504606846975 z) (+ 4611686018427387904 z) (- -1152921504606846978 (- 0 z)))))
(shift-counts 1)
