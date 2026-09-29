;;; The fixed-width integers wrap (docs/fx26.md): FNV-1a of a string in
;;; u32, i32's largest plus one, u64's all-ones squared, and shifts.
(define* fnv (subr (maxeff (read @heap) spin) (u32 (listof char @heap)) u32)
  (lambda (h cs)
    (if (null? cs) h (fnv (u32* (u32-xor h (int->u32 (char->integer (car cs)))) (int->u32 16777619)) (cdr cs)))))
(u32->int (fnv (int->u32 2166136261) (string->list "hello")))
(i32->int (i32+ (int->i32 2147483647) (int->i32 1)))
(u64->int (u64* (int->u64 -1) (int->u64 -1)))
(cons (i64->int (i64-shr (int->i64 -16) 2))
      (cons (u32->int (u32-shr (int->u32 -16) 2))
            (cons (i32->int (i32-remainder (int->i32 -7) (int->i32 2))) (the (listof int @heap) nil))))
