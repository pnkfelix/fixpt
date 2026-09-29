;;; The fixed-width integers wrap (docs/fx26.md): FNV-1a of a string in
;;; u32, i32's largest plus one, u64's all-ones squared, and shifts.
(define fnv-step (subr pure (u32 char) u32)
  (lambda (h c) (u32* (u32-xor h (int->u32 (char->integer c))) (int->u32 16777619))))
(define* fnv (subr (maxeff (read @heap) spin) (u32 (listof char @heap)) u32)
  (lambda (h cs)
    (if (null? cs) h (fnv (fnv-step h (car cs)) (cdr cs)))))
(u32->int (fnv (int->u32 2166136261) (string->list "hello")))
(i32->int (i32+ (int->i32 2147483647) (int->i32 1)))
(u64->int (u64* (int->u64 -1) (int->u64 -1)))
(let ((i64-shifted (i64->int (i64-shr (int->i64 -16) 2)))
      (u32-shifted (u32->int (u32-shr (int->u32 -16) 2)))
      (remainder (i32->int (i32-remainder (int->i32 -7) (int->i32 2)))))
  (cons i64-shifted (cons u32-shifted (cons remainder (the (listof int @heap) nil)))))
