;;; Blobrefs natively (`TODO.md` §77): every scalar written and read through
;;; one, in line where the inline path can and by the primitive where it
;;; cannot (an `i64` past a fixnum); a read at an odd offset; steps,
;;; owners and offsets; and a loop that allocates as it walks, so that a
;;; collection moves the owner under the refs it holds.
(define-type o (bloblet (fields int) @heap))
(define* walk (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin)
                    ((blobref o i64) int int) int)
  (lambda (r i acc)
    (if (= i 0)
        acc
        (begin
          (blobref-set! r (int->i64 i))
          (let ((junk (list i i i)))
            (walk (blobref+ r 8) (- i 1) (+ acc (i64->int (blobref-get r)))))))))
(define-type ints (listof int @heap))
(define* blobrefs (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (int) ints)
  (lambda (k)
    (let* ((b (the o (make-bloblet 64 k)))
           (x (the (blobref o f64) (blobref-at b 0)))
           (f (the (blobref o f32) (blobref-at b 8)))
           (s (the (blobref o i32) (blobref+ f 4)))
           (u (the (blobref o u32) (blobref-at b 16)))
           (w (the (blobref o i64) (blobref-at b 24)))
           (v (the (blobref o u64) (blobref-at b 32)))
           (odd (the (blobref o i32) (blobref-at b 41)))
           (big (i64* (int->i64 3037000499) (int->i64 3037000499))))
      (begin
        (blobref-set! x (int->f64 (+ k 3)))
        (blobref-set! f (int->f32 (+ k 2)))
        (blobref-set! s (int->i32 (- 0 k)))
        (blobref-set! u (int->u32 4000000000))
        (blobref-set! w big)
        (blobref-set! v (int->u64 12345678901234567))
        (blobref-set! odd (int->i32 -7))
        (list (f64->int (blobref-get x)) (f32->int (blobref-get f)) (i32->int (blobref-get s))
              (u32->int (blobref-get u)) (i64->int (blobref-get w)) (u64->int (blobref-get v))
              (i32->int (blobref-get odd)) (blobref-offset s) (bloblet-ref (blobref-owner odd) 0)
              (walk (the (blobref o i64) (blobref-at (the o (make-bloblet 808 0)) 0)) 100 0))))))
(blobrefs 5)
