; Bytevectors (TODO.md §84): made, written and read at a region; copied,
; compared; a string's UTF-8 and back, and bytes that are not UTF-8, which
; give the offset of the first bad one. With `u8` arithmetic over them.
(define-type ints (listof int @heap))
(define* sum-bytes (subr (maxeff (read @b) spin) ((bytevectorof @b) int int) int)
  (lambda (bv i acc)
    (if (>= i (bytevector-length bv))
        acc
        (sum-bytes bv (+ i 1) (+ acc (bytevector-u8-ref bv i))))))
;; FNV-1a over bytes, in `u32`, as a hash of a file's contents would be.
(define* fnv (subr (maxeff (read @b) spin) ((bytevectorof @b) int u32) u32)
  (lambda (bv i h)
    (if (>= i (bytevector-length bv))
        h
        (fnv bv (+ i 1)
             (u32* (u32-xor h (int->u32 (bytevector-u8-ref bv i))) (int->u32 16777619))))))
;; Each byte doubled, wrapping as a `u8` does.
(define* doubled! (subr (maxeff (read @b) (write @b) spin) ((bytevectorof @b) int) unit)
  (lambda (bv i)
    (if (>= i (bytevector-length bv))
        #u
        (begin (bytevector-u8-set! bv i (u8* (bytevector-u8-ref bv i) (int->u8 2)))
               (doubled! bv (+ i 1))))))
(define* text-length (subr (read @b) ((bytevectorof @b)) int)
  (lambda (bv) (tagcase (utf8->string bv) (text s (string-length s)) (bad k (- 0 k)))))
(define* bytes (subr (maxeff (read (globals sum-bytes fnv doubled! text-length)) (alloc @heap)
                           (alloc @b) (read @b) (write @b) spin)
                     () ints)
  (lambda ()
    (let ((bv (the (bytevectorof @b) (make-bytevector 4 (int->u8 7))))
          (hi (the (bytevectorof @b) (string->utf8 "héllo, wörld")))
          (none (the (bytevectorof @b) (make-bytevector 0 (int->u8 0)))))
      (begin
        (bytevector-u8-set! bv 1 (int->u8 250))
        (bytevector-copy! bv 2 hi 0 2)
        (let ((before (sum-bytes bv 0 0)))
          (begin
            (doubled! bv 0)
            (list before (sum-bytes bv 0 0) (bytevector-length hi) (bytevector-length none)
                  (if (bytevector=? bv (the (bytevectorof @b) (bytevector-copy bv 0 4))) 1 0)
                  (if (bytevector=? bv hi) 1 0)
                  (text-length hi)
                  (text-length (the (bytevectorof @b) (bytevector-copy hi 0 2)))
                  (text-length (the (bytevectorof @b) (bytevector-copy hi 3 14)))
                  (text-length none)
                  (u32->int (fnv hi 0 (int->u32 2166136261))))))))))
(bytes)
