;;; CHECKSUM -- the Internet-style checksum of FoxNet 2.0 over a 10000000-byte
;;; buffer, read a little-endian 32-bit word at a time.
;;;
;;; Author: sweeks@sweeks.com. Based on "The Performance of FoxNet 2.0",
;;; Herb Derby, CMU-CS-99-137, June 1999.
;;; From MLton's benchmark suite (benchmark/tests/checksum.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): (doit 2), checksumming the same buffer twice.
;;; Answer: 0, the checksum of a buffer of zeros (the original checks for it).
;;;
;;; Word32 arithmetic is int arithmetic masked to 32 bits: `>> (w, 0w16)` is
;;; (quotient w 65536), `andb (w, 0wxFFFF)` is (modulo w 65536), and each
;;; sum is taken (modulo _ 4294967296). FX-26 has no bitwise operations.
;;; The Word8Array is a bloblet of bytes, and PackWord32Little.subArr reads
;;; four of them, least significant first.

(define-type buffer (bloblet (fields) @b))

(define word32 int 4294967296)

(define* check-one (subr pure (int int) int)
  (lambda (new ac)
    (modulo (+ (modulo (+ ac (quotient new 65536)) word32) (modulo new 65536)) word32)))

;; PackWord32Little.subArr (buf, i): the ith 32-bit word, little-endian.
(define sub-arr (subr (read @b) (buffer int) int)
  (lambda (buf i)
    (let ((at (* i 4)))
      (+ (bloblet-byte buf at)
         (* 256 (+ (bloblet-byte buf (+ at 1))
                   (* 256 (+ (bloblet-byte buf (+ at 2))
                             (* 256 (bloblet-byte buf (+ at 3)))))))))))

(define* fold (subr (maxeff (read @b) spin) ((subr (read (globals word32)) (int int) int) int buffer int int) int)
  (lambda (f b buf first last)
    (letrec ((loop (subr (maxeff (read @b) spin (read (globals sub-arr word32))) (int int) int)
               (lambda (i ac)
                 (if (> i last)
                     ac
                     (loop (+ i 1) (f (sub-arr buf i) ac))))))
      (loop first b))))

(define* checksum (subr (maxeff (read @b) spin) (buffer int int) int)
  (lambda (buf first last) (fold check-one 0 buf first last)))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define size int 10000000)
(define iterations int 2)

(define* doit (subr (maxeff (alloc @b) (read @b) spin) (int) int)
  (lambda (n)
    (let* ((first 0)
           (buf (the buffer (make-bloblet size)))
           (bytes-per-word 4)
           (last (- (quotient size bytes-per-word) 1)))
      (letrec ((loop (subr (maxeff (read @b) spin (read (globals checksum check-one fold sub-arr word32))) (int int) int)
                 (lambda (n result)
                   (if (= n 0) result (loop (- n 1) (checksum buf first last))))))
        (loop n -1)))))
(doit iterations)
