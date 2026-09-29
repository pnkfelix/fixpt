;;; BV2STRING -- Tests of string <-> bytevector conversions.
;;;
;;; Copyright 2007 William D Clinger.
;;;
;;; Permission to copy this software, in whole or in part, to use this
;;; software for any lawful purpose, and to redistribute this software
;;; is granted subject to the restriction that all copies made of this
;;; software must include this copyright notice in full.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/bv2string.scm),
;;; ported to FX-26. Larceny's input: 100 iterations of
;;; (string-bytevector-tests 1000 1000), then (length failed-tests).
;;; Answer: 0.
;;;
;;; What the port changed, and why:
;;; - A bytevector is a bloblet with no fields and a byte suffix,
;;;   `(bloblet (fields) @heap)`: `make-bytevector` is `make-bloblet`,
;;;   `bytevector-u8-set!`/`-ref` are `bloblet-set-byte!`/`bloblet-byte`,
;;;   `bytevector-length` is `bloblet-bytes`.
;;; - FX-26 has no `utf8->string` or `string->utf8`, which in Larceny are
;;;   runtime procedures and are what this benchmark measures. They are
;;;   written here, in FX-26, as full UTF-8 codecs (not just the ASCII the
;;;   test feeds them): the decoder turns each byte that does not begin
;;;   a well-formed sequence into U+FFFD; the encoder counts the bytes,
;;;   makes the bytevector, then fills it. FX-26's strings are immutable, so
;;;   the decoder builds a list of characters and then `list->string`.
;;; - `remainder` is `modulo` (every operand here is nonnegative), and
;;;   `(zero? q)` is `(= q 0)`.
;;; - `test` compares booleans with `bool=?` (for `equal?`), and on failure
;;;   only records the name: FX-26 has no `display`. No test fails.
;;; - `(length failed-tests)` is `strings-length`, a walk written here:
;;;   FX-26's `length` takes only lists known to be acyclic, and
;;;   `failed-tests` is a mutable list in a reference.
;;; - `random-bytevector2` and `random-bytevector4` are defined but never
;;;   called in the original; they are left out.
;;; - The generator's state `x` and its constants are a `let` around the
;;;   `letrec` rather than members of it (FX-26's `letrec` binds only
;;;   procedures); `x` is a `(ref int @heap)`, fresh on each call, as the
;;;   original's is.

(define-type bytevector (bloblet (fields) @heap))
(define-type chars (listof char @heap))
(define-type strings (listof string @heap))

;;; UTF-8, the runtime's part.

(define* utf8-continuation? (subr pure (int) bool)
  (lambda (b) (and (>= b 128) (< b 192))))

;; The scalar value of the sequence of `w` bytes at `i`, or -1 if it is
;; malformed, overlong, a surrogate, or beyond U+10FFFF.
(define* utf8-scalar (subr (read @heap) (bytevector int int int) int)
  (lambda (bv i n w)
    (if (> (+ i w) n)
        -1
        (let ((b0 (bloblet-byte bv i)))
          (cond ((= w 2)
                 (let ((b1 (bloblet-byte bv (+ i 1))))
                   (if (utf8-continuation? b1)
                       (+ (* (- b0 192) 64) (- b1 128))
                       -1)))
                ((= w 3)
                 (let ((b1 (bloblet-byte bv (+ i 1)))
                       (b2 (bloblet-byte bv (+ i 2))))
                   (if (and (utf8-continuation? b1) (utf8-continuation? b2))
                       (let ((cp (+ (* (- b0 224) 4096)
                                    (+ (* (- b1 128) 64) (- b2 128)))))
                         (if (or (< cp 2048) (and (>= cp 55296) (< cp 57344)))
                             -1
                             cp))
                       -1)))
                (else
                 (let ((b1 (bloblet-byte bv (+ i 1)))
                       (b2 (bloblet-byte bv (+ i 2)))
                       (b3 (bloblet-byte bv (+ i 3))))
                   (if (and (utf8-continuation? b1)
                            (and (utf8-continuation? b2) (utf8-continuation? b3)))
                       (let ((cp (+ (* (- b0 240) 262144)
                                    (+ (* (- b1 128) 4096)
                                       (+ (* (- b2 128) 64) (- b3 128))))))
                         (if (or (< cp 65536) (> cp 1114111)) -1 cp))
                       -1))))))))

;; How many bytes the sequence led by `b0` should have; 0 if `b0` leads none.
(define* utf8-width (subr pure (int) int)
  (lambda (b0)
    (cond ((< b0 128) 1)
          ((< b0 194) 0)
          ((< b0 224) 2)
          ((< b0 240) 3)
          ((< b0 245) 4)
          (else 0))))

(define* utf8-decode (subr (maxeff (read @heap) (alloc @heap) spin) (bytevector int int chars) chars)
  (lambda (bv i n acc)
    (if (>= i n)
        (reverse acc)
        (let ((b0 (bloblet-byte bv i)))
          (if (< b0 128)
              (utf8-decode bv (+ i 1) n (cons (integer->char b0) acc))
              (let ((w (utf8-width b0)))
                (let ((cp (if (= w 0) -1 (utf8-scalar bv i n w))))
                  (if (< cp 0)
                      (utf8-decode bv (+ i 1) n (cons (integer->char 65533) acc))
                      (utf8-decode bv (+ i w) n (cons (integer->char cp) acc))))))))))

(define* utf8->string (subr (maxeff (read @heap) (alloc @heap) spin) (bytevector) string)
  (lambda (bv) (list->string (utf8-decode bv 0 (bloblet-bytes bv) nil))))

(define* utf8-encoded-width (subr pure (int) int)
  (lambda (cp)
    (cond ((< cp 128) 1)
          ((< cp 2048) 2)
          ((< cp 65536) 3)
          (else 4))))

(define* utf8-length (subr spin (string int int int) int)
  (lambda (s i n acc)
    (if (= i n)
        acc
        (utf8-length s (+ i 1) n
                     (+ acc (utf8-encoded-width (char->integer (string-ref s i))))))))

;; Writes the characters of `s` from `i` into `bv` from `j`.
(define* utf8-encode (subr (maxeff (write @heap) spin) (string int int bytevector int) unit)
  (lambda (s i n bv j)
    (if (= i n)
        #u
        (let ((cp (char->integer (string-ref s i))))
          (cond ((< cp 128)
                 (begin (bloblet-set-byte! bv j cp)
                        (utf8-encode s (+ i 1) n bv (+ j 1))))
                ((< cp 2048)
                 (begin (bloblet-set-byte! bv j (+ 192 (quotient cp 64)))
                        (bloblet-set-byte! bv (+ j 1) (+ 128 (modulo cp 64)))
                        (utf8-encode s (+ i 1) n bv (+ j 2))))
                ((< cp 65536)
                 (begin (bloblet-set-byte! bv j (+ 224 (quotient cp 4096)))
                        (bloblet-set-byte! bv (+ j 1) (+ 128 (modulo (quotient cp 64) 64)))
                        (bloblet-set-byte! bv (+ j 2) (+ 128 (modulo cp 64)))
                        (utf8-encode s (+ i 1) n bv (+ j 3))))
                (else
                 (begin (bloblet-set-byte! bv j (+ 240 (quotient cp 262144)))
                        (bloblet-set-byte! bv (+ j 1) (+ 128 (modulo (quotient cp 4096) 64)))
                        (bloblet-set-byte! bv (+ j 2) (+ 128 (modulo (quotient cp 64) 64)))
                        (bloblet-set-byte! bv (+ j 3) (+ 128 (modulo cp 64)))
                        (utf8-encode s (+ i 1) n bv (+ j 4)))))))))

(define* string->utf8 (subr (maxeff (write @heap) (alloc @heap) spin) (string) bytevector)
  (lambda (s)
    (let ((n (string-length s)))
      (let ((bv (the bytevector (make-bloblet (utf8-length s 0 n 0)))))
        (begin (utf8-encode s 0 n bv 0) bv)))))

;;; Crude test rig, just for benchmarking.

(define failed-tests (ref strings @heap) (new nil))

(define* bool=? (subr pure (bool bool) bool)
  (lambda (a b) (if a b (not b))))

(define* test (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (string bool bool) unit)
  (lambda (name actual expected)
    (if (not (bool=? actual expected))
        (set failed-tests (cons name (get failed-tests)))
        #u)))

;;; We're limited to Ascii strings here because the R7RS doesn't
;;; actually require anything beyond Ascii.

;;; Basic sanity tests, followed by stress tests on random inputs.

(define* string-bytevector-tests
  (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) unit)
  (lambda (random-stress-tests random-stress-test-max-size)
    (let ((a 701)
          (x (the (ref int @heap) (new 1)))
          (c 743483)
          (m 524287))
      (letrec ((test-roundtrip
                (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin
                              (read (globals utf8->string string->utf8 test bool=? failed-tests
                                             utf8-continuation? utf8-decode utf8-encode
                                             utf8-encoded-width utf8-length utf8-scalar utf8-width)))
                      (bytevector) unit)
                (lambda (bvec)
                  (let* ((s1 (utf8->string bvec))
                         (b2 (string->utf8 s1))
                         (s2 (utf8->string b2)))
                    (test "round trip of string conversion" (string=? s1 s2) #t))))

               ;; This random number generator doesn't have to be good.
               ;; It just has to be fast.
               (random14
                (subr (maxeff (read @heap) (write @heap)) (int) int)
                (lambda (n)
                  (begin
                    (set x (modulo (+ (* a (get x)) c) (+ m 1)))
                    (modulo (quotient (get x) 8) n))))
               (loop
                (subr (maxeff (read @heap) (write @heap) spin) (int int int) int)
                (lambda (q r n)
                  (if (= q 0)
                      (modulo r n)
                      (loop (quotient q 16384)
                            (+ (* 16384 r) (random14 16384))
                            n))))
               (random
                (subr (maxeff (read @heap) (write @heap) spin) (int) int)
                (lambda (n)
                  (if (< n 16384)
                      (random14 n)
                      (loop (quotient n 16384) (random14 16384) n))))

               ;; Returns a random bytevector of length up to n,
               ;; with all elements less than 128.
               (random-bytevector
                (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) bytevector)
                (lambda (n0)
                  (let* ((n (random n0))
                         (bv (the bytevector (make-bloblet n))))
                    (letrec ((fill (subr (maxeff (read @heap) (write @heap) spin) (int) bytevector)
                               (lambda (i)
                                 (if (= i n)
                                     bv
                                     (begin (bloblet-set-byte! bv i (random 128))
                                            (fill (+ i 1)))))))
                      (fill 0)))))

               (stress
                (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin
                              (read (globals utf8->string string->utf8 test bool=? failed-tests
                                             utf8-continuation? utf8-decode utf8-encode
                                             utf8-encoded-width utf8-length utf8-scalar utf8-width)))
                      (int) unit)
                (lambda (i)
                  (if (= i random-stress-tests)
                      #u
                      (begin
                        (test-roundtrip (random-bytevector random-stress-test-max-size))
                        (stress (+ i 1)))))))
        (begin
          (test-roundtrip (random-bytevector 10))
          (stress 0))))))

;; `length`, which FX-26 gives only to lists it knows are acyclic.
(define* strings-length (subr (maxeff (read @heap) spin) (strings int) int)
  (lambda (l n) (if (null? l) n (strings-length (cdr l) (+ n 1)))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 1000)
(define input2 int 1000)
(define iterations int 100)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) int)
  (lambda (i result)
    (if (= i 0)
        result
        (run (- i 1)
             (begin (string-bytevector-tests input1 input2)
                    (strings-length (get failed-tests) 0))))))
(run iterations -1)
