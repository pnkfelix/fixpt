;;; The native convention's compiler to arm64 written in FX-26: the fast
;;; paths of the primitives that never collect (`pure_fast`) and `string=?`
;;; (`string_eq`), each the instructions of `direct.rs`'s own, step for
;;; step. Apart from `native-direct-arm64-prims.fx`, as x86_64's strings
;;; are, which makes it of the modules it is given and gives on all it
;;; defines. A file of one expression (`load-input`, `TODO.md` §68).

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (arm-direct-types (load-module "fx26:native-direct-arm64-types.fx"))
       (layout-types (load-module "fx26:native-direct-arm64-layout-types.fx"))
       (arm64-types (load-module "fx26:arm64-types.fx")))
  (lambda ((arm (select arm64-types arm64-direct-sig))
           (dl (select layout-types native-direct-arm64-layout-sig))
           (asm (select arm-direct-types native-direct-arm64-asm-sig))
           (raw (select arm-direct-types native-direct-arm64-raw-sig))
           (flat (select arm-direct-types native-direct-arm64-flat-sig)))
    (module
(hide (include direct-types) (include arm-direct-types))
(hide (include arm) (include dl) (include asm) (include raw) (include flat))

;; Whether `s` begins with `pre`, and what follows it.
(define adq-starts? (subr pure (string string) bool)
  (lambda (s pre)
    (let ((n (string-length s)) (m (string-length pre)))
      (and (>= n m) (string=? (substring s 0 m) pre)))))
(define adq-after (subr pure (string string) string)
  (lambda (s pre) (substring s (string-length pre) (string-length s))))

;;; ------------------------------------------------------------ `string_eq`

;; `string=?` of the strings in `x` and `y`, into `RESULT`: their lengths,
;; then their characters, 32 bits each, as register code's. Uses X9 and
;; X13 to X16.
(define adq-string-eq (subr da-assembles (int int) unit)
  (lambda (x y)
    (let ((again (ada-label)) (yes (ada-label)) (no (ada-label)) (end (ada-label)))
      (begin
        (ada-e (arm-ldur d-x15 x -4))
        (ada-e (arm-ldur d-x16 y -4))
        (ada-e (arm-cmp d-x15 d-x16))
        (ada-bc ada-c-ne no)
        (ada-mov d-x13 x)
        (ada-mov d-x14 y)
        (ada-bind again)
        (ada-e (arm-cmp-imm d-x15 0))
        (ada-bc ada-c-eq yes)
        (ada-e (arm-ldur-w d-x9 d-x13 4))
        (ada-e (arm-ldur-w d-x16 d-x14 4))
        (ada-e (arm-cmp d-x9 d-x16))
        (ada-bc ada-c-ne no)
        (ada-e (arm-add-imm d-x13 d-x13 4))
        (ada-e (arm-add-imm d-x14 d-x14 4))
        (ada-e (arm-sub-imm d-x15 d-x15 1))
        (ada-b again)
        (ada-bind yes)
        (ada-imm d-result d-true)
        (ada-b end)
        (ada-bind no)
        (ada-imm d-result d-false)
        (ada-bind end)))))

;;; ------------------------------------------------------------ `pure_fast`

;; The fast path of primitive `name`, one that never collects and no
;; operation of `i64` or `u64` (those are `raw_fast`'s), on `RESULT` and
;; `y`, into `RESULT`, going to `slow` for what it leaves to the primitive:
;; #f if it has none. Uses X13 to X16.
(define adq-fixnums (subr da-assembles (int int) unit)
  (lambda (y slow)
    (begin (ada-e (arm-orr d-x13 d-result y)) (ada-e (arm-tst-low d-x13 3))
           (ada-bc ada-c-ne slow))))
(define adq-nonzero (subr da-assembles (int int) unit)
  (lambda (y slow) (begin (ada-e (arm-cmp-imm y 0)) (ada-bc ada-c-eq slow))))

(define adq-pure-fast (subr da-assembles (string int int) bool)
  (lambda (name y slow)
    (let ((x d-result))
      (cond
        ((adf-shape-fast name slow) #t)
        ;; A product in 61 bits, or `slow`: the high word only the low's sign.
        ((string=? name "%fx26-mul")
         (begin (adq-fixnums y slow)
                (ada-e (arm-asr-imm d-x14 y 3))
                (ada-e (arm-mul d-x13 x d-x14))
                (ada-e (arm-smulh d-x15 x d-x14))
                (ada-e (arm-asr-imm d-x16 d-x13 63))
                (ada-e (arm-cmp d-x15 d-x16))
                (ada-bc ada-c-ne slow)
                (ada-mov d-result d-x13)
                #t))
        ((or (string=? name "%fx26-quotient") (string=? name "modulo")
             (string=? name "%fx26-remainder"))
         (begin (adq-fixnums y slow) (adq-nonzero y slow)
                (ada-e (arm-sdiv d-x13 x y))
                (cond ((string=? name "%fx26-quotient")
                       (begin (ada-e (arm-lsl-imm d-x14 d-x13 3))
                              (ada-e (arm-asr-imm d-x15 d-x14 3))
                              (ada-e (arm-cmp d-x15 d-x13)) (ada-bc ada-c-ne slow)))
                      ((string=? name "%fx26-remainder") (ada-e (arm-msub d-x14 d-x13 y x)))
                      (else (adq-modulo y)))
                (ada-mov d-result d-x14)
                #t))
        ((string=? name "%fx26-arithmetic-shift") (begin (adq-shift y slow) #t))
        ;; A bloblet's count of fields: its trailer's distance.
        ((string=? name "%bloblet-fields")
         (begin
           (ada-e (arm-and-low d-x13 x 3)) (ada-e (arm-cmp-imm d-x13 d-tag-bloblet))
           (ada-bc ada-c-ne slow)
           (ada-e (arm-ldur d-x16 x (ada-field-off 1)))
           (ada-e (arm-and-low d-x13 d-x16 3)) (ada-e (arm-cmp-imm d-x13 d-tag-trailer))
           (ada-bc ada-c-ne slow)
           (ada-e (arm-ubfx d-x16 d-x16 d-t-distance-lo 32))
           (ada-e (arm-lsl-imm d-result d-x16 3))
           #t))
        ;; A bytevector's length, a byte at its index; a string's, 32 bits
        ;; each.
        ((or (string=? name "bytevector-length") (string=? name "string-length"))
         (begin (ada-e (arm-ldur d-x13 x -4)) (ada-e (arm-lsl-imm d-result d-x13 3)) #t))
        ((string=? name "bytevector-u8-ref")
         (begin
           (adq-index y slow)
           (ada-e (arm-add d-x13 x d-x15))
           (ada-e (arm-ldurb d-x16 d-x13 4))
           (ada-e (arm-lsl-imm d-result d-x16 3))
           #t))
        ((string=? name "string-ref")
         (begin
           (adq-index y slow)
           (ada-e (arm-add-lsl d-x13 x d-x15 2))
           (ada-e (arm-ldur-w d-x16 d-x13 4))
           (ada-imm d-x14 d-char0)
           (ada-e (arm-add-lsl d-result d-x14 d-x16 8))
           #t))
        ((string=? name "%fx26-flatarray-length")
         (begin (adf-flat-count x d-x13) (ada-e (arm-lsl-imm d-result d-x13 3)) #t))
        ((string=? name "%fx26-flatarray-ref") (begin (adf-flat-ref y slow) #t))
        ((or (string=? name "%suffix-ref-offset") (string=? name "%suffix-ref-owner"))
         (begin (adq-suffix-part name slow) #t))
        ((string=? name "%suffix-ref+") (begin (adq-suffix-plus y slow) #t))
        ((adq-starts? name "%fx26-") (adq-small (adq-after name "%fx26-") y slow))
        (else #f)))))

;; `y`, a fixnum, an index below the length the word before `RESULT`'s
;; bytes: its value in X15, the length in X14.
(define adq-index (subr da-assembles (int int) unit)
  (lambda (y slow)
    (begin
      (ada-check-fixnum y slow)
      (ada-e (arm-ldur d-x14 d-result -4))
      (ada-e (arm-asr-imm d-x15 y 3))
      (ada-e (arm-cmp d-x15 d-x14))
      (ada-bc ada-c-hs slow))))
;; The remainder in X14 given the divisor's sign, or 0.
(define adq-modulo (subr da-assembles (int) unit)
  (lambda (y)
    (let ((signed (ada-label)))
      (begin
        (ada-e (arm-msub d-x14 d-x13 y d-result))
        (ada-e (arm-cmp-imm d-x14 0))
        (ada-bc ada-c-eq signed)
        (ada-e (arm-eor d-x15 d-x14 y))
        (ada-e (arm-cmp-imm d-x15 0))
        (ada-bc ada-c-ge signed)
        (ada-e (arm-add d-x14 d-x14 y))
        (ada-bind signed)))))
;; Left by fewer than 61 while the result stays a fixnum; right (floor) by
;; fewer than 63.
(define adq-shift (subr da-assembles (int int) unit)
  (lambda (y slow)
    (let ((right (ada-label)) (done (ada-label)) (x d-result))
      (begin
        (adq-fixnums y slow)
        (ada-e (arm-asr-imm d-x14 y 3))
        (ada-e (arm-cmp d-x14 d-xzr))
        (ada-bc ada-c-lt right)
        (ada-e (arm-cmp-imm d-x14 61))
        (ada-bc ada-c-ge slow)
        (ada-e (arm-lslv d-x13 x d-x14))
        (ada-e (arm-asrv d-x15 d-x13 d-x14))
        (ada-e (arm-cmp d-x15 x))
        (ada-bc ada-c-ne slow)
        (ada-mov d-result d-x13)
        (ada-b done)
        (ada-bind right)
        (ada-e (arm-sub d-x14 d-xzr d-x14))
        (ada-e (arm-cmp-imm d-x14 63))
        (ada-bc ada-c-hs slow)
        (ada-e (arm-asrv d-x13 x d-x14))
        (ada-e (arm-asr-imm d-x13 d-x13 3))
        (ada-e (arm-lsl-imm d-result d-x13 3))
        (ada-bind done)))))
;; A suffix ref's offset, and its owner, a bloblet.
(define adq-suffix-part (subr da-assembles (string int) unit)
  (lambda (name slow)
    (let ((x d-result))
      (begin
        (ada-e (arm-and-low d-x16 x 3))
        (ada-e (arm-cmp-imm d-x16 d-tag-suffix-ref))
        (ada-bc ada-c-ne slow)
        (if (string=? name "%suffix-ref-offset")
            (begin (ada-e (arm-lsr-imm d-x13 x d-suffix-offset-shift))
                   (ada-e (arm-lsl-imm d-result d-x13 3)))
            (begin (ada-e (arm-ubfx d-x14 x 3 d-suffix-owner-bits))
                   (ada-ld d-x9 d-st d-st-words)
                   (ada-e (arm-add-lsl d-x11 d-x9 d-x14 3))
                   (ada-e (arm-add-imm d-result d-x11 d-tag-bloblet))))))))
;; `y` bytes along: still in the owner's suffix, the offset rebuilt.
(define adq-suffix-plus (subr da-assembles (int int) unit)
  (lambda (y slow)
    (let ((x d-result))
      (begin
        (ada-check-fixnum y slow)
        (adf-suffix-owner x slow)
        (ada-e (arm-asr-imm d-x9 y 3))
        (ada-e (arm-add d-x9 d-x15 d-x9))
        (ada-e (arm-cmp d-x9 d-x13))
        (ada-bc ada-c-hs slow)
        (ada-e (arm-ubfx d-x14 x 0 d-suffix-offset-shift))
        (ada-e (arm-lsl-imm d-x9 d-x9 d-suffix-offset-shift))
        (ada-e (arm-orr d-result d-x14 d-x9))))))

;; The fixnum-shaped widths: `i8`, `u8`, `i32`, `u32`'s bits, 0 for none,
;; and whether signed.
(define adq-bits (subr pure (string) int)
  (lambda (t)
    (cond ((or (string=? t "i8") (string=? t "u8")) 8)
          ((or (string=? t "i32") (string=? t "u32")) 32)
          (else 0))))
(define adq-signed? (subr pure (string) bool) (lambda (t) (adq-starts? t "i")))
;; The width `rest` begins with, an operation after it not beginning with a
;; digit; "" for none.
(define adq-digit? (subr pure (string) bool)
  (lambda (op)
    (and (> (string-length op) 0)
         (let ((c (substring op 0 1))) (and (string<? "/" c) (string<? c ":"))))))
(define adq-width? (subr pure (string string) bool)
  (lambda (rest t) (and (adq-starts? rest t) (not (adq-digit? (adq-after rest t))))))
(define adq-width-of (subr pure (string) string)
  (lambda (rest)
    (cond ((adq-width? rest "i8") "i8") ((adq-width? rest "u8") "u8")
          ((adq-width? rest "i32") "i32") ((adq-width? rest "u32") "u32") (else ""))))
;; The test an operation is: its condition, -1 for none.
(define adq-test (subr pure (string) int)
  (lambda (op)
    (cond ((string=? op "<") ada-c-lt) ((string=? op "<=") ada-c-le) ((string=? op ">") ada-c-gt)
          ((string=? op ">=") ada-c-ge) ((string=? op "=") ada-c-eq) (else -1))))
;; What follows `%fx26-`: an `f32` operation, a conversion to a small
;; width, or a small width's operation, the fixnums' then wrapped.
(define adq-small (subr da-assembles (string int int) bool)
  (lambda (rest y slow)
    (let ((x d-result))
      (cond
        ((adq-starts? rest "f32") (adr-f32-fast (adq-after rest "f32") y))
        ((and (adq-starts? rest "int->") (> (adq-bits (adq-after rest "int->")) 0))
         (let ((t (adq-after rest "int->")))
           (begin (ada-check-fixnum x slow) (adr-wrap-small (adq-signed? t) (adq-bits t)) #t)))
        ((string=? (adq-width-of rest) "") #f)
        (else
         (let* ((t (adq-width-of rest)) (op (adq-after rest t)) (s (adq-signed? t))
                (bits (adq-bits t)) (tz (if (= bits 8) 3 5)) (c (adq-test op)))
           (cond
             ((>= c 0)
              (begin (ada-e (arm-cmp x y)) (ada-imm d-x13 d-true) (ada-imm d-x14 d-false)
                     (ada-e (arm-csel d-result d-x13 d-x14 c)) #t))
             ((string=? op "->int") #t)
             ((string=? op "+") (begin (ada-e (arm-add d-result x y)) (adr-wrap-small s bits) #t))
             ((string=? op "-") (begin (ada-e (arm-sub d-result x y)) (adr-wrap-small s bits) #t))
             ((string=? op "*")
              (begin (ada-e (arm-asr-imm d-x13 y 3)) (ada-e (arm-mul d-result x d-x13))
                     (adr-wrap-small s bits) #t))
             ((string=? op "-quotient")
              (begin (adq-nonzero y slow) (ada-e (arm-sdiv d-x13 x y))
                     (ada-e (arm-lsl-imm d-result d-x13 3)) (adr-wrap-small s bits) #t))
             ((string=? op "-remainder")
              (begin (adq-nonzero y slow) (ada-e (arm-sdiv d-x13 x y))
                     (ada-e (arm-msub d-result d-x13 y x)) #t))
             ((string=? op "-and") (begin (ada-e (arm-and d-result x y)) #t))
             ((string=? op "-or") (begin (ada-e (arm-orr d-result x y)) #t))
             ((string=? op "-xor") (begin (ada-e (arm-eor d-result x y)) #t))
             ((string=? op "-not")
              (begin (ada-e (arm-sub d-result d-xzr x)) (ada-e (arm-sub-imm d-result d-result 8))
                     (adr-wrap-small s bits) #t))
             ((string=? op "-shl")
              (begin (ada-check-fixnum y slow) (ada-e (arm-ubfx d-x13 y 3 tz))
                     (ada-e (arm-lslv d-result x d-x13)) (adr-wrap-small s bits) #t))
             ;; An arithmetic or logical shift right, the tag's bits cleared.
             ((string=? op "-shr")
              (begin (ada-check-fixnum y slow) (ada-e (arm-ubfx d-x13 y 3 tz))
                     (ada-e (if s (arm-asrv d-x14 x d-x13) (arm-lsrv d-x14 x d-x13)))
                     (ada-e (arm-and-bits d-result d-x14 3 61)) #t))
             (else #f))))))))
)))
