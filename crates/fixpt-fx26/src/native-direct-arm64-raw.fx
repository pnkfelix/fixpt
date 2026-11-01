;;; Raw values, and the operations native code does on them in line, in
;;; FX-26, for arm64: `direct.rs`'s `box_reg` to `int_of_f64`, `f32_fast`,
;;; `f64_fast`, `raw_compare` to `wrap_small` and `IntSlow`, step for step
;;; and instruction for instruction, each `adr-` and the Rust name
;;; (`adr-box-f64` is `box_f64`), over the native convention's assembler
;;; (`native-direct-arm64-asm.fx`). The Rust pieces are these ones' oracle
;;; (`tests/native_direct_arm64_raw.rs`).
;;;
;;; A representation (`Rep`) and a conversion (`Convert`) are numbers, as
;;; `native-reps-sig` says; an operation's name (`what`) is the string the
;;; Rust matches.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder, the layout and the
;;; assembler.

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (arm-direct-types (load-module "fx26:native-direct-arm64-types.fx"))
       (layout-types (load-module "fx26:native-direct-arm64-layout-types.fx"))
       (arm64-types (load-module "fx26:arm64-types.fx")))
  (lambda ((arm (select arm64-types arm64-direct-sig))
           (dl (select layout-types native-direct-arm64-layout-sig))
           (asm (select arm-direct-types native-direct-arm64-asm-sig)))
    (module
(hide (include direct-types) (include arm-direct-types))
(hide (include arm) (include dl) (include asm))

(define adr-bit (subr pure (bool) int) (lambda (b) (if b 1 0)))

;; The word a call that takes an `f64` value raw puts where the callee
;; returns to (`raw_f64_mark`): `movk xzr, #0xf64f, lsl #48`, which does
;; nothing, and which nothing else emits.
(define adr-raw-f64-mark int #xF2FEC9FF)

;;; ------------------------------------------------------------ boxing

;; Register `r`'s raw `i64` (signed) or `u64` boxed, in place: a fixnum
;; where it fits, else a bignum, made by a call-out.
(define adr-box-reg (subr da-assembles (int bool) unit)
  (lambda (r signed)
    (let ((slow (ada-label)) (done (ada-label)))
      (begin
        (if signed
            (begin
              (ada-e (arm-lsl-imm d-x16 r 3))
              (ada-e (arm-asr-imm d-x13 d-x16 3))
              (ada-e (arm-cmp d-x13 r))
              (ada-bc ada-c-ne slow)
              (ada-mov r d-x16))
            (begin
              (ada-e (arm-lsr-imm d-x13 r 60))
              (ada-e (arm-cmp-imm d-x13 0))
              (ada-bc ada-c-ne slow)
              (ada-e (arm-lsl-imm r r 3))))
        (ada-b done)
        (ada-bind slow)
        (ada-pure-call (ada-co d-co-box (adr-bit signed) 0) (ada-args1 r) r)
        (ada-bind done)))))

;; Register `r`'s exact integer unboxed, in place: its low 64 bits, a
;; fixnum's by a shift, a bignum's by a call-out.
(define adr-unbox-reg (subr da-assembles (int) unit)
  (lambda (r)
    (let ((slow (ada-label)) (done (ada-label)))
      (begin
        (ada-e (arm-tst-low r 3))
        (ada-bc ada-c-ne slow)
        (ada-e (arm-asr-imm r r 3))
        (ada-b done)
        (ada-bind slow)
        (ada-pure-call (ada-co d-co-unbox 0 0) (ada-args1 r) r)
        (ada-bind done)))))

;; Register `r`'s flonum unboxed, in place: its double's bits, the word its
;; pointer is 4 past; anything but a bloblet gives 0, and is not read.
(define adr-unbox-f64 (subr da-assembles (int) unit)
  (lambda (r)
    (let ((other (ada-label)) (done (ada-label)))
      (begin
        (ada-e (arm-and-low d-x16 r 3))
        (ada-e (arm-cmp-imm d-x16 d-tag-bloblet))
        (ada-bc ada-c-ne other)
        (ada-e (arm-ldur r r -4))
        (ada-b done)
        (ada-bind other)
        (ada-e (arm-movz r 0 0))
        (ada-bind done)))))

;; Register `r`'s value unboxed to `rep`.
(define adr-unbox-to (subr da-assembles (int int) unit)
  (lambda (r rep) (if (= rep 4) (adr-unbox-f64 r) (adr-unbox-reg r))))

;; After a call whose value only `f64` operations use: the value raw in
;; `RESULT`. A callee returning one raw returns 8 past the mark; any other
;; return comes to the mark, which does nothing, and the value is unboxed.
(define adr-take-raw-f64 (subr da-assembles () unit)
  (lambda ()
    (let ((boxed (ada-label)) (join (ada-label)))
      (begin
        (ada-e adr-raw-f64-mark)
        (ada-b boxed)
        (ada-b join)
        (ada-bind boxed)
        (adr-unbox-f64 d-result)
        (ada-bind join)))))

;; Register `r`'s raw `f64` boxed, in place: a flonum from the free space
;; when there is room short of the collection's threshold, else by a
;; call-out that does not collect. Uses X11 and X13 to X17.
(define adr-box-f64 (subr da-assembles (int) unit)
  (lambda (r)
    (let ((slow (ada-label)) (done (ada-label)))
      (begin
        (ada-ld d-x13 d-st d-st-top)
        (ada-ld d-x14 d-x13 0)
        (ada-ld d-x15 d-st d-st-alloc-limit)
        (ada-e (arm-add-imm d-x16 d-x14 2))
        (ada-e (arm-cmp d-x16 d-x15))
        (ada-bc ada-c-hi slow)
        (ada-ld d-x17 d-st d-st-words)
        (ada-e (arm-add-lsl d-x11 d-x17 d-x14 3))
        (ada-imm d-x17 (ada-header d-flonum 0 8))
        (ada-sto d-x17 d-x11 0)
        (ada-sto r d-x11 8)
        (ada-sto d-x16 d-x13 0)
        (ada-e (arm-add-imm r d-x11 (+ 8 d-tag-bloblet)))
        (ada-b done)
        (ada-bind slow)
        (ada-pure-call (ada-co d-co-box-f64 0 0) (ada-args1 r) r)
        (ada-bind done)))))

;; A return of the raw `f64` in `RESULT`: as it is, 8 past the return
;; address, where the caller takes it so (its mark there); else boxed, to
;; the return address.
(define adr-raw-return (subr da-assembles () unit)
  (lambda ()
    (let ((boxed (ada-label)))
      (begin
        (ada-e (arm-ldur-w d-x16 d-link 0))
        (ada-imm d-x17 adr-raw-f64-mark)
        (ada-e (arm-cmp d-x16 d-x17))
        (ada-bc ada-c-ne boxed)
        (ada-e (arm-add-imm d-link d-link 8))
        (ada-e arm-ret)
        (ada-bind boxed)
        (adr-box-f64 d-result)
        (ada-e arm-ret)))))

;; Bytes from a procedure's entry past its unboxing of the `n` parameters
;; it takes raw: one unboxing emitted, measured, and taken back.
(define adr-raw-entry-skip (subr da-assembles (int) int)
  (lambda (n)
    (let* ((m (ada-mark)) (from (ada-here)))
      (begin
        (adr-unbox-f64 1)
        (let ((words (- (ada-here) from)))
          (begin (ada-rewind m) (* 4 (* words n))))))))

;; The conversions `reps` asks for before an instruction; a test for a
;; fixnum going to `general` where it fails. `result` is where `RESULT`'s
;; value is.
(define adr-convert (subr da-assembles (da-bytes int int) unit)
  (lambda (cs general result)
    (if (null? cs)
        #u
        (let* ((c (car cs)) (kind (quotient c 128)) (r (modulo (quotient c 8) 16))
               (rep (modulo c 8)))
          (begin
            (cond ((and (= kind 0) (or (= rep 2) (= rep 3))) (adr-box-reg r (= rep 2)))
                  ((= kind 0) (adr-box-f64 r))
                  ((= kind 1) (adr-unbox-to r rep))
                  (else (ada-check-fixnum (if (= r 0) result r) general)))
            (adr-convert (cdr cs) general result))))))

;;; ------------------------------------------------------------ f64 and f32

;; `int->f64` (primitive `p`) of the int in `RESULT`, raw into `RESULT`: a
;; fixnum's by `scvtf`; a bignum's by the primitive.
(define adr-f64-of-int (subr da-assembles (int) unit)
  (lambda (p)
    (let ((slow (ada-label)) (done (ada-label)))
      (begin
        (ada-e (arm-tst-low d-result 3))
        (ada-bc ada-c-ne slow)
        (ada-e (arm-asr-imm d-x13 d-result 3))
        (ada-e (arm-scvtf 16 d-x13))
        (ada-e (arm-fmov-from-d d-result 16))
        (ada-b done)
        (ada-bind slow)
        (ada-pure-call (ada-co d-co-pure p 1) (ada-args1 d-result) d-result)
        (adr-unbox-f64 d-result)
        (ada-bind done)))))

;; `f64->int` (primitive `p`) of the raw `f64` in `RESULT`, into `RESULT`:
;; by `fcvtzs` where that is exact and a fixnum; else the primitive's, on
;; the boxed value.
(define adr-int-of-f64 (subr da-assembles (int) unit)
  (lambda (p)
    (let ((slow (ada-label)) (done (ada-label)))
      (begin
        (ada-e (arm-fmov-to-d 16 d-result))
        (ada-e (arm-fcvtzs d-x13 16))
        (ada-e (arm-scvtf 17 d-x13))
        (ada-e (arm-fcmp 16 17))
        (ada-bc ada-c-ne slow)
        (ada-e (arm-lsl-imm d-x14 d-x13 3))
        (ada-e (arm-asr-imm d-x15 d-x14 3))
        (ada-e (arm-cmp d-x15 d-x13))
        (ada-bc ada-c-ne slow)
        (ada-mov d-result d-x14)
        (ada-b done)
        (ada-bind slow)
        (adr-box-f64 d-result)
        (ada-pure-call (ada-co d-co-pure p 1) (ada-args1 d-result) d-result)
        (ada-trap-set)
        (ada-bind done)))))

;; A float comparison's condition after `fcmp`, by its name; -1 for none.
(define adr-float-test (subr pure (string) int)
  (lambda (what)
    (case what
      (("<") ada-c-mi)
      (("<=") ada-c-ls)
      ((">") ada-c-gt)
      ((">=") ada-c-ge)
      (("=") ada-c-eq)
      (else -1))))

;; `RESULT` := `#t` where `c` holds, else `#f`.
(define adr-flag (subr da-assembles (int) unit)
  (lambda (c)
    (begin
      (ada-imm d-x13 d-true)
      (ada-imm d-x14 d-false)
      (ada-e (arm-csel d-result d-x13 d-x14 c)))))

;; A double's operation `what` of `d16` (and `d17`) into `d16`, `frintn`
;; for any other; and whether `what` is one.
(define adr-float-op (subr da-assembles (string) int)
  (lambda (what)
    (case what
      (("+") (arm-fadd 16 16 17))
      (("-") (arm-fsub 16 16 17))
      (("*") (arm-fmul 16 16 17))
      (("/") (arm-fdiv 16 16 17))
      (("-abs") (arm-fabs 16 16))
      (("-neg") (arm-fneg 16 16))
      (("-sqrt") (arm-fsqrt 16 16))
      (("-floor") (arm-frintm 16 16))
      (("-ceiling") (arm-frintp 16 16))
      (("-truncate") (arm-frintz 16 16))
      (else (arm-frintn 16 16)))))
(define adr-float-op? (subr pure (string) bool)
  (lambda (what)
    (case what
      (("+" "-" "*" "/" "-abs" "-neg" "-sqrt" "-floor" "-ceiling" "-truncate" "-round") #t)
      (else #f))))

;; An `f32` operation `what` on the immediates in `RESULT` and `y`, into
;; `RESULT`, by way of `s16` and `s17`; false for one the runtime does:
;; nothing is emitted.
(define adr-f32-fast (subr da-assembles (string int) bool)
  (lambda (what y)
    (let ((test (adr-float-test what)))
      (if (and (< test 0) (not (adr-float-op? what)))
          #f
          (begin
            (ada-e (arm-lsr-imm d-x13 d-result 32))
            (ada-e (arm-fmov-to-s 16 d-x13))
            (ada-e (arm-lsr-imm d-x14 y 32))
            (ada-e (arm-fmov-to-s 17 d-x14))
            (if (>= test 0)
                (begin (ada-e (arm-single (arm-fcmp 16 17))) (adr-flag test))
                (begin
                  (ada-e (arm-single (adr-float-op what)))
                  (ada-e (arm-fmov-from-s d-x13 16))
                  (ada-e (arm-lsl-imm d-x13 d-x13 32))
                  (ada-e (arm-add-imm d-result d-x13 (modulo d-f32-0 256)))))
            #t)))))

;; An `f64` operation `what` on raw `RESULT` and `y`, into `RESULT`: raw,
;; or a comparison's boolean. By way of `d16` and `d17`.
(define adr-f64-fast (subr da-assembles (string int) unit)
  (lambda (what y)
    (let ((test (adr-float-test what)))
      (begin
        (ada-e (arm-fmov-to-d 16 d-result))
        (ada-e (arm-fmov-to-d 17 y))
        (if (>= test 0)
            (begin (ada-e (arm-fcmp 16 17)) (adr-flag test))
            (begin
              (ada-e (adr-float-op what))
              (ada-e (arm-fmov-from-d d-result 16))))))))

;;; ------------------------------------------------------------ integers

;; The condition an `i64` (signed) or `u64` comparison `what` holds on; -1
;; for none.
(define adr-compare (subr pure (bool string) int)
  (lambda (signed what)
    (case what
      (("<") (if signed ada-c-lt ada-c-lo))
      (("<=") (if signed ada-c-le ada-c-ls))
      ((">") (if signed ada-c-gt ada-c-hi))
      ((">=") (if signed ada-c-ge ada-c-hs))
      (("=") ada-c-eq)
      (else -1))))

;; An `i64` (signed) or `u64` operation `what` on raw `RESULT` and `y`
;; (raw, or a shift's count, a fixnum), into `RESULT`: raw, or a
;; comparison's boolean. Its arithmetic wraps. Uses X13 to X16.
(define adr-raw-fast (subr da-assembles (bool string int) unit)
  (lambda (signed what y)
    (let ((c (adr-compare signed what)) (x d-result)
          (nonzero (lambda () (begin (ada-e (arm-cmp-imm y 0))
                                     (ada-trap d-divided-by-zero ada-c-eq)))))
      (if (>= c 0)
          (begin (ada-e (arm-cmp x y)) (adr-flag c))
          (case what
            (("from") #u)
            (("+") (ada-e (arm-add d-result x y)))
            (("-") (ada-e (arm-sub d-result x y)))
            (("*") (ada-e (arm-mul d-result x y)))
            (("-and") (ada-e (arm-and d-result x y)))
            (("-or") (ada-e (arm-orr d-result x y)))
            (("-xor") (ada-e (arm-eor d-result x y)))
            (("-not")
             (begin (ada-e (arm-sub d-result d-xzr x))
                    (ada-e (arm-sub-imm d-result d-result 1))))
            (("-quotient")
             (begin (nonzero)
                    (ada-e (if signed (arm-sdiv d-result x y) (arm-udiv d-result x y)))))
            (("-remainder")
             (begin (nonzero)
                    (ada-e (if signed (arm-sdiv d-x13 x y) (arm-udiv d-x13 x y)))
                    (ada-e (arm-msub d-result d-x13 y x))))
            (("-shl" "-shr")
             (begin
               (ada-e (arm-ubfx d-x13 y 3 6))
               (ada-e (cond ((string=? what "-shl") (arm-lslv d-result x d-x13))
                            (signed (arm-asrv d-result x d-x13))
                            (else (arm-lsrv d-result x d-x13))))))
            (else (ada-fail "a 64-bit operation")))))))

;; `RESULT`, the fixnum of an integer, wrapped to the range of a type of
;; `bits` bits: its bits 3 to `bits` + 2 kept, sign-extended if signed.
(define adr-wrap-small (subr da-assembles (bool int) unit)
  (lambda (signed bits)
    (if signed
        (begin
          (ada-e (arm-lsl-imm d-result d-result (- 61 bits)))
          (ada-e (arm-asr-imm d-result d-result (- 61 bits))))
        (ada-e (arm-and-bits d-result d-result 3 bits)))))

;; The slow path of an `int` operation (`IntSlow::emit`): a sum written
;; over its operand undone, the runtime's, and back.
(define adr-int-slow (subr da-assembles (dr-int-slow) unit)
  (lambda (s)
    (let ((overflow (extract s 2)) (x (extract s 4)) (y (extract s 5)) (imm (extract s 6))
          (into (extract s 7)) (sub (extract s 9)) (branch (extract s 10)))
      (begin
        (if (< overflow 0)
            #u
            (begin
              (ada-bind overflow)
              (if (= into x)
                  (ada-e (if (< y 0)
                             (if sub (arm-add-imm x into imm) (arm-sub-imm x into imm))
                             (if sub (arm-add x into y) (arm-sub x into y))))
                  #u)))
        (ada-bind (extract s 1))
        (let ((y2 (if (< y 0) (begin (ada-e (arm-movz d-x16 imm 0)) d-x16) y)))
          (ada-pure-call (ada-co d-co-pure (extract s 8) 2) (ada-args2 x y2) into))
        (ada-trap-set)
        (if (< branch 0)
            #u
            (begin
              (ada-imm d-x16 d-true)
              (ada-e (arm-cmp d-result d-x16))
              (ada-bc (if (extract s 11) ada-c-eq ada-c-ne) branch)))
        (ada-b (extract s 3))))))
)))
