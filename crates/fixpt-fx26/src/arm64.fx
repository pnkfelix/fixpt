;;; An arm64 encoder, in FX-26 (PLAN.md §11, step 11b): the instructions the
;;; native machine uses, each a function to its 32-bit word, exactly as
;;; `fixpt-native/src/arm64.rs` encodes them. That encoder is this one's
;;; oracle (`tests/arm64.rs` in this crate), as the system assembler is
;;; that one's.
;;;
;;; FX-26 has no bitwise operations and needs none here: an instruction is
;;; fields that do not overlap, so shifting is multiplying by a power of
;;; two and combining is adding. A signed field is masked by `modulo`,
;;; which is never negative for a positive divisor. What does not fit gives
;;; -1, which no instruction is: the encoders are pure, and whoever places
;;; the code checks.

;; Registers are 0–30; 31 is sp or xzr, as the instruction takes it.
;; Conditions: eq 0, ne 1, hs 2, lo 3, vs 6, vc 7, hi 8, ls 9, ge 10,
;; lt 11, gt 12, le 13.

;; A file of one expression (`load-input`, `TODO.md` §68): the module, of no
;; state and given nothing, which the conductor gives `native.fx`. Its types
;; (`arm64-types.fx`) are loaded around it, so that they are not among its
;; values; the module names what it uses of them.
(let ((arm64-types (load-module "fx26:arm64-types.fx")))
  (module
(hide (include arm64-types))

;; 2 to the `n`, `n` ≥ 0: a shift (in line natively), not `n` doublings.
(define arm-pow2 (->* (int) int)
  (lambda (n) (arithmetic-shift 1 n)))

;; `v` as a `bits`-bit two's-complement field, or -1 if it does not fit.
(define arm-simm (->* (int int) int)
  (lambda (v bits)
    (let ((half (arm-pow2 (- bits 1))))
      (if (or (< v (- 0 half)) (>= v half)) -1 (modulo v (* 2 half))))))

;; Fields at their places: each is -1 if it did not fit, and so the sum.
(define arm-f (->* (int int) int)
  (lambda (v shift) (if (< v 0) -1 (arithmetic-shift v shift))))
(define arm-sum (->* (int int) int)
  (lambda (a b) (if (or (< a 0) (< b 0)) -1 (+ a b))))
(define arm-sum3 (->* (int int int) int)
  (lambda (a b c) (arm-sum a (arm-sum b c))))
(define arm-sum4 (->* (int int int int) int)
  (lambda (a b c d) (arm-sum a (arm-sum3 b c d))))
(define arm-reg (->* (int) int)
  (lambda (x) (if (and (>= x 0) (<= x 31)) x -1)))
;; `v` if `ok`, else -1.
(define arm-check (->* (bool int) int)
  (lambda (ok v) (if ok v -1)))
;; Whether lo ≤ v < hi.
(define arm-in? (->* (int int int) bool)
  (lambda (v lo hi) (and (>= v lo) (< v hi))))
;; Register `x` at `shift`, and `v` as a `bits`-bit signed field at `shift`.
(define arm-reg-at (->* (int int) int)
  (lambda (x shift) (arm-f (arm-reg x) shift)))
(define arm-simm-at (->* (int int int) int)
  (lambda (v bits shift) (arm-f (arm-simm v bits) shift)))
;; op | field | n << 5 | t: an instruction on registers `n` and `t` (or
;; `d`), `field` its other operands at their places.
(define arm-n-t (->* (int int int int) int)
  (lambda (op field n t) (arm-sum4 op field (arm-reg-at n 5) (arm-reg t))))

;;; ------------------------------------------------------ loads, stores

;; op | simm9 << 12 | n << 5 | t: the unscaled and indexed forms.
(define arm-mem9 (->* (int int int int) int)
  (lambda (op t n imm) (arm-n-t op (arm-simm-at imm 9 12) n t)))
(define arm-ldr-post arm-op3 (lambda (t n imm) (arm-mem9 #xF8400400 t n imm)))
(define arm-ldr-pre arm-op3 (lambda (t n imm) (arm-mem9 #xF8400C00 t n imm)))
(define arm-str-post arm-op3 (lambda (t n imm) (arm-mem9 #xF8000400 t n imm)))
(define arm-str-pre arm-op3 (lambda (t n imm) (arm-mem9 #xF8000C00 t n imm)))
(define arm-ldur arm-op3 (lambda (t n imm) (arm-mem9 #xF8400000 t n imm)))
(define arm-stur arm-op3 (lambda (t n imm) (arm-mem9 #xF8000000 t n imm)))

;; `ldr`/`str xt, [xn, #off]`, `off` a multiple of 8 below 32768.
(define arm-mem12 (->* (int int int int) int)
  (lambda (op t n off)
    (arm-check (and (= (modulo off 8) 0) (>= off 0) (< off 32768))
               (arm-n-t op (arm-f (quotient off 8) 10) n t))))
(define arm-ldr arm-op3 (lambda (t n off) (arm-mem12 #xF9400000 t n off)))
(define arm-str arm-op3 (lambda (t n off) (arm-mem12 #xF9000000 t n off)))

(define arm-ldr-lit arm-op2
  (lambda (t words) (arm-sum3 #x58000000 (arm-simm-at words 19 5) (arm-reg t))))
(define arm-ldr-reg arm-op3
  (lambda (t n m) (arm-n-t #xF8606800 (arm-reg-at m 16) n t)))

;; The pairs: op | simm7(imm / 8) << 15 | t2 << 10 | n << 5 | t.
(define arm-pair (->* (int int int int int) int)
  (lambda (op t t2 n imm)
    (let ((offset (arm-simm-at (quotient imm 8) 7 15)))
      (arm-check (= (modulo imm 8) 0)
                 (arm-n-t op (arm-sum offset (arm-reg-at t2 10)) n t)))))
(define arm-stp-pre arm-op4 (lambda (t t2 n imm) (arm-pair #xA9800000 t t2 n imm)))
(define arm-ldp-post arm-op4 (lambda (t t2 n imm) (arm-pair #xA8C00000 t t2 n imm)))
(define arm-stp arm-op4 (lambda (t t2 n imm) (arm-pair #xA9000000 t t2 n imm)))
(define arm-ldp arm-op4 (lambda (t t2 n imm) (arm-pair #xA9400000 t t2 n imm)))

;;; ------------------------------------------------------ arithmetic

;; op | imm12 << 10 | n << 5 | d.
(define arm-imm12 (->* (int int int int) int)
  (lambda (op d n imm)
    (arm-check (arm-in? imm 0 4096) (arm-n-t op (arm-f imm 10) n d))))
(define arm-add-imm arm-op3 (lambda (d n imm) (arm-imm12 #x91000000 d n imm)))
(define arm-sub-imm arm-op3 (lambda (d n imm) (arm-imm12 #xD1000000 d n imm)))
(define arm-subs-imm arm-op3 (lambda (d n imm) (arm-imm12 #xF1000000 d n imm)))
(define arm-cmp-imm arm-op2 (lambda (n imm) (arm-imm12 #xF1000000 31 n imm)))

;; op | m << 16 | n << 5 | d.
(define arm-reg3 (->* (int int int int) int)
  (lambda (op d n m) (arm-n-t op (arm-reg-at m 16) n d)))
(define arm-add arm-op3 (lambda (d n m) (arm-reg3 #x8B000000 d n m)))
(define arm-sub arm-op3 (lambda (d n m) (arm-reg3 #xCB000000 d n m)))
(define arm-adds arm-op3 (lambda (d n m) (arm-reg3 #xAB000000 d n m)))
(define arm-subs arm-op3 (lambda (d n m) (arm-reg3 #xEB000000 d n m)))
(define arm-orr arm-op3 (lambda (d n m) (arm-reg3 #xAA000000 d n m)))
(define arm-cmp arm-op2 (lambda (n m) (arm-reg3 #xEB000000 31 n m)))
(define arm-mov arm-op2 (lambda (d m) (arm-reg3 #xAA000000 d 31 m)))

;; The low `bits` bits: 1 ≤ bits < 64. The mask's field is its width less
;; one at 10.
(define arm-low-mask (->* (int) int)
  (lambda (bits) (arm-check (arm-in? bits 1 64) (arm-f (- bits 1) 10))))
(define arm-and-low arm-op3
  (lambda (d n bits) (arm-n-t #x92400000 (arm-low-mask bits) n d)))
(define arm-tst-low arm-op2
  (lambda (n bits) (arm-sum3 #xF240001F (arm-low-mask bits) (arm-reg-at n 5))))
(define arm-ubfx arm-op4
  (lambda (d n lsb width)
    (let ((immr (arm-f lsb 16))
          (imms (arm-f (- (+ lsb width) 1) 10)))
      (arm-check (and (< lsb 64) (>= width 1) (<= (+ lsb width) 64))
                 (arm-n-t #xD3400000 (arm-sum immr imms) n d)))))
;; A shift by `s`, 0 ≤ s < 64.
(define arm-shift-imm (->* (int int int int) int)
  (lambda (op d n s) (arm-check (arm-in? s 0 64) (arm-n-t op (arm-f s 16) n d))))
(define arm-asr-imm arm-op3 (lambda (d n s) (arm-shift-imm #x9340FC00 d n s)))
(define arm-lsr-imm arm-op3 (lambda (d n s) (arm-shift-imm #xD340FC00 d n s)))
;; `strb wt, [xn]`.
(define arm-strb arm-op2 (lambda (t n) (arm-sum3 #x39000000 (arm-reg-at n 5) (arm-reg t))))
(define arm-csel arm-op4
  (lambda (d n m c) (arm-n-t #x9A800000 (arm-sum (arm-reg-at m 16) (arm-f c 12)) n d)))

;; `movz`/`movk xd, #imm16, lsl #(16 hw)`.
(define arm-mov16 (->* (int int int int) int)
  (lambda (op d imm16 hw)
    (arm-check (and (>= imm16 0) (< imm16 65536) (>= hw 0) (< hw 4))
               (arm-sum4 op (arm-f hw 21) (arm-f imm16 5) (arm-reg d)))))
(define arm-movz arm-op3 (lambda (d imm16 hw) (arm-mov16 #xD2800000 d imm16 hw)))
(define arm-movk arm-op3 (lambda (d imm16 hw) (arm-mov16 #xF2800000 d imm16 hw)))
;; Any non-negative 64-bit constant below 2^60 (a fixnum's range): `movz`,
;; then a `movk` for each other nonzero 16 bits, low to high.
(define arm-mov-imm64 (->* (int int) arm-code)
  (lambda (d v)
    (letrec ((ks (subr (maxeff (read @globals) (alloc @k) spin) (int int) arm-code)
                (lambda (hw rest)
                  (if (= hw 4)
                      nil
                      (let ((part (modulo (quotient rest 65536) 65536)))
                        (if (= part 0)
                            (ks (+ hw 1) (quotient rest 65536))
                            (cons (arm-movk d part hw) (ks (+ hw 1) (quotient rest 65536)))))))))
      (the arm-code (cons (arm-movz d (modulo v 65536) 0) (ks 1 v))))))

;;; ------------------------------------------------------ control

(define arm-b (->* (int) int) (lambda (words) (arm-sum #x14000000 (arm-simm words 26))))
(define arm-bl (->* (int) int) (lambda (words) (arm-sum #x94000000 (arm-simm words 26))))
(define arm-b-cond arm-op2
  (lambda (c words) (arm-sum3 #x54000000 (arm-simm-at words 19 5) c)))
(define arm-cbz arm-op2
  (lambda (t words) (arm-sum3 #xB4000000 (arm-simm-at words 19 5) (arm-reg t))))
(define arm-cbnz arm-op2
  (lambda (t words) (arm-sum3 #xB5000000 (arm-simm-at words 19 5) (arm-reg t))))
(define arm-br (->* (int) int) (lambda (n) (arm-sum #xD61F0000 (arm-reg-at n 5))))
(define arm-blr (->* (int) int) (lambda (n) (arm-sum #xD63F0000 (arm-reg-at n 5))))
(define arm-ret int #xD65F03C0)

;;; ------------------------------------------------------ the native convention's
;;; What the native convention's compiler (`native-direct-arm64*.fx`, the
;;; Rust `direct.rs`) uses besides: narrow and indexed memory, wide
;;; immediates, division, shifts by a register, and floating point.

;; The unscaled loads and stores of 32, 16 and 8 bits.
(define arm-ldur-w arm-op3 (lambda (t n imm) (arm-mem9 #xB8400000 t n imm)))
(define arm-ldurh arm-op3 (lambda (t n imm) (arm-mem9 #x78400000 t n imm)))
(define arm-ldurb arm-op3 (lambda (t n imm) (arm-mem9 #x38400000 t n imm)))
(define arm-sturh arm-op3 (lambda (t n imm) (arm-mem9 #x78000000 t n imm)))
(define arm-sturb arm-op3 (lambda (t n imm) (arm-mem9 #x38000000 t n imm)))
(define arm-stur-w arm-op3 (lambda (t n imm) (arm-mem9 #xB8000000 t n imm)))
;; Indexed by `m`, scaled by the width.
(define arm-ldr-x8 arm-op3 (lambda (t n m) (arm-n-t #xF8607800 (arm-reg-at m 16) n t)))
(define arm-ldr-w4 arm-op3 (lambda (t n m) (arm-n-t #xB8607800 (arm-reg-at m 16) n t)))
(define arm-ldrsw-4 arm-op3 (lambda (t n m) (arm-n-t #xB8A07800 (arm-reg-at m 16) n t)))
(define arm-str-x8 arm-op3 (lambda (t n m) (arm-n-t #xF8207800 (arm-reg-at m 16) n t)))
(define arm-str-w4 arm-op3 (lambda (t n m) (arm-n-t #xB8207800 (arm-reg-at m 16) n t)))

;; By 4 KB pages; `adds`.
(define arm-add-imm-pages arm-op3 (lambda (d n imm) (arm-imm12 #x91400000 d n imm)))
(define arm-sub-imm-pages arm-op3 (lambda (d n imm) (arm-imm12 #xD1400000 d n imm)))
(define arm-adds-imm arm-op3 (lambda (d n imm) (arm-imm12 #xB1000000 d n imm)))
;; `add xd, xn, xm, lsl #s`.
(define arm-add-lsl arm-op4
  (lambda (d n m s)
    (arm-check (arm-in? s 0 64) (arm-n-t #x8B000000 (arm-sum (arm-reg-at m 16) (arm-f s 10)) n d))))
;; `cmp sp, xm`.
(define arm-cmp-sp (->* (int) int) (lambda (m) (arm-sum #xEB2063FF (arm-reg-at m 16))))
(define arm-eor arm-op3 (lambda (d n m) (arm-reg3 #xCA000000 d n m)))
(define arm-and arm-op3 (lambda (d n m) (arm-reg3 #x8A000000 d n m)))
(define arm-sdiv arm-op3 (lambda (d n m) (arm-reg3 #x9AC00C00 d n m)))
(define arm-udiv arm-op3 (lambda (d n m) (arm-reg3 #x9AC00800 d n m)))
(define arm-mul arm-op3 (lambda (d n m) (arm-reg3 #x9B007C00 d n m)))
(define arm-smulh arm-op3 (lambda (d n m) (arm-reg3 #x9B407C00 d n m)))
(define arm-lslv arm-op3 (lambda (d n m) (arm-reg3 #x9AC02000 d n m)))
(define arm-lsrv arm-op3 (lambda (d n m) (arm-reg3 #x9AC02400 d n m)))
(define arm-asrv arm-op3 (lambda (d n m) (arm-reg3 #x9AC02800 d n m)))
(define arm-msub arm-op4
  (lambda (d n m a) (arm-n-t #x9B008000 (arm-sum (arm-reg-at m 16) (arm-reg-at a 10)) n d)))
;; `and xd, xn, #mask` of `width` ones from `lsb`, `width` < 64.
(define arm-and-bits arm-op4
  (lambda (d n lsb width)
    (arm-check (and (>= lsb 0) (>= width 1) (<= (+ lsb width) 64) (< width 64))
               (arm-n-t #x92400000
                        (arm-sum (arm-f (modulo (- 64 lsb) 64) 16) (arm-f (- width 1) 10)) n d))))
(define arm-lsl-imm arm-op3
  (lambda (d n s)
    (arm-check (arm-in? s 0 64)
               (arm-n-t #xD3400000 (arm-sum (arm-f (modulo (- 64 s) 64) 16) (arm-f (- 63 s) 10))
                        n d))))
;; `adr xd, words` (as instructions), in reach of 21 bits of bytes.
(define arm-adr arm-op2
  (lambda (d words)
    (let ((bytes (arm-simm (* 4 words) 21)))
      (if (< bytes 0)
          -1
          (arm-sum3 (+ #x10000000 (arithmetic-shift (modulo bytes 4) 29))
                    (arm-f (quotient bytes 4) 5) (arm-reg d))))))
(define arm-nop int #xD503201F)

;; The card of the word at `obj + off` marked (`arm64::card_mark`): `off`
;; in reach of one `add` or `sub`.
(define arm-card-mark
  (subr (maxeff (alloc @k) (read @globals) spin) (int int int int int int) arm-code)
  (lambda (obj off state cards t1 t2)
    ;; cons-chain: in `@k`, the caller's region, which `list` would not be
    (cons (if (< off 0) (arm-sub-imm t1 obj (- 0 off)) (arm-add-imm t1 obj off))
          (cons (arm-lsr-imm t1 t1 9)
                (cons (arm-ldr t2 state cards)
                      (cons (arm-add t2 t2 t1)
                            (cons (arm-movz t1 1 0) (cons (arm-strb t1 t2) nil))))))))

;; Floating point: `d` registers numbered as `x` ones, each a double.
(define arm-fmov-to-d arm-op2 (lambda (d n) (arm-n-t #x9E670000 0 n d)))
(define arm-fmov-from-d arm-op2 (lambda (d n) (arm-n-t #x9E660000 0 n d)))
(define arm-fp2 (->* (int int int int) int)
  (lambda (op d n m) (arm-n-t (+ #x1E600800 (arithmetic-shift op 12)) (arm-reg-at m 16) n d)))
(define arm-fadd arm-op3 (lambda (d n m) (arm-fp2 2 d n m)))
(define arm-fsub arm-op3 (lambda (d n m) (arm-fp2 3 d n m)))
(define arm-fmul arm-op3 (lambda (d n m) (arm-fp2 0 d n m)))
(define arm-fdiv arm-op3 (lambda (d n m) (arm-fp2 1 d n m)))
(define arm-fp1 (->* (int int int) int)
  (lambda (op d n) (arm-n-t (+ #x1E604000 (arithmetic-shift op 15)) 0 n d)))
(define arm-fabs arm-op2 (lambda (d n) (arm-fp1 1 d n)))
(define arm-fneg arm-op2 (lambda (d n) (arm-fp1 2 d n)))
(define arm-fsqrt arm-op2 (lambda (d n) (arm-fp1 3 d n)))
(define arm-frintn arm-op2 (lambda (d n) (arm-fp1 8 d n)))
(define arm-frintp arm-op2 (lambda (d n) (arm-fp1 9 d n)))
(define arm-frintm arm-op2 (lambda (d n) (arm-fp1 10 d n)))
(define arm-frintz arm-op2 (lambda (d n) (arm-fp1 11 d n)))
(define arm-fcmp arm-op2 (lambda (n m) (arm-sum3 #x1E602000 (arm-reg-at m 16) (arm-reg-at n 5))))
(define arm-scvtf arm-op2 (lambda (d n) (arm-n-t #x9E620000 0 n d)))
(define arm-fcvtzs arm-op2 (lambda (d n) (arm-n-t #x9E780000 0 n d)))
;; A double's instruction as a single's: its type bit cleared.
(define arm-single (->* (int) int)
  (lambda (w) (if (< w 0) -1 (if (= (bitwise-and w #x400000) 0) w (- w #x400000)))))
(define arm-fmov-to-s arm-op2 (lambda (d n) (arm-n-t #x1E270000 0 n d)))
(define arm-fmov-from-s arm-op2 (lambda (d n) (arm-n-t #x1E260000 0 n d)))))
