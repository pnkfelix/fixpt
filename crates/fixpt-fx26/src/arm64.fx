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

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define arm64-module (module
;; What the encoders do: read the encoders, and count down.
(define-effect encodes (maxeff (read @globals) spin))
;; The encoders of two, three and four operands.
(define-type arm-op2 (subr encodes (int int) int))
(define-type arm-op3 (subr encodes (int int int) int))
(define-type arm-op4 (subr encodes (int int int int) int))

;; `acc` times 2 to the `n`.
(define arm-times-pow2 (subr encodes (int int) int)
  (lambda (n acc) (if (= n 0) acc (arm-times-pow2 (- n 1) (* 2 acc)))))
(define arm-pow2 (subr encodes (int) int)
  (lambda (n) (arm-times-pow2 n 1)))

;; `v` as a `bits`-bit two's-complement field, or -1 if it does not fit.
(define arm-simm (subr encodes (int int) int)
  (lambda (v bits)
    (let ((half (arm-pow2 (- bits 1))))
      (if (or (< v (- 0 half)) (>= v half)) -1 (modulo v (* 2 half))))))

;; Fields at their places: each is -1 if it did not fit, and so the sum.
(define arm-f (subr encodes (int int) int)
  (lambda (v shift) (if (< v 0) -1 (* v (arm-pow2 shift)))))
(define arm-sum (subr pure (int int) int)
  (lambda (a b) (if (or (< a 0) (< b 0)) -1 (+ a b))))
(define arm-sum3 (subr (read @globals) (int int int) int)
  (lambda (a b c) (arm-sum a (arm-sum b c))))
(define arm-sum4 (subr (read @globals) (int int int int) int)
  (lambda (a b c d) (arm-sum a (arm-sum3 b c d))))
(define arm-reg (subr pure (int) int)
  (lambda (x) (if (and (>= x 0) (<= x 31)) x -1)))
;; `v` if `ok`, else -1.
(define arm-check (subr pure (bool int) int)
  (lambda (ok v) (if ok v -1)))
;; Whether lo ≤ v < hi.
(define arm-in? (subr pure (int int int) bool)
  (lambda (v lo hi) (and (>= v lo) (< v hi))))
;; Register `x` at `shift`, and `v` as a `bits`-bit signed field at `shift`.
(define arm-reg-at (subr encodes (int int) int)
  (lambda (x shift) (arm-f (arm-reg x) shift)))
(define arm-simm-at (subr encodes (int int int) int)
  (lambda (v bits shift) (arm-f (arm-simm v bits) shift)))
;; op | field | n << 5 | t: an instruction on registers `n` and `t` (or
;; `d`), `field` its other operands at their places.
(define arm-n-t (subr encodes (int int int int) int)
  (lambda (op field n t) (arm-sum4 op field (arm-reg-at n 5) (arm-reg t))))

;;; ------------------------------------------------------ loads, stores

;; op | simm9 << 12 | n << 5 | t: the unscaled and indexed forms.
(define arm-mem9 (subr encodes (int int int int) int)
  (lambda (op t n imm) (arm-n-t op (arm-simm-at imm 9 12) n t)))
(define arm-ldr-post arm-op3 (lambda (t n imm) (arm-mem9 #xF8400400 t n imm)))
(define arm-ldr-pre arm-op3 (lambda (t n imm) (arm-mem9 #xF8400C00 t n imm)))
(define arm-str-post arm-op3 (lambda (t n imm) (arm-mem9 #xF8000400 t n imm)))
(define arm-str-pre arm-op3 (lambda (t n imm) (arm-mem9 #xF8000C00 t n imm)))
(define arm-ldur arm-op3 (lambda (t n imm) (arm-mem9 #xF8400000 t n imm)))
(define arm-stur arm-op3 (lambda (t n imm) (arm-mem9 #xF8000000 t n imm)))

;; `ldr`/`str xt, [xn, #off]`, `off` a multiple of 8 below 32768.
(define arm-mem12 (subr encodes (int int int int) int)
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
(define arm-pair (subr encodes (int int int int int) int)
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
(define arm-imm12 (subr encodes (int int int int) int)
  (lambda (op d n imm)
    (arm-check (arm-in? imm 0 4096) (arm-n-t op (arm-f imm 10) n d))))
(define arm-add-imm arm-op3 (lambda (d n imm) (arm-imm12 #x91000000 d n imm)))
(define arm-sub-imm arm-op3 (lambda (d n imm) (arm-imm12 #xD1000000 d n imm)))
(define arm-subs-imm arm-op3 (lambda (d n imm) (arm-imm12 #xF1000000 d n imm)))
(define arm-cmp-imm arm-op2 (lambda (n imm) (arm-imm12 #xF1000000 31 n imm)))

;; op | m << 16 | n << 5 | d.
(define arm-reg3 (subr encodes (int int int int) int)
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
(define arm-low-mask (subr encodes (int) int)
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
(define arm-shift-imm (subr encodes (int int int int) int)
  (lambda (op d n s) (arm-check (arm-in? s 0 64) (arm-n-t op (arm-f s 16) n d))))
(define arm-asr-imm arm-op3 (lambda (d n s) (arm-shift-imm #x9340FC00 d n s)))
(define arm-lsr-imm arm-op3 (lambda (d n s) (arm-shift-imm #xD340FC00 d n s)))
;; `strb wt, [xn]`.
(define arm-strb arm-op2 (lambda (t n) (arm-sum3 #x39000000 (arm-reg-at n 5) (arm-reg t))))
(define arm-csel arm-op4
  (lambda (d n m c) (arm-n-t #x9A800000 (arm-sum (arm-reg-at m 16) (arm-f c 12)) n d)))

;; `movz`/`movk xd, #imm16, lsl #(16 hw)`.
(define arm-mov16 (subr encodes (int int int int) int)
  (lambda (op d imm16 hw)
    (arm-check (and (>= imm16 0) (< imm16 65536) (>= hw 0) (< hw 4))
               (arm-sum4 op (arm-f hw 21) (arm-f imm16 5) (arm-reg d)))))
(define arm-movz arm-op3 (lambda (d imm16 hw) (arm-mov16 #xD2800000 d imm16 hw)))
(define arm-movk arm-op3 (lambda (d imm16 hw) (arm-mov16 #xF2800000 d imm16 hw)))
;; Any non-negative 64-bit constant below 2^60 (a fixnum's range): `movz`,
;; then a `movk` for each other nonzero 16 bits, low to high.
(define-type arm-code (listof int @k))
(define arm-mov-imm64 (subr (maxeff (read @globals) (alloc @k) spin) (int int) arm-code)
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

(define arm-b (subr encodes (int) int) (lambda (words) (arm-sum #x14000000 (arm-simm words 26))))
(define arm-bl (subr encodes (int) int) (lambda (words) (arm-sum #x94000000 (arm-simm words 26))))
(define arm-b-cond arm-op2
  (lambda (c words) (arm-sum3 #x54000000 (arm-simm-at words 19 5) c)))
(define arm-cbz arm-op2
  (lambda (t words) (arm-sum3 #xB4000000 (arm-simm-at words 19 5) (arm-reg t))))
(define arm-cbnz arm-op2
  (lambda (t words) (arm-sum3 #xB5000000 (arm-simm-at words 19 5) (arm-reg t))))
(define arm-br (subr encodes (int) int) (lambda (n) (arm-sum #xD61F0000 (arm-reg-at n 5))))
(define arm-blr (subr encodes (int) int) (lambda (n) (arm-sum #xD63F0000 (arm-reg-at n 5))))
(define arm-ret int #xD65F03C0)))

(define arm-ldr-post (with arm64-module arm-ldr-post))
(define arm-ldr-pre (with arm64-module arm-ldr-pre))
(define arm-str-post (with arm64-module arm-str-post))
(define arm-str-pre (with arm64-module arm-str-pre))
(define arm-ldur (with arm64-module arm-ldur))
(define arm-stur (with arm64-module arm-stur))
(define arm-ldr (with arm64-module arm-ldr))
(define arm-str (with arm64-module arm-str))
(define arm-ldr-lit (with arm64-module arm-ldr-lit))
(define arm-ldr-reg (with arm64-module arm-ldr-reg))
(define arm-stp-pre (with arm64-module arm-stp-pre))
(define arm-ldp-post (with arm64-module arm-ldp-post))
(define arm-stp (with arm64-module arm-stp))
(define arm-ldp (with arm64-module arm-ldp))
(define arm-add-imm (with arm64-module arm-add-imm))
(define arm-sub-imm (with arm64-module arm-sub-imm))
(define arm-subs-imm (with arm64-module arm-subs-imm))
(define arm-cmp-imm (with arm64-module arm-cmp-imm))
(define arm-add (with arm64-module arm-add))
(define arm-sub (with arm64-module arm-sub))
(define arm-adds (with arm64-module arm-adds))
(define arm-subs (with arm64-module arm-subs))
(define arm-orr (with arm64-module arm-orr))
(define arm-cmp (with arm64-module arm-cmp))
(define arm-mov (with arm64-module arm-mov))
(define arm-and-low (with arm64-module arm-and-low))
(define arm-tst-low (with arm64-module arm-tst-low))
(define arm-ubfx (with arm64-module arm-ubfx))
(define arm-asr-imm (with arm64-module arm-asr-imm))
(define arm-lsr-imm (with arm64-module arm-lsr-imm))
(define arm-strb (with arm64-module arm-strb))
(define arm-csel (with arm64-module arm-csel))
(define arm-movz (with arm64-module arm-movz))
(define arm-movk (with arm64-module arm-movk))
(define arm-mov-imm64 (with arm64-module arm-mov-imm64))
(define arm-b (with arm64-module arm-b))
(define arm-bl (with arm64-module arm-bl))
(define arm-b-cond (with arm64-module arm-b-cond))
(define arm-cbz (with arm64-module arm-cbz))
(define arm-cbnz (with arm64-module arm-cbnz))
(define arm-br (with arm64-module arm-br))
(define arm-blr (with arm64-module arm-blr))
(define arm-ret (with arm64-module arm-ret))
