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

(define arm-pow2 (subr pure (int) int)
  (lambda (n) (if (= n 0) 1 (* 2 (arm-pow2 (- n 1))))))

;; `v` as a `bits`-bit two's-complement field, or -1 if it does not fit.
(define arm-simm (subr pure (int int) int)
  (lambda (v bits)
    (let ((half (arm-pow2 (- bits 1))))
      (if (or (< v (- 0 half)) (>= v half)) -1 (modulo v (* 2 half))))))

;; Fields at their places: each is -1 if it did not fit, and so the sum.
(define arm-f (subr pure (int int) int)
  (lambda (v shift) (if (< v 0) -1 (* v (arm-pow2 shift)))))
(define arm-sum (subr pure (int int) int)
  (lambda (a b) (if (or (< a 0) (< b 0)) -1 (+ a b))))
(define arm-sum3 (subr pure (int int int) int)
  (lambda (a b c) (arm-sum a (arm-sum b c))))
(define arm-sum4 (subr pure (int int int int) int)
  (lambda (a b c d) (arm-sum a (arm-sum3 b c d))))
(define arm-sum5 (subr pure (int int int int int) int)
  (lambda (a b c d e) (arm-sum a (arm-sum4 b c d e))))
(define arm-reg (subr pure (int) int)
  (lambda (x) (if (and (>= x 0) (<= x 31)) x -1)))
;; `v` if `ok`, else -1.
(define arm-check (subr pure (bool int) int)
  (lambda (ok v) (if ok v -1)))

;;; ------------------------------------------------------ loads, stores

;; op | simm9 << 12 | n << 5 | t: the unscaled and indexed forms.
(define arm-mem9 (subr pure (int int int int) int)
  (lambda (op t n imm) (arm-sum4 op (arm-f (arm-simm imm 9) 12) (arm-f (arm-reg n) 5) (arm-reg t))))
(define arm-ldr-post (subr pure (int int int) int) (lambda (t n imm) (arm-mem9 #xF8400400 t n imm)))
(define arm-ldr-pre (subr pure (int int int) int) (lambda (t n imm) (arm-mem9 #xF8400C00 t n imm)))
(define arm-str-post (subr pure (int int int) int) (lambda (t n imm) (arm-mem9 #xF8000400 t n imm)))
(define arm-str-pre (subr pure (int int int) int) (lambda (t n imm) (arm-mem9 #xF8000C00 t n imm)))
(define arm-ldur (subr pure (int int int) int) (lambda (t n imm) (arm-mem9 #xF8400000 t n imm)))
(define arm-stur (subr pure (int int int) int) (lambda (t n imm) (arm-mem9 #xF8000000 t n imm)))

;; `ldr`/`str xt, [xn, #off]`, `off` a multiple of 8 below 32768.
(define arm-mem12 (subr pure (int int int int) int)
  (lambda (op t n off)
    (arm-check (and (= (modulo off 8) 0) (>= off 0) (< off 32768))
               (arm-sum4 op (arm-f (quotient off 8) 10) (arm-f (arm-reg n) 5) (arm-reg t)))))
(define arm-ldr (subr pure (int int int) int) (lambda (t n off) (arm-mem12 #xF9400000 t n off)))
(define arm-str (subr pure (int int int) int) (lambda (t n off) (arm-mem12 #xF9000000 t n off)))

(define arm-ldr-lit (subr pure (int int) int)
  (lambda (t words) (arm-sum3 #x58000000 (arm-f (arm-simm words 19) 5) (arm-reg t))))
(define arm-ldr-reg (subr pure (int int int) int)
  (lambda (t n m) (arm-sum4 #xF8606800 (arm-f (arm-reg m) 16) (arm-f (arm-reg n) 5) (arm-reg t))))

;; The pairs: op | simm7(imm / 8) << 15 | t2 << 10 | n << 5 | t.
(define arm-pair (subr pure (int int int int int) int)
  (lambda (op t t2 n imm)
    (arm-check (= (modulo imm 8) 0)
               (arm-sum5 op (arm-f (arm-simm (quotient imm 8) 7) 15) (arm-f (arm-reg t2) 10) (arm-f (arm-reg n) 5) (arm-reg t)))))
(define arm-stp-pre (subr pure (int int int int) int) (lambda (t t2 n imm) (arm-pair #xA9800000 t t2 n imm)))
(define arm-ldp-post (subr pure (int int int int) int) (lambda (t t2 n imm) (arm-pair #xA8C00000 t t2 n imm)))
(define arm-stp (subr pure (int int int int) int) (lambda (t t2 n imm) (arm-pair #xA9000000 t t2 n imm)))
(define arm-ldp (subr pure (int int int int) int) (lambda (t t2 n imm) (arm-pair #xA9400000 t t2 n imm)))

;;; ------------------------------------------------------ arithmetic

;; op | imm12 << 10 | n << 5 | d.
(define arm-imm12 (subr pure (int int int int) int)
  (lambda (op d n imm)
    (arm-check (and (>= imm 0) (< imm 4096)) (arm-sum4 op (arm-f imm 10) (arm-f (arm-reg n) 5) (arm-reg d)))))
(define arm-add-imm (subr pure (int int int) int) (lambda (d n imm) (arm-imm12 #x91000000 d n imm)))
(define arm-sub-imm (subr pure (int int int) int) (lambda (d n imm) (arm-imm12 #xD1000000 d n imm)))
(define arm-subs-imm (subr pure (int int int) int) (lambda (d n imm) (arm-imm12 #xF1000000 d n imm)))
(define arm-cmp-imm (subr pure (int int) int) (lambda (n imm) (arm-imm12 #xF1000000 31 n imm)))

;; op | m << 16 | n << 5 | d.
(define arm-reg3 (subr pure (int int int int) int)
  (lambda (op d n m) (arm-sum4 op (arm-f (arm-reg m) 16) (arm-f (arm-reg n) 5) (arm-reg d))))
(define arm-add (subr pure (int int int) int) (lambda (d n m) (arm-reg3 #x8B000000 d n m)))
(define arm-sub (subr pure (int int int) int) (lambda (d n m) (arm-reg3 #xCB000000 d n m)))
(define arm-adds (subr pure (int int int) int) (lambda (d n m) (arm-reg3 #xAB000000 d n m)))
(define arm-subs (subr pure (int int int) int) (lambda (d n m) (arm-reg3 #xEB000000 d n m)))
(define arm-orr (subr pure (int int int) int) (lambda (d n m) (arm-reg3 #xAA000000 d n m)))
(define arm-cmp (subr pure (int int) int) (lambda (n m) (arm-reg3 #xEB000000 31 n m)))
(define arm-mov (subr pure (int int) int) (lambda (d m) (arm-reg3 #xAA000000 d 31 m)))

;; The low `bits` bits: 1 ≤ bits < 64.
(define arm-and-low (subr pure (int int int) int)
  (lambda (d n bits)
    (arm-check (and (>= bits 1) (< bits 64)) (arm-sum4 #x92400000 (arm-f (- bits 1) 10) (arm-f (arm-reg n) 5) (arm-reg d)))))
(define arm-tst-low (subr pure (int int) int)
  (lambda (n bits) (arm-check (and (>= bits 1) (< bits 64)) (arm-sum3 #xF240001F (arm-f (- bits 1) 10) (arm-f (arm-reg n) 5)))))
(define arm-ubfx (subr pure (int int int int) int)
  (lambda (d n lsb width)
    (arm-check (and (< lsb 64) (>= width 1) (<= (+ lsb width) 64))
               (arm-sum5 #xD3400000 (arm-f lsb 16) (arm-f (- (+ lsb width) 1) 10) (arm-f (arm-reg n) 5) (arm-reg d)))))
(define arm-asr-imm (subr pure (int int int) int)
  (lambda (d n s) (arm-check (and (>= s 0) (< s 64)) (arm-sum4 #x9340FC00 (arm-f s 16) (arm-f (arm-reg n) 5) (arm-reg d)))))
(define arm-csel (subr pure (int int int int) int)
  (lambda (d n m c) (arm-sum5 #x9A800000 (arm-f (arm-reg m) 16) (arm-f c 12) (arm-f (arm-reg n) 5) (arm-reg d))))

;; `movz`/`movk xd, #imm16, lsl #(16 hw)`.
(define arm-mov16 (subr pure (int int int int) int)
  (lambda (op d imm16 hw)
    (arm-check (and (>= imm16 0) (< imm16 65536) (>= hw 0) (< hw 4))
               (arm-sum4 op (arm-f hw 21) (arm-f imm16 5) (arm-reg d)))))
(define arm-movz (subr pure (int int int) int) (lambda (d imm16 hw) (arm-mov16 #xD2800000 d imm16 hw)))
(define arm-movk (subr pure (int int int) int) (lambda (d imm16 hw) (arm-mov16 #xF2800000 d imm16 hw)))

;; Any non-negative 64-bit constant below 2^60 (a fixnum's range): `movz`,
;; then a `movk` for each other nonzero 16 bits, low to high.
(define-type arm-code (listof int @k))
(define arm-mov-imm64 (subr (alloc @k) (int int) arm-code)
  (lambda (d v)
    (letrec ((ks (subr (alloc @k) (int int) arm-code)
                (lambda (hw rest)
                  (if (= hw 4)
                      nil
                      (let ((part (modulo (quotient rest 65536) 65536)))
                        (if (= part 0)
                            (ks (+ hw 1) (quotient rest 65536))
                            (cons (arm-movk d part hw) (ks (+ hw 1) (quotient rest 65536)))))))))
      (the arm-code (cons (arm-movz d (modulo v 65536) 0) (ks 1 v))))))

;;; ------------------------------------------------------ control

(define arm-b (subr pure (int) int) (lambda (words) (arm-sum #x14000000 (arm-simm words 26))))
(define arm-bl (subr pure (int) int) (lambda (words) (arm-sum #x94000000 (arm-simm words 26))))
(define arm-b-cond (subr pure (int int) int)
  (lambda (c words) (arm-sum3 #x54000000 (arm-f (arm-simm words 19) 5) c)))
(define arm-cbz (subr pure (int int) int)
  (lambda (t words) (arm-sum3 #xB4000000 (arm-f (arm-simm words 19) 5) (arm-reg t))))
(define arm-cbnz (subr pure (int int) int)
  (lambda (t words) (arm-sum3 #xB5000000 (arm-f (arm-simm words 19) 5) (arm-reg t))))
(define arm-br (subr pure (int) int) (lambda (n) (arm-sum #xD61F0000 (arm-f (arm-reg n) 5))))
(define arm-blr (subr pure (int) int) (lambda (n) (arm-sum #xD63F0000 (arm-f (arm-reg n) 5))))
(define arm-ret int #xD65F03C0)
