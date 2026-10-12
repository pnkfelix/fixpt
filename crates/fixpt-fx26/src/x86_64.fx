;;; An x86_64 encoder, in FX-26: the instructions the x86_64 machine's
;;; compiled words use, each a function to its bytes, exactly as
;;; `fixpt-native/src/x86_64.rs` encodes them. That encoder is this one's
;;; oracle (`tests/x86_64.rs` in this crate), as the system assembler is
;;; that one's; `arm64.fx` is the same for arm64.
;;;
;;; As there, no bitwise operations: a byte of fields is their sum, each
;;; multiplied to its place, and a register's high bit, which goes in a
;;; REX prefix, is its quotient by 8. Every operation is on 64 bits unless
;;; its name says otherwise. A memory operand is a base, an index (-1 for
;;; none), a scale and a displacement.

;; Registers are 0–15 as the hardware numbers them: rax 0, rcx 1, rdx 2,
;; rbx 3, rsp 4, rbp 5, rsi 6, rdi 7, r8 to r15 8 to 15.
;; Conditions: o 0, no 1, b 2, ae 3, e 4, ne 5, be 6, a 7, s 8, ns 9,
;; l 12, ge 13, le 14, g 15.
;; Arithmetic, as `x86-alu` takes it: add 0, or 1, and 4, sub 5, xor 6,
;; cmp 7. Shifts: shl 4, shr 5, sar 7.

;; A file of one expression (`load-input`, `TODO.md` §68): the module, of no
;; state and given nothing, which the conductor gives `native-x64.fx`.
(let ((x86-64-types (load-module "fx26:x86_64-types.fx")))
  (module
(hide (include x86-64-types))

;; Bytes of one and two, as lists of the encoders' region.
(define x86-b1 (subr x86-encodes (int) x86-bytes) (lambda (a) (cons a nil)))
(define x86-b2 (subr x86-encodes (int int) x86-bytes)
  ;; cons-chain: in `@k`, the encoders' region, which `list` would not be
  (lambda (a b) (cons a (cons b nil))))

;; A register's high bit, for a REX prefix, and its low three, for the rest.
(define x86-hi (subr pure (int) int) (lambda (r) (quotient r 8)))
(define x86-lo (subr pure (int) int) (lambda (r) (modulo r 8)))

;; The `n` bytes of `v` modulo 256^n, lowest first.
(define x86-le (subr x86-encodes (int int) x86-bytes)
  (lambda (n v)
    (if (= n 0) nil (cons (modulo v 256) (x86-le (- n 1) (quotient (modulo v 4294967296) 256))))))
;; Eight of them: two halves of four, as `x86-le` keeps four at most.
(define x86-le8 (subr x86-encodes (int) x86-bytes)
  (lambda (v)
    (let ((u (modulo v 18446744073709551616)))
      (append (x86-le 4 (modulo u 4294967296)) (x86-le 4 (quotient u 4294967296))))))

;; Whether `v` fits a signed byte.
(define x86-i8? (subr pure (int) bool) (lambda (v) (and (>= v -128) (< v 128))))

;; A REX prefix: `w` 1 for 64 bits, and the high bits of ModRM's `reg`
;; field, the SIB index and ModRM's `rm` (or SIB base); none when nothing
;; needs one.
(define x86-rex (subr x86-encodes (int int int int) x86-bytes)
  (lambda (w r x b)
    (let ((v (+ (+ 64 (* 8 w)) (+ (* 4 (x86-hi r)) (+ (* 2 (x86-hi x)) (x86-hi b))))))
      (if (= v 64) nil (x86-b1 v)))))

;; A SIB byte's scale field: 1, 2, 4 or 8 as 0 to 3.
(define x86-scale-bits (subr pure (int) int)
  (lambda (scale) (cond ((= scale 8) 3) ((= scale 4) 2) ((= scale 2) 1) (else 0))))

;; ModRM, SIB and displacement for `[base + index * scale + disp]`, with
;; `field` in ModRM's `reg`. rbp and r13 as a base with no displacement
;; mean something else, so they take a zero byte of one; rsp and r12 as a
;; base need a SIB byte, as does an index.
(define x86-modrm-mem (subr x86-encodes (int int int int int) x86-bytes)
  (lambda (field base index scale disp)
    (let* ((b3 (x86-lo base))
           (md (cond ((and (= disp 0) (not (= b3 5))) 0) ((x86-i8? disp) 1) (else 2)))
           (head (if (and (< index 0) (not (= b3 4)))
                     (x86-b1 (+ (+ (* 64 md) (* 8 (x86-lo field))) b3))
                     (x86-b2 (+ (+ (* 64 md) (* 8 (x86-lo field))) 4)
                           (+ (+ (* 64 (x86-scale-bits scale))
                                 (* 8 (if (< index 0) 4 (x86-lo index))))
                              b3)))))
      (append head (cond ((= md 1) (x86-le 1 disp)) ((= md 2) (x86-le 4 disp)) (else nil))))))

;; An instruction on two registers: REX, opcode, ModRM with `field` in its
;; `reg` and `rm` in its `rm`.
(define x86-op-rr (subr x86-encodes (int x86-bytes int int) x86-bytes)
  (lambda (w op field rm)
    (append (x86-rex w field 0 rm)
            (append op (x86-b1 (+ (+ 192 (* 8 (x86-lo field))) (x86-lo rm)))))))
;; The same with a memory operand in `rm`.
(define x86-op-rm (subr x86-encodes (int x86-bytes int int int int int) x86-bytes)
  (lambda (w op field base index scale disp)
    (append (x86-rex w field (if (< index 0) 0 index) base)
            (append op (x86-modrm-mem field base index scale disp)))))

;;; ------------------------------------------------------------ moves

(define x86-mov x86-op2 (lambda (d s) (x86-op-rr 1 (x86-b1 137) s d)))
(define x86-load x86-op3 (lambda (d base disp) (x86-op-rm 1 (x86-b1 139) d base -1 1 disp)))
(define x86-load-ix x86-op5
  (lambda (d base index scale disp) (x86-op-rm 1 (x86-b1 139) d base index scale disp)))
(define x86-store x86-op3 (lambda (base disp s) (x86-op-rm 1 (x86-b1 137) s base -1 1 disp)))
(define x86-lea x86-op3 (lambda (d base disp) (x86-op-rm 1 (x86-b1 141) d base -1 1 disp)))
(define x86-lea-ix x86-op5
  (lambda (d base index scale disp) (x86-op-rm 1 (x86-b1 141) d base index scale disp)))
;; `mov d, imm` in as few bytes as do it: 32 bits zero-extended, 32 bits
;; sign-extended, or all 64 (`movabs`). `imm` is the value as a signed or
;; an unsigned integer, either.
(define x86-mov-imm x86-op2
  (lambda (d imm)
    (cond ((and (>= imm 0) (< imm 4294967296))
           (append (x86-rex 0 0 0 d) (cons (+ 184 (x86-lo d)) (x86-le 4 imm))))
          ((and (>= imm -2147483648) (< imm 2147483648))
           (append (x86-op-rr 1 (x86-b1 199) 0 d) (x86-le 4 imm)))
          (else (append (x86-rex 1 0 0 d) (cons (+ 184 (x86-lo d)) (x86-le8 imm)))))))
(define x86-cmov-m x86-op4
  (lambda (c d base disp) (x86-op-rm 1 (x86-b2 15 (+ 64 c)) d base -1 1 disp)))

;;; ------------------------------------------------------------ arithmetic

(define x86-alu x86-op3 (lambda (op d s) (x86-op-rr 1 (x86-b1 (+ (* 8 op) 1)) s d)))
;; `op d, imm`, sign-extended: a byte of it when it fits one, and the short
;; form for rax otherwise, as the assembler chooses.
(define x86-alu-imm x86-op3
  (lambda (op d imm)
    (cond ((x86-i8? imm) (append (x86-op-rr 1 (x86-b1 131) op d) (x86-le 1 imm)))
          ((= d 0) (cons 72 (cons (+ (* 8 op) 5) (x86-le 4 imm))))
          (else (append (x86-op-rr 1 (x86-b1 129) op d) (x86-le 4 imm))))))
(define x86-alu-rm x86-op4
  (lambda (op d base disp) (x86-op-rm 1 (x86-b1 (+ (* 8 op) 3)) d base -1 1 disp)))
(define x86-alu-mi x86-op4
  (lambda (op base disp imm)
    (if (x86-i8? imm)
        (append (x86-op-rm 1 (x86-b1 131) op base -1 1 disp) (x86-le 1 imm))
        (append (x86-op-rm 1 (x86-b1 129) op base -1 1 disp) (x86-le 4 imm)))))
(define x86-test x86-op2 (lambda (a b) (x86-op-rr 1 (x86-b1 133) b a)))
;; `test a32, imm`: the low 32 bits.
(define x86-test-imm x86-op2
  (lambda (a imm)
    (if (= a 0)
        (cons 169 (x86-le 4 imm))
        (append (x86-op-rr 0 (x86-b1 247) 0 a) (x86-le 4 imm)))))
(define x86-shift-imm x86-op3
  (lambda (op d imm)
    (if (= imm 1)
        (x86-op-rr 1 (x86-b1 209) op d)
        (append (x86-op-rr 1 (x86-b1 193) op d) (x86-b1 imm)))))

;;; ------------------------------------------------------------ control

;; Jumps by `rel` from the end of the instruction.
(define x86-jmp x86-op1 (lambda (rel) (cons 233 (x86-le 4 rel))))
(define x86-jcc x86-op2 (lambda (c rel) (cons 15 (cons (+ 128 c) (x86-le 4 rel)))))
(define x86-jmp-r x86-op1 (lambda (s) (x86-op-rr 0 (x86-b1 255) 4 s)))
(define x86-jmp-m x86-op4
  (lambda (base index scale disp) (x86-op-rm 0 (x86-b1 255) 4 base index scale disp)))
(define x86-call-m x86-op2 (lambda (base disp) (x86-op-rm 0 (x86-b1 255) 2 base -1 1 disp)))
;; `mov byte [mem], imm`.
(define x86-store8-imm x86-op5
  (lambda (base index scale disp imm)
    (append (x86-op-rm 0 (x86-b1 198) 0 base index scale disp) (x86-b1 imm))))
(define x86-call-m-ix x86-op4
  (lambda (base index scale disp) (x86-op-rm 0 (x86-b1 255) 2 base index scale disp)))
(define x86-call x86-op1 (lambda (rel) (cons 232 (x86-le 4 rel))))
(define x86-ret x86-op0 (lambda () (x86-b1 195)))

;;; ------------------------------------------------------------ register code's
;;; What register code (`native-x64-regs.fx`) uses besides: the machine
;;; stack, multiplying and dividing, narrow loads, shifts by `cl`, no-ops.

(define x86-push x86-op1
  (lambda (s) (append (x86-rex 0 0 0 s) (x86-b1 (+ 80 (x86-lo s))))))
(define x86-pop x86-op1
  (lambda (d) (append (x86-rex 0 0 0 d) (x86-b1 (+ 88 (x86-lo d))))))
(define x86-push-m x86-op2 (lambda (base disp) (x86-op-rm 0 (x86-b1 255) 6 base -1 1 disp)))
(define x86-pop-m x86-op2 (lambda (base disp) (x86-op-rm 0 (x86-b1 143) 0 base -1 1 disp)))
(define x86-neg x86-op1 (lambda (d) (x86-op-rr 1 (x86-b1 247) 3 d)))
(define x86-neg-m x86-op2 (lambda (base disp) (x86-op-rm 1 (x86-b1 247) 3 base -1 1 disp)))
(define x86-imul x86-op2 (lambda (d s) (x86-op-rr 1 (x86-b2 15 175) d s)))
(define x86-idiv x86-op1 (lambda (s) (x86-op-rr 1 (x86-b1 247) 7 s)))
(define x86-cqo x86-op0 (lambda () (x86-b2 72 153)))
;; `movzx d32, s8`: a REX prefix for s of 4 to 7 too, so that it names
;; `spl` … `dil`, not `ah` … `bh`.
(define x86-movzx8 x86-op2
  (lambda (d s)
    (append (if (or (>= d 8) (>= s 4)) (x86-b1 (+ 64 (+ (* 4 (x86-hi d)) (x86-hi s)))) nil)
            (cons 15 (cons 182 (x86-b1 (+ (+ 192 (* 8 (x86-lo d))) (x86-lo s))))))))
;; `mov d32, [mem]`: 32 bits, zero-extended.
(define x86-load32-ix x86-op5
  (lambda (d base index scale disp) (x86-op-rm 0 (x86-b1 139) d base index scale disp)))
(define x86-shift-cl x86-op2 (lambda (op d) (x86-op-rr 1 (x86-b1 211) op d)))
;; The no-op of `n` bytes, 1 to 9, as the manuals recommend them.
(define x86-nop x86-op1
  (lambda (n)
    (case n
      ((1) (x86-b1 144))
      ((2) (x86-b2 102 144))
      ((3) (cons 15 (x86-b2 31 0)))
      ((4) (cons 15 (cons 31 (x86-b2 64 0))))
      ((5) (cons 15 (cons 31 (cons 68 (x86-b2 0 0)))))
      ((6) (cons 102 (cons 15 (cons 31 (cons 68 (x86-b2 0 0))))))
      ((7) (cons 15 (cons 31 (cons 128 (x86-le 4 0)))))
      ((8) (cons 15 (cons 31 (cons 132 (cons 0 (x86-le 4 0))))))
      (else (cons 102 (cons 15 (cons 31 (cons 132 (cons 0 (x86-le 4 0))))))))))
;; No-ops of `n` bytes more after `acc`, nine at most each.
(define x86-nops-after (subr x86-encodes (int x86-bytes) x86-bytes)
  (lambda (n acc)
    (cond ((= n 0) acc)
          ((> n 9) (x86-nops-after (- n 9) (append acc (x86-nop 9))))
          (else (append acc (x86-nop n))))))
(define x86-nops x86-op1 (lambda (n) (x86-nops-after n nil)))
))
