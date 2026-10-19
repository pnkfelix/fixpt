;;; Raw values, and the operations native code does on them in line, in
;;; FX-26: `direct/x64.rs`'s `box_reg` to `narrow_fast` and `IntSlow`,
;;; step for step and instruction for instruction, each `dr-` and the Rust
;;; name (`dr-box-f64` is `box_f64`), over the native convention's
;;; assembler (`native-direct-x64-asm.fx`). The Rust pieces are these ones'
;;; oracle (`tests/native_direct_x64_raw.rs`).
;;;
;;; A representation (`Rep`) and a conversion (`Convert`) are numbers, as
;;; `native-reps-sig` says; an operation's name (`what`) is the string the
;;; Rust matches.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder, the layout and the
;;; assembler.

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (layout-types (load-module "fx26:native-direct-x64-layout-types.fx"))
       (x86-64-types (load-module "fx26:x86_64-types.fx")))
  (lambda ((x86 (select x86-64-types x86-64-sig))
           (dl (select layout-types native-direct-x64-layout-sig))
           (asm (select direct-types native-direct-x64-asm-sig)))
    (module
(hide (include direct-types))
(hide (include x86) (include dl) (include asm))

;; What a call that takes an `f64` raw puts where the callee returns to
;; (`RAW_F64_MARK`): an eight-byte `nop` whose displacement nothing else
;; emits; the same as a word, lowest byte first; and how far past the
;; return address a callee returning one raw returns (`RAW_F64_SKIP`).
(define dr-mark-bytes (subr da-assembles () da-bytes)
  ;; cons-chain: in `@k`, which `list` would not be
  (lambda () (cons 15 (cons 31 (cons 132 (cons 0 (cons 79 (cons 246 (cons 79 (cons 246 nil))))))))))
(define dr-mark-word int 17748675475661922063)
(define dr-raw-f64-skip int 13)

;; Scalar operations, by their opcodes (`Fop`).
(define dr-sqrt int 81)
(define dr-fadd int 88)
(define dr-fmul int 89)
(define dr-fsub int 92)
(define dr-fdiv int 94)

(define dr-bit (subr pure (bool) int) (lambda (b) (if b 1 0)))
;; Whether `s` begins with `p`, and what follows it.
(define dr-prefix? (subr pure (string string) bool)
  (lambda (s p) (= (string-search s p 0) 0)))
(define dr-after (subr pure (string string) string)
  (lambda (s p) (substring s (string-length p) (string-length s))))

;;; ------------------------------------------------------------ boxing

;; Register `r`'s raw `i64` (signed) or `u64` boxed, in place.
(define dr-box-reg (subr da-assembles (int bool) unit)
  (lambda (r signed)
    (let ((slow (da-label)) (done (da-label)))
      (begin
        (if signed
            (begin
              (da-mov d-x16 r)
              (da-e (x86-shift-imm da-shl d-x16 3))
              (da-mov d-x13 d-x16)
              (da-e (x86-shift-imm da-sar d-x13 3))
              (da-e (x86-alu da-cmp d-x13 r))
              (da-jcc da-c-ne slow)
              (da-mov r d-x16))
            (begin
              (da-mov d-x13 r)
              (da-e (x86-shift-imm da-shr d-x13 60))
              (da-jcc da-c-ne slow)
              (da-e (x86-shift-imm da-shl r 3))))
        (da-jmp done)
        (da-bind slow)
        (da-pure-call (da-co d-co-box (dr-bit signed) 0) (da-args1 r) r)
        (da-bind done)))))

;; Register `r`'s exact integer unboxed, in place: its low 64 bits.
(define dr-unbox-reg (subr da-assembles (int) unit)
  (lambda (r)
    (let ((slow (da-label)) (done (da-label)))
      (begin
        (da-e (x86-test-imm r 7))
        (da-jcc da-c-ne slow)
        (da-e (x86-shift-imm da-sar r 3))
        (da-jmp done)
        (da-bind slow)
        (da-pure-call (da-co d-co-unbox 0 0) (da-args1 r) r)
        (da-bind done)))))

;; Register `r`'s flonum unboxed, in place: its double's bits; anything but
;; a bloblet gives 0.
(define dr-unbox-f64 (subr da-assembles (int) unit)
  (lambda (r)
    (let ((other (da-label)) (done (da-label)))
      (begin
        (da-mov d-x16 r)
        (da-e (x86-alu-imm da-and d-x16 7))
        (da-e (x86-alu-imm da-cmp d-x16 d-tag-bloblet))
        (da-jcc da-c-ne other)
        (da-ld r r -4)
        (da-jmp done)
        (da-bind other)
        (da-imm r 0)
        (da-bind done)))))

;; The parameters in `params` unboxed, at a procedure's entry.
(define dr-raw-entry (subr da-assembles (int) unit)
  (lambda (params)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r)
                 (if (> r 8)
                     #u
                     (begin
                       (if (= (bitwise-and params (arithmetic-shift 1 (- r 1))) 0)
                           #u
                           (da-in-place r (lambda ((x int)) (dr-unbox-f64 x))))
                       (go (+ r 1)))))))
      (go 1))))

;; Bytes from a procedure's entry past its unboxing of `params`: emitted,
;; measured, and taken back.
(define dr-raw-entry-skip (subr da-assembles (int) int)
  (lambda (params)
    (let* ((m (da-mark)) (from (da-here)))
      (begin
        (dr-raw-entry params)
        (let ((n (- (da-here) from)))
          (begin (da-rewind m) n))))))

;; After a call whose value only `f64` operations use: the value raw in
;; `RESULT`.
(define dr-take-raw-f64 (subr da-assembles () unit)
  (lambda ()
    (let ((boxed (da-label)) (join (da-label)))
      (begin
        (da-e (dr-mark-bytes))
        (da-jmp boxed)
        (da-jmp join)
        (da-bind boxed)
        (dr-unbox-f64 d-result)
        (da-bind join)))))

;; Register `r`'s raw `f64` boxed, in place. Uses X11 and X13 to X17.
(define dr-box-f64 (subr da-assembles (int) unit)
  (lambda (r)
    (let ((slow (da-label)) (done (da-label)))
      (begin
        (da-ld d-x13 d-st d-st-top)
        (da-ld d-x14 d-x13 0)
        (da-e (x86-lea d-x16 d-x14 2))
        (da-e (x86-alu-rm da-cmp d-x16 d-st d-st-alloc-limit))
        (da-jcc da-c-a slow)
        (da-ld d-x17 d-st d-st-words)
        (da-e (x86-lea-ix d-x11 d-x17 d-x14 8 0))
        (da-imm d-x17 (da-header d-flonum 0 8))
        (da-sto d-x11 0 d-x17)
        (da-sto d-x11 8 r)
        (da-sto d-x13 0 d-x16)
        (da-e (x86-lea r d-x11 (+ 8 d-tag-bloblet)))
        (da-jmp done)
        (da-bind slow)
        (da-pure-call (da-co d-co-box-f64 0 0) (da-args1 r) r)
        (da-bind done)))))

;; A return of the raw `f64` in `RESULT`: as it is, past the mark, where
;; the caller takes it so; else boxed.
(define dr-raw-return (subr da-assembles () unit)
  (lambda ()
    (let ((boxed (da-label)))
      (begin
        (da-ld d-x16 d-sp 0)
        (da-ld d-x16 d-x16 0)
        (da-imm d-x17 dr-mark-word)
        (da-e (x86-alu da-cmp d-x16 d-x17))
        (da-jcc da-c-ne boxed)
        (da-e (x86-alu-mi da-add d-sp 0 dr-raw-f64-skip))
        (da-e (x86-ret))
        (da-bind boxed)
        (dr-box-f64 d-result)
        (da-e (x86-ret))))))

;; An `f64` boxed from the free space into `RESULT`, its bits in X9; to
;; `slow` when there is no room.
(define dr-box-bits (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (da-ld d-x13 d-st d-st-top)
      (da-ld d-x14 d-x13 0)
      (da-e (x86-lea d-x16 d-x14 2))
      (da-e (x86-alu-rm da-cmp d-x16 d-st d-st-alloc-limit))
      (da-jcc da-c-a slow)
      (da-ld d-x17 d-st d-st-words)
      (da-e (x86-lea-ix d-x11 d-x17 d-x14 8 0))
      (da-imm d-x17 (da-header d-flonum 0 8))
      (da-sto d-x11 0 d-x17)
      (da-sto d-x11 8 d-x9)
      (da-sto d-x13 0 d-x16)
      (da-e (x86-lea d-result d-x11 (+ 8 d-tag-bloblet))))))

;; `REGr`'s value unboxed to `rep`, in place.
(define dr-unbox-to (subr da-assembles (int int) unit)
  (lambda (r rep)
    (da-in-place r (lambda ((x int)) (if (= rep 4) (dr-unbox-f64 x) (dr-unbox-reg x))))))

;; The conversions `reps` asks for before an instruction; a test for a
;; fixnum going to `general` where it fails. `result` is where `RESULT`'s
;; value is.
(define dr-convert (subr da-assembles (da-bytes int int) unit)
  (lambda (cs general result)
    (if (null? cs)
        #u
        (let* ((c (car cs)) (kind (quotient c 128)) (r (modulo (quotient c 8) 16))
               (rep (modulo c 8)))
          (begin
            (cond ((and (= kind 0) (or (= rep 2) (= rep 3)))
                   (da-in-place r (lambda ((x int)) (dr-box-reg x (= rep 2)))))
                  ((= kind 0) (da-in-place r (lambda ((x int)) (dr-box-f64 x))))
                  ((= kind 1) (dr-unbox-to r rep))
                  ((= r 0) (da-check-reg result general))
                  (else (da-check-fixnum r general)))
            (dr-convert (cdr cs) general result))))))

;;; ------------------------------------------------------------ f64 and f32

;; `int->f64` (primitive `p`) of the int in `RESULT`, raw into `RESULT`.
(define dr-f64-of-int (subr da-assembles (int) unit)
  (lambda (p)
    (let ((slow (da-label)) (done (da-label)))
      (begin
        (da-e (x86-test-imm d-result 7))
        (da-jcc da-c-ne slow)
        (da-mov d-x13 d-result)
        (da-e (x86-shift-imm da-sar d-x13 3))
        (da-e (x86-cvtsi2sd 0 d-x13))
        (da-e (x86-movq-from-xmm d-result 0))
        (da-jmp done)
        (da-bind slow)
        (da-pure-call (da-co d-co-pure p 1) (da-args1 d-result) d-result)
        (dr-unbox-f64 d-result)
        (da-bind done)))))

;; `f64->int` (primitive `p`) of the raw `f64` in `RESULT`, into `RESULT`.
(define dr-int-of-f64 (subr da-assembles (int) unit)
  (lambda (p)
    (let ((slow (da-label)) (done (da-label)))
      (begin
        (da-e (x86-movq-to-xmm 0 d-result))
        (da-e (x86-cvttsd2si d-x13 0))
        (da-e (x86-cvtsi2sd 1 d-x13))
        (da-e (x86-ucomis 1 0 1))
        (da-jcc da-c-ne slow)
        (da-jcc da-c-p slow)
        (da-mov d-x14 d-x13)
        (da-e (x86-shift-imm da-shl d-x14 3))
        (da-mov d-x15 d-x14)
        (da-e (x86-shift-imm da-sar d-x15 3))
        (da-e (x86-alu da-cmp d-x15 d-x13))
        (da-jcc da-c-ne slow)
        (da-mov d-result d-x14)
        (da-jmp done)
        (da-bind slow)
        (dr-box-f64 d-result)
        (da-pure-call (da-co d-co-pure p 1) (da-args1 d-result) d-result)
        (da-trap-set)
        (da-bind done)))))

;; After `ucomis`, the comparison `what` into `RESULT`, `#f` where either
;; is a NaN; false for no comparison.
(define dr-float-test (subr da-assembles (bool string) bool)
  (lambda (double what)
    (let ((test (lambda ((l int) (r int) (c int))
              (begin
                (da-e (x86-ucomis (dr-bit double) l r))
                (da-flag c d-x13)
                (if (string=? what "=")
                    (begin (da-imm d-x13 d-false) (da-e (x86-cmov da-c-p d-result d-x13)))
                    #u)
                #t))))
      (case what
        (("<") (test 1 0 da-c-a))
        (("<=") (test 1 0 da-c-ae))
        ((">") (test 0 1 da-c-a))
        ((">=") (test 0 1 da-c-ae))
        (("=") (test 0 1 da-c-e))
        (else #f)))))

;; An `f64` operation `what` on raw `RESULT` and `y`, into `RESULT`.
(define dr-f64-fast (subr da-assembles (string int) unit)
  (lambda (what y)
    (begin
      (da-e (x86-movq-to-xmm 0 d-result))
      (da-e (x86-movq-to-xmm 1 y))
      (cond ((dr-float-test #t what) #u)
            ((string=? what "-abs")
             (begin (da-e (x86-shift-imm da-shl d-result 1))
                    (da-e (x86-shift-imm da-shr d-result 1))))
            ((string=? what "-neg")
             (begin (da-imm d-x13 9223372036854775808) (da-e (x86-alu da-xor d-result d-x13))))
            (else
             (begin
               (da-e (case what
                       (("+") (x86-fop 1 dr-fadd 0 1))
                       (("-") (x86-fop 1 dr-fsub 0 1))
                       (("*") (x86-fop 1 dr-fmul 0 1))
                       (("/") (x86-fop 1 dr-fdiv 0 1))
                       (("-sqrt") (x86-fop 1 dr-sqrt 0 0))
                       (("-floor") (x86-round 1 0 0 1))
                       (("-ceiling") (x86-round 1 0 0 2))
                       (("-truncate") (x86-round 1 0 0 3))
                       (else (x86-round 1 0 0 0))))
               (da-e (x86-movq-from-xmm d-result 0))))))))

;; Whether `what` is an `f32` operation done in line.
(define dr-f32-known? (subr pure (string) bool)
  (lambda (what)
    (case what
      (("<" "<=" ">" ">=" "=" "+" "-" "*" "/" "-abs" "-neg" "-sqrt" "-floor" "-ceiling"
        "-truncate" "-round")
       #t)
      (else #f))))
;; The operation of an `f32` one, none for `-abs` and `-neg`.
(define dr-f32-op (subr da-assembles (string) da-bytes)
  (lambda (what)
    (case what
      (("+") (x86-fop 0 dr-fadd 0 1))
      (("-") (x86-fop 0 dr-fsub 0 1))
      (("*") (x86-fop 0 dr-fmul 0 1))
      (("/") (x86-fop 0 dr-fdiv 0 1))
      (("-sqrt") (x86-fop 0 dr-sqrt 0 0))
      (("-floor") (x86-round 0 0 0 1))
      (("-ceiling") (x86-round 0 0 0 2))
      (("-truncate") (x86-round 0 0 0 3))
      (("-round") (x86-round 0 0 0 0))
      (else nil))))
;; An `f32` operation `what` on the immediates in `RESULT` and `y`, into
;; `RESULT`; false for one the runtime does.
(define dr-f32-fast (subr da-assembles (string int) bool)
  (lambda (what y)
    (if (not (dr-f32-known? what))
        #f
        (begin
          (da-mov d-x13 d-result)
          (da-e (x86-shift-imm da-shr d-x13 32))
          (da-e (x86-movd-to-xmm 0 d-x13))
          (da-mov d-x14 y)
          (da-e (x86-shift-imm da-shr d-x14 32))
          (da-e (x86-movd-to-xmm 1 d-x14))
          (if (dr-float-test #f what)
              #u
              (begin
                (da-e (dr-f32-op what))
                (da-e (x86-movd-from-xmm d-x13 0))
                (cond ((string=? what "-abs")
                       (begin (da-imm d-x14 2147483647) (da-e (x86-alu da-and d-x13 d-x14))))
                      ((string=? what "-neg") (da-e (x86-alu-imm da-xor d-x13 -2147483648)))
                      (else #u))
                (da-e (x86-shift-imm da-shl d-x13 32))
                (da-e (x86-lea d-result d-x13 (modulo d-f32-0 256)))))
          #t))))

;;; ------------------------------------------------------------ integers

;; `RESULT`, the fixnum of an integer, wrapped to a type of `bits` bits.
(define dr-wrap-small (subr da-assembles (bool int) unit)
  (lambda (signed bits)
    (let ((k (- 61 bits)))
      (begin
        (da-e (x86-shift-imm da-shl d-result k))
        (da-e (x86-shift-imm (if signed da-sar da-shr) d-result k))))))

;; A comparison's condition, by its name and signedness; -1 for none.
(define dr-compare (subr pure (string bool) int)
  (lambda (what signed)
    (case what
      (("<") (if signed da-c-l da-c-b))
      (("<=") (if signed da-c-le da-c-be))
      ((">") (if signed da-c-g da-c-a))
      ((">=") (if signed da-c-ge da-c-ae))
      (("=") da-c-e)
      (else -1))))

;; `i64` or `u64` division of `RESULT` by `y`: the quotient, or with
;; `remainder` the remainder, into `RESULT`.
(define dr-divide (subr da-assembles (bool int bool) unit)
  (lambda (signed y remainder)
    (let ((done (begin (da-e (x86-test y y)) (da-trap d-divided-by-zero da-c-e) (da-label))))
      (begin
        (if signed
            (let ((normal (da-label)))
              (begin
                (da-e (x86-alu-imm da-cmp y -1))
                (da-jcc da-c-ne normal)
                (if remainder (da-imm d-result 0) (da-e (x86-neg d-result)))
                (da-jmp done)
                (da-bind normal)
                (da-e (x86-cqo))
                (da-e (x86-idiv y))))
            (begin (da-imm d-rdx 0) (da-e (x86-div y))))
        (if remainder (da-mov d-result d-rdx) #u)
        (da-bind done)))))

;; An `i64` (signed) or `u64` operation `what` on raw `RESULT` and `y`,
;; into `RESULT`.
(define dr-raw-fast (subr da-assembles (bool string int) unit)
  (lambda (signed what y)
    (let ((c (dr-compare what signed)))
      (if (>= c 0)
          (begin (da-e (x86-alu da-cmp d-result y)) (da-flag c d-x13))
          (case what
            (("from") #u)
            (("+") (da-e (x86-alu da-add d-result y)))
            (("-") (da-e (x86-alu da-sub d-result y)))
            (("*") (da-e (x86-imul d-result y)))
            (("-and") (da-e (x86-alu da-and d-result y)))
            (("-or") (da-e (x86-alu da-or d-result y)))
            (("-xor") (da-e (x86-alu da-xor d-result y)))
            (("-not") (da-e (x86-not d-result)))
            (("-quotient") (dr-divide signed y #f))
            (("-remainder") (dr-divide signed y #t))
            (("-shl" "-shr")
             (begin
               (da-mov d-rcx y)
               (da-e (x86-shift-imm da-shr d-rcx 3))
               (da-e (x86-shift-cl (cond ((string=? what "-shl") da-shl) (signed da-sar)
                                         (else da-shr))
                                   d-result))))
            (else (da-fail "a 64-bit operation")))))))

;; A narrow type's signedness (1 signed, 0 not) and bits, -1 for none.
(define dr-width-signed (subr pure (string) int)
  (lambda (t) (case t (("i8" "i32") 1) (("u8" "u32") 0) (else -1))))
(define dr-width-bits (subr pure (string) int)
  (lambda (t) (case t (("i8" "u8") 8) (("i32" "u32") 32) (else -1))))
;; The narrow type `rest` begins with, its operation not one of digits;
;; "" for none.
(define dr-narrow-type (subr pure (string) string)
  (lambda (rest)
    (let ((fits (lambda ((t string))
                  (and (dr-prefix? rest t)
                       (let ((op (dr-after rest t)))
                         (or (= (string-length op) 0)
                             (not (char-numeric? (string-ref op 0)))))))))
      (cond ((fits "i8") "i8") ((fits "u8") "u8") ((fits "i32") "i32") ((fits "u32") "u32")
            (else "")))))

;; Of `narrow_fast`: operation `op` of the type of `bits` bits.
(define dr-narrow-op (subr da-assembles (bool int string int int) bool)
  (lambda (s bits op y slow)
    (let ((nonzero (lambda () (begin (da-e (x86-test y y)) (da-jcc da-c-e slow))))
          (c (case op (("<") da-c-l) (("<=") da-c-le) ((">") da-c-g) ((">=") da-c-ge)
                      (("=") da-c-e) (else -1))))
      (if (>= c 0)
          (begin (da-e (x86-alu da-cmp d-result y)) (da-flag c d-x13) #t)
          (case op
            (("->int") #t)
            (("+") (begin (da-e (x86-alu da-add d-result y)) (dr-wrap-small s bits) #t))
            (("-") (begin (da-e (x86-alu da-sub d-result y)) (dr-wrap-small s bits) #t))
            (("*")
             (begin (da-mov d-x13 y) (da-e (x86-shift-imm da-sar d-x13 3))
                    (da-e (x86-imul d-result d-x13)) (dr-wrap-small s bits) #t))
            (("-quotient")
             (begin (nonzero) (da-e (x86-cqo)) (da-e (x86-idiv y))
                    (da-e (x86-shift-imm da-shl d-result 3)) (dr-wrap-small s bits) #t))
            (("-remainder")
             (begin (nonzero) (da-e (x86-cqo)) (da-e (x86-idiv y)) (da-mov d-result d-rdx) #t))
            (("-and") (begin (da-e (x86-alu da-and d-result y)) #t))
            (("-or") (begin (da-e (x86-alu da-or d-result y)) #t))
            (("-xor") (begin (da-e (x86-alu da-xor d-result y)) #t))
            (("-not")
             (begin (da-e (x86-neg d-result)) (da-e (x86-alu-imm da-sub d-result 8))
                    (dr-wrap-small s bits) #t))
            (("-shl" "-shr")
             (begin
               (da-e (x86-test-imm y 7))
               (da-jcc da-c-ne slow)
               (da-mov d-rcx y)
               (da-e (x86-shift-imm da-shr d-rcx 3))
               (da-e (x86-alu-imm da-and d-rcx (- bits 1)))
               (if (string=? op "-shl")
                   (begin (da-e (x86-shift-cl da-shl d-result)) (dr-wrap-small s bits))
                   (begin (da-e (x86-shift-cl (if s da-sar da-shr) d-result))
                          (da-e (x86-alu-imm da-and d-result -8))))
               #t))
            (else #f))))))

;; The rest of `pure_fast`: `f32` operations, and the 8- and 32-bit
;; integers', each the fixnum of its value.
(define dr-narrow-fast (subr da-assembles (string int int) bool)
  (lambda (name y slow)
    (if (not (dr-prefix? name "%fx26-"))
        #f
        (let ((rest (dr-after name "%fx26-")))
          (cond
            ((dr-prefix? rest "f32") (dr-f32-fast (dr-after rest "f32") y))
            ((and (dr-prefix? rest "int->") (>= (dr-width-bits (dr-after rest "int->")) 0))
             (let ((t (dr-after rest "int->")))
               (begin
                 (da-e (x86-test-imm d-result 7))
                 (da-jcc da-c-ne slow)
                 (dr-wrap-small (= (dr-width-signed t) 1) (dr-width-bits t))
                 #t)))
            (else
             (let ((t (dr-narrow-type rest)))
               (if (string=? t "")
                   #f
                   (dr-narrow-op (= (dr-width-signed t) 1) (dr-width-bits t) (dr-after rest t)
                                 y slow)))))))))

;; The slow path of an `int` operation (`IntSlow::emit`).
(define dr-int-slow (subr da-assembles (dr-int-slow) unit)
  (lambda (s)
    (let ((overflow (extract s 2)) (x (extract s 4)) (y (extract s 5)) (imm (extract s 6))
          (into (extract s 7)) (branch (extract s 10)))
      (begin
        (if (< overflow 0)
            #u
            (begin
              (da-bind overflow)
              (if (= into x)
                  (let ((undo (if (extract s 9) da-add da-sub)))
                    (if (< y 0)
                        (da-e (x86-alu-imm undo x imm))
                        (da-e (x86-alu undo x y))))
                  #u)))
        (da-bind (extract s 1))
        (let ((y2 (if (< y 0) (begin (da-imm d-x16 imm) d-x16) y)))
          (da-pure-call (da-co d-co-pure (extract s 8) 2) (da-args2 x y2) into))
        (da-trap-set)
        (if (< branch 0)
            #u
            (begin (da-cmp-k d-result d-true)
                   (da-jcc (if (extract s 11) da-c-e da-c-ne) branch)))
        (da-jmp (extract s 3))))))
)))
