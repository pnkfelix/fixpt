;;; The native convention's compiler to x86_64 written in FX-26: the
;;; primitives of strings and characters (`string=?`, `string-ref`, the
;;; character tests), each the instructions of `procedure_x64`'s own
;;; (`fixpt-native/src/direct/x64.rs`). Apart from
;;; `native-direct-x64-prims.fx` since 2026-10-31 (`TODO.md` §188), which
;;; makes it of the modules it is given and gives on all it defines.
;;; A file of one expression (`load-input`, `TODO.md` §68).


(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (direct-layout-types (load-module "fx26:native-direct-x64-layout-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (x86-64-types (load-module "fx26:x86_64-types.fx")))
  (lambda ((x86 (select x86-64-types x86-64-sig))
           (dl (select direct-layout-types native-direct-x64-layout-sig))
           (layout (select layout-types layout-sig))
           (asm (select direct-types native-direct-x64-asm-sig))
           (reps (select direct-types native-reps-sig))
           (raw (select direct-types native-direct-x64-raw-sig))
           (flat (select direct-types native-direct-x64-flat-sig))
           (proc (select direct-types native-direct-x64-proc-sig)))
    (module
(hide (include direct-types))
(hide (include x86) (include dl) (include layout) (include asm) (include reps) (include raw)
      (include flat) (include proc))

;; `string=?` of the strings in `x` and `y`, into `RESULT`: their lengths,
;; then their characters, 32 bits each, as register code's.
(define dq-string-eq (subr da-assembles (int int) unit)
  (lambda (x y)
    (let ((again (da-label)) (yes (da-label)) (no (da-label)) (end (da-label)))
      (begin
        (da-ld d-x13 x -4)
        (da-e (x86-alu-rm da-cmp d-x13 y -4))
        (da-jcc da-c-ne no)
        (da-mov d-x14 x)
        (da-mov d-x15 y)
        (da-bind again)
        (da-e (x86-test d-x13 d-x13))
        (da-jcc da-c-e yes)
        (da-e (x86-load32-ix d-x16 d-x14 -1 1 4))
        (da-e (x86-load32-ix d-x9 d-x15 -1 1 4))
        (da-e (x86-alu da-cmp d-x16 d-x9))
        (da-jcc da-c-ne no)
        (da-e (x86-alu-imm da-add d-x14 4))
        (da-e (x86-alu-imm da-add d-x15 4))
        (da-e (x86-alu-imm da-sub d-x13 1))
        (da-jmp again)
        (da-bind yes)
        (da-imm d-result d-true)
        (da-jmp end)
        (da-bind no)
        (da-imm d-result d-false)
        (da-bind end)))))

;; `%fx26-string<?` of the strings in `x` and `y`, into `RESULT`: the
;; first code point that differs, unsigned, else the shorter
;; (`Heap::string_cmp`); `x` and `y` kept until `RESULT` is written.
(define dq-string-lt (subr da-assembles (int int) unit)
  (lambda (x y)
    (let ((again (da-label)) (differ (da-label)) (end (da-label)) (out (da-label)))
      (begin
        (da-ld d-x13 x -4)
        (da-ld d-x14 y -4)
        (da-mov d-x15 d-x13)
        (da-e (x86-alu da-cmp d-x14 d-x15))
        (da-e (x86-cmov da-c-b d-x15 d-x14))
        (da-imm d-x16 0)
        (da-bind again)
        (da-e (x86-alu da-cmp d-x16 d-x15))
        (da-jcc da-c-ae end)
        (da-e (x86-load32-ix d-x9 x d-x16 4 4))
        (da-e (x86-load32-ix d-x11 y d-x16 4 4))
        (da-e (x86-alu da-cmp d-x9 d-x11))
        (da-jcc da-c-ne differ)
        (da-e (x86-alu-imm da-add d-x16 1))
        (da-jmp again)
        (da-bind differ)
        (da-flag da-c-b d-x12)
        (da-jmp out)
        (da-bind end)
        (da-e (x86-alu da-cmp d-x13 d-x14))
        (da-flag da-c-b d-x12)
        (da-bind out)))))

;; The code point of the character in `x`, into `into`; to `slow` if `x` is
;; not a character.
(define dq-char-point (subr da-assembles (int int int) unit)
  (lambda (x into slow)
    (begin
      (da-mov into x)
      (da-e (x86-alu-imm da-and into 255))
      (da-e (x86-alu-imm da-cmp into d-char0))
      (da-jcc da-c-ne slow)
      (da-mov into x)
      (da-e (x86-shift-imm da-shr into 8)))))

;; `char-whitespace?` of the character in `x`, into `RESULT`: of ASCII here
;; (tab, line feed, line tabulation, form feed, carriage return, space); of
;; the rest, Unicode's, the primitive's at `slow`, as of what is not one.
(define dq-char-whitespace (subr da-assembles (int int) unit)
  (lambda (x slow)
    (let ((no (da-label)) (end (da-label)))
      (begin
        (dq-char-point x d-x13 slow)
        (da-e (x86-alu-imm da-cmp d-x13 128))
        (da-jcc da-c-ae slow)
        (da-e (x86-alu-imm da-cmp d-x13 32))
        (da-jcc da-c-a no)
        (da-imm d-x14 (+ (arithmetic-shift 1 32) 15872))
        (da-e (x86-shift-cl da-shr d-x14))
        (da-e (x86-test-imm d-x14 1))
        (da-jcc da-c-e no)
        (da-imm d-result d-true)
        (da-jmp end)
        (da-bind no)
        (da-imm d-result d-false)
        (da-bind end)))))

;; `%fx26-char-in?` of the character in `c` and the string in `s`, into
;; `RESULT`: each of its characters, 32 bits, compared with the code point.
(define dq-char-in (subr da-assembles (int int) unit)
  (lambda (c s)
    (let ((again (da-label)) (yes (da-label)) (no (da-label)) (end (da-label)))
      (begin
        (da-ld d-x13 s -4)
        (da-mov d-x14 s)
        (da-mov d-x15 c)
        (da-e (x86-shift-imm da-shr d-x15 8))
        (da-bind again)
        (da-e (x86-test d-x13 d-x13))
        (da-jcc da-c-e no)
        (da-e (x86-load32-ix d-x16 d-x14 -1 1 4))
        (da-e (x86-alu da-cmp d-x16 d-x15))
        (da-jcc da-c-e yes)
        (da-e (x86-alu-imm da-add d-x14 4))
        (da-e (x86-alu-imm da-sub d-x13 1))
        (da-jmp again)
        (da-bind yes)
        (da-imm d-result d-true)
        (da-jmp end)
        (da-bind no)
        (da-imm d-result d-false)
        (da-bind end))))))))
