;;; Flat arrays, suffix refs, bytevectors and shapes in line, for the native
;;; convention's compiler to x86_64 written in FX-26: `direct/x64.rs`'s
;;; `flat_count` to `flat_set` and `shape_fast`, step for step and
;;; instruction for instruction, each `df-` and its Rust name. The Rust
;;; pieces are these' oracle (`tests/native_direct_x64_flat.rs`).
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder, the layout, the
;;; assembler and the raw values' module (for `box_bits`).

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (layout-types (load-module "fx26:native-direct-x64-layout-types.fx"))
       (x86-64-types (load-module "fx26:x86_64-types.fx")))
  (lambda ((x86 (select x86-64-types x86-64-sig))
           (dl (select layout-types native-direct-x64-layout-sig))
           (asm (select direct-types native-direct-x64-asm-sig))
           (raw (select direct-types native-direct-x64-raw-sig)))
    (module
(hide (include direct-types))
(hide (include x86) (include dl) (include asm) (include raw))

;;; ------------------------------------------------------------ shorthands
;;; The Rust encoder's names for what these pieces emit.

(define df-and-imm (subr da-assembles (int int) unit)
  (lambda (d imm) (da-e (x86-alu-imm da-and d imm))))
(define df-cmp-imm (subr da-assembles (int int) unit)
  (lambda (d imm) (da-e (x86-alu-imm da-cmp d imm))))
(define df-add-imm (subr da-assembles (int int) unit)
  (lambda (d imm) (da-e (x86-alu-imm da-add d imm))))
(define df-sub-imm (subr da-assembles (int int) unit)
  (lambda (d imm) (da-e (x86-alu-imm da-sub d imm))))
(define df-cmp (subr da-assembles (int int) unit) (lambda (a b) (da-e (x86-alu da-cmp a b))))
(define df-add (subr da-assembles (int int) unit) (lambda (d s) (da-e (x86-alu da-add d s))))
(define df-sub (subr da-assembles (int int) unit) (lambda (d s) (da-e (x86-alu da-sub d s))))
(define df-or (subr da-assembles (int int) unit) (lambda (d s) (da-e (x86-alu da-or d s))))
(define df-shl (subr da-assembles (int int) unit)
  (lambda (d n) (da-e (x86-shift-imm da-shl d n))))
(define df-shr (subr da-assembles (int int) unit)
  (lambda (d n) (da-e (x86-shift-imm da-shr d n))))
(define df-sar (subr da-assembles (int int) unit)
  (lambda (d n) (da-e (x86-shift-imm da-sar d n))))
(define df-test-imm (subr da-assembles (int int) unit)
  (lambda (a imm) (da-e (x86-test-imm a imm))))
(define df-neg (subr da-assembles (int) unit) (lambda (d) (da-e (x86-neg d))))
;; `mov [base], s32`.
(define df-store32 (subr da-assembles (int int) unit)
  (lambda (base s) (da-e (x86-store32-ix base -1 1 0 s))))
;; Register `r`'s tag `tag`, else to `slow` (uses `t`).
(define df-tagged (subr da-assembles (int int int int) unit)
  (lambda (t r tag slow)
    (begin (da-mov t r) (df-and-imm t 7) (df-cmp-imm t tag) (da-jcc da-c-ne slow))))
;; A flat layout's element size in bytes (`flat_size`).
(define df-flat-size (subr pure (int) int)
  (lambda (code)
    (if (or (= code d-flat-i32) (or (= code d-flat-u32) (= code d-flat-f32))) 4 8)))
;; `layout::array_operand_parts`: a flat array's length, and its element's
;; size.
(define df-operand-n (subr pure (int) int)
  (lambda (code) (arithmetic-shift code (- 0 d-array-operand-length-shift))))
(define df-operand-size (subr pure (int) int)
  (lambda (code)
    (bitwise-and code (- (arithmetic-shift 1 d-array-operand-size-bits) 1))))
;; An `f32`'s immediate tag, its low byte.
(define df-f32-tag int (bitwise-and d-f32-0 255))

;;; ------------------------------------------------------------ flat arrays

;; `out` := how many elements the flat array in `arr` has (untagged). Uses
;; X11 and X16.
(define df-flat-count (subr da-assembles (int int) unit)
  (lambda (arr out)
    (let ((wide (da-label)) (done (da-label)))
      (begin
        (da-ld out arr -28)
        (df-shr out 32)
        (da-ld d-x16 arr (da-field-off 2))
        (df-shr d-x16 3)
        (df-cmp-imm d-x16 d-flat-i64)
        (da-jcc da-c-e wide)
        (df-cmp-imm d-x16 d-flat-u64)
        (da-jcc da-c-e wide)
        (df-cmp-imm d-x16 d-flat-f64)
        (da-jcc da-c-e wide)
        (df-shr out 2)
        (da-jmp done)
        (da-bind wide)
        (df-shr out 3)
        (da-bind done)))))

;; Where a flat array's elements are, and element `y`: X14 the index, X15
;; the suffix, X16 the layout, as a fixnum; to `slow` unless the index is
;; a fixnum in range.
(define df-flat-element (subr da-assembles (int int int) unit)
  (lambda (arr y slow)
    (begin
      (df-test-imm y 7)
      (da-jcc da-c-ne slow)
      (da-mov d-x14 y)
      (df-sar d-x14 3)
      (df-flat-count arr d-x13)
      (df-cmp d-x14 d-x13)
      (da-jcc da-c-ae slow)
      (da-ld d-x16 arr (da-field-off 2))
      (da-e (x86-lea d-x15 arr (- 0 d-tag-bloblet))))))

;; To `not` unless the layout in X16 is `code`'s.
(define df-is (subr da-assembles (int int int) unit)
  (lambda (r code not) (begin (df-cmp-imm r (* code 8)) (da-jcc da-c-ne not))))

;; An `i64` (or `u64`, by the layout in X16) in X13 into `RESULT` as a
;; fixnum, to `end`; else to `slow`.
(define df-flat-wide (subr da-assembles (int int) unit)
  (lambda (slow end)
    (let ((unsigned (da-label)))
      (begin
        (df-cmp-imm d-x16 (* d-flat-u64 8))
        (da-jcc da-c-e unsigned)
        (da-mov d-x14 d-x13)
        (df-shl d-x14 3)
        (da-mov d-x15 d-x14)
        (df-sar d-x15 3)
        (df-cmp d-x15 d-x13)
        (da-jcc da-c-ne slow)
        (da-mov d-result d-x14)
        (da-jmp end)
        (da-bind unsigned)
        (da-mov d-x15 d-x13)
        (df-shr d-x15 60)
        (da-jcc da-c-ne slow)
        (df-shl d-x13 3)
        (da-mov d-result d-x13)))))

;; `flatarray-ref` of the flat array in `RESULT` at `y`, into `RESULT`.
(define df-flat-ref (subr da-assembles (int int) unit)
  (lambda (y slow)
    (let ((end (da-label)))
      (begin
        (df-flat-element d-result y slow)
        (let ((not-f64 (da-label)) (not-f32 (da-label)) (not-i32 (da-label))
              (not-u32 (da-label)))
          (begin
            (df-is d-x16 d-flat-f64 not-f64)
            (da-e (x86-load-ix d-x9 d-x15 d-x14 8 0))
            (dr-box-bits slow)
            (da-jmp end)
            (da-bind not-f64)
            (df-is d-x16 d-flat-f32 not-f32)
            (da-e (x86-load32-ix d-x13 d-x15 d-x14 4 0))
            (df-shl d-x13 32)
            (da-e (x86-lea d-result d-x13 df-f32-tag))
            (da-jmp end)
            (da-bind not-f32)
            (df-is d-x16 d-flat-i32 not-i32)
            (da-e (x86-load32s-ix d-x13 d-x15 d-x14 4 0))
            (df-shl d-x13 3)
            (da-mov d-result d-x13)
            (da-jmp end)
            (da-bind not-i32)
            (df-is d-x16 d-flat-u32 not-u32)
            (da-e (x86-load32-ix d-x13 d-x15 d-x14 4 0))
            (df-shl d-x13 3)
            (da-mov d-result d-x13)
            (da-jmp end)
            (da-bind not-u32)
            (da-e (x86-load-ix d-x13 d-x15 d-x14 8 0))
            (df-flat-wide slow end)
            (da-bind end)))))))

;;; ------------------------------------------------------------ suffix refs

;; Suffix ref `r` taken apart: X15 its offset, X11 where its owner's suffix
;; starts, X12 the owner's header, X13 the suffix's length, X16 the
;; trailer's distance; to `slow` unless it is one whose owner has a
;; trailer and a header of one word. Uses X9 and X14.
(define df-suffix-owner (subr da-assembles (int int) unit)
  (lambda (r slow)
    (begin
      (df-tagged d-x16 r d-tag-suffix-ref slow)
      (da-ubfx d-x14 r 3 d-suffix-owner-bits)
      (da-mov d-x15 r)
      (df-shr d-x15 d-suffix-offset-shift)
      (da-ld d-x9 d-st d-st-words)
      (da-e (x86-lea-ix d-x11 d-x9 d-x14 8 0))
      ;; The trailer, the last field, says how far back the header is.
      (da-ld d-x16 d-x11 -8)
      (df-tagged d-x9 d-x16 d-tag-trailer slow)
      (da-ubfx d-x16 d-x16 d-t-distance-lo 32)
      (da-mov d-x9 d-x11)
      (da-e (x86-lea d-x12 d-x16 0))
      (df-shl d-x12 3)
      (df-sub d-x9 d-x12)
      (da-ld d-x12 d-x9 -8)
      (da-mov d-x9 d-x12)
      (df-shr d-x9 d-h-large-lo)
      (df-test-imm d-x9 1)
      (da-jcc da-c-ne slow)
      (da-mov d-x13 d-x12)
      (df-shr d-x13 d-h-bytes-lo))))

;; The same, to `slow` unless its owner is a program's own bloblet or a
;; flat array whose suffix is not frozen.
(define df-suffix-writable (subr da-assembles (int int) unit)
  (lambda (r slow)
    (let ((owned (begin (df-suffix-owner r slow) (da-label))))
      (begin
        (da-ubfx d-x9 d-x12 d-h-kind-lo d-h-kind-width)
        (df-cmp-imm d-x9 d-kind-bloblet)
        (da-jcc da-c-e owned)
        (df-cmp-imm d-x9 d-kind-flat-array)
        (da-jcc da-c-ne slow)
        (da-bind owned)
        (da-mov d-x9 d-x12)
        (df-shr d-x9 d-h-suffix-frozen-lo)
        (df-test-imm d-x9 1)
        (da-jcc da-c-ne slow)))))

;; `blobref-set!` of the suffix ref in `RESULT`, a scalar of layout `code`,
;; to `v` (with `raw`, an `f64`'s bits): unit into `RESULT`.
(define df-suffix-store (subr da-assembles (int int bool int) unit)
  (lambda (code v raw slow)
    (begin
      (df-suffix-writable d-result slow)
      (da-e (x86-lea d-x9 d-x15 (df-flat-size code)))
      (df-cmp d-x9 d-x13)
      (da-jcc da-c-a slow)
      (df-add d-x11 d-x15)
      (cond ((and (= code d-flat-f64) raw) (da-sto d-x11 0 v))
            ((= code d-flat-f64)
             (begin (da-ld d-x13 v (- 0 d-tag-bloblet)) (da-sto d-x11 0 d-x13)))
            ((= code d-flat-f32)
             (begin (da-mov d-x13 v) (df-shr d-x13 32) (df-store32 d-x11 d-x13)))
            ((or (= code d-flat-i64) (= code d-flat-u64))
             (begin
               (df-test-imm v 7)
               (da-jcc da-c-ne slow)
               (da-mov d-x13 v)
               (df-sar d-x13 3)
               (da-sto d-x11 0 d-x13)))
            (else
             (begin (da-mov d-x13 v) (df-sar d-x13 3) (df-store32 d-x11 d-x13))))
      (da-imm d-result d-unit))))

;; The number of trailing zero bits of `n` (> 0).
(define df-zeros (subr da-reads (int) int)
  (lambda (n) (if (= (modulo n 2) 1) 0 (+ 1 (df-zeros (quotient n 2))))))

;; `blobref-index` of the suffix ref in `RESULT` at `i`, of layout `code`
;; (`layout::array_operand`), into `RESULT`.
(define df-blobref-index (subr da-assembles (int int int) unit)
  (lambda (code i slow)
    (let ((n (df-operand-n code)) (size (df-operand-size code)))
      (begin
        (df-test-imm i 7)
        (da-jcc da-c-ne slow)
        (df-suffix-owner d-result slow)
        (da-mov d-x9 i)
        (df-sar d-x9 3)
        (da-imm d-x17 n)
        (df-cmp d-x9 d-x17)
        (da-jcc da-c-ae slow)
        (if (and (> size 0) (= (bitwise-and size (- size 1)) 0))
            (df-shl d-x9 (df-zeros size))
            (begin (da-imm d-x17 size) (da-e (x86-imul d-x9 d-x17))))
        (da-e (x86-lea-ix d-x16 d-x15 d-x9 1 0))
        (df-cmp d-x16 d-x13)
        (da-jcc da-c-ae slow)
        (df-shl d-x9 d-suffix-offset-shift)
        (df-add d-result d-x9)))))

;; Fields 2 to the trailer's distance (X16) of the owner, the first that is
;; `l`: its index from 0 in X17; to `slow` if none is.
(define df-variant-look (subr da-assembles (int int) unit)
  (lambda (l slow)
    (let ((look (da-label)) (found (da-label)))
      (begin
        (da-imm d-x17 2)
        (da-bind look)
        (df-cmp d-x17 d-x16)
        (da-jcc da-c-a slow)
        (da-mov d-x9 d-x17)
        (df-shl d-x9 3)
        (df-neg d-x9)
        (df-add d-x9 d-x11)
        (da-ld d-x9 d-x9 0)
        (df-cmp d-x9 l)
        (da-jcc da-c-e found)
        (df-add-imm d-x17 1)
        (da-jmp look)
        (da-bind found)
        (df-sub-imm d-x17 2)))))

;; A narrow store of `w` bytes (1, 2 or 4) of `s` at `[base]`.
(define df-store-narrow (subr da-assembles (int int int) unit)
  (lambda (w base s)
    (case w
      ((1) (da-e (x86-store8-ix base -1 1 0 s)))
      ((2) (da-e (x86-store16-ix base -1 1 0 s)))
      (else (da-e (x86-store32-ix base -1 1 0 s))))))

;; `blobref-variant!` of the suffix ref in `RESULT` to label `l`, of layout
;; `code`.
(define df-flat-variant (subr da-assembles (int int int) unit)
  (lambda (code l slow)
    (let ((w (bitwise-and code 7))
          (p (arithmetic-shift code -8))
          (numeric (not (= (bitwise-and code 8) 0))))
      (begin
        (if numeric
            (begin (df-test-imm l 7) (da-jcc da-c-ne slow) (da-mov d-x17 l) (df-sar d-x17 3))
            #u)
        (df-suffix-writable d-result slow)
        (if numeric #u (df-variant-look l slow))
        (if (< w 8)
            (begin (da-mov d-x9 d-x17) (df-shr d-x9 (* 8 w)) (da-jcc da-c-ne slow))
            #u)
        (da-imm d-x9 p)
        (da-e (x86-lea-ix d-x16 d-x15 d-x9 1 0))
        (df-cmp d-x16 d-x13)
        (da-jcc da-c-ae slow)
        (df-add d-x11 d-x15)
        (df-store-narrow w d-x11 d-x17)
        (df-shl d-x9 d-suffix-offset-shift)
        (df-add d-result d-x9)))))

;; `blobref-at` of the bloblet in `RESULT` at byte `d` of its suffix, into
;; `RESULT`.
(define df-blobref-at (subr da-assembles (int int) unit)
  (lambda (d slow)
    (begin
      (df-tagged d-x16 d-result d-tag-bloblet slow)
      (da-e (x86-lea d-x11 d-result (- 0 d-tag-bloblet)))
      (da-ld d-x16 d-x11 -8)
      (df-tagged d-x9 d-x16 d-tag-trailer slow)
      (da-ubfx d-x16 d-x16 d-t-distance-lo 32)
      (da-mov d-x9 d-x16)
      (df-shl d-x9 3)
      (df-neg d-x9)
      (df-add d-x9 d-x11)
      (da-ld d-x12 d-x9 -8)
      (da-mov d-x9 d-x12)
      (df-shr d-x9 d-h-large-lo)
      (df-test-imm d-x9 1)
      (da-jcc da-c-ne slow)
      (da-mov d-x13 d-x12)
      (df-shr d-x13 d-h-bytes-lo)
      (da-imm d-x9 d-suffix-offset-limit)
      (df-cmp d-x13 d-x9)
      (da-jcc da-c-ae slow)
      (da-imm d-x9 d)
      (df-cmp d-x9 d-x13)
      (da-jcc da-c-ae slow)
      ;; The owner, the suffix's word in the heap, where it fits its bits.
      (da-e (x86-alu-rm da-sub d-x11 d-st d-st-words))
      (da-mov d-x9 d-x11)
      (df-shr d-x9 (+ 3 d-suffix-owner-bits))
      (da-jcc da-c-ne slow)
      (da-imm d-x9 (+ (arithmetic-shift d d-suffix-offset-shift) d-tag-suffix-ref))
      (da-mov d-result d-x11)
      (df-or d-result d-x9))))

;; Suffix ref `RESULT` moved `d` bytes along, into `RESULT`.
(define df-suffix-step (subr da-assembles (int int) unit)
  (lambda (d slow)
    (if (= d 0)
        (df-tagged d-x16 d-result d-tag-suffix-ref slow)
        (begin
          (df-suffix-owner d-result slow)
          (da-imm d-x9 d)
          (df-add d-x9 d-x15)
          (df-cmp d-x9 d-x13)
          (da-jcc da-c-ae slow)
          (da-imm d-x9 (arithmetic-shift d d-suffix-offset-shift))
          (df-add d-result d-x9)))))

;; A new blobref (`%fx26-suffix-fits`): to `slow` unless `size` bytes from
;; the suffix ref in `RESULT` lie in its owner's suffix.
(define df-suffix-fits (subr da-assembles (int int) unit)
  (lambda (size slow)
    (begin
      (df-suffix-owner d-result slow)
      (da-imm d-x9 size)
      (df-add d-x9 d-x15)
      (df-cmp d-x9 d-x13)
      (da-jcc da-c-a slow))))

;; `blobref-length` of the suffix ref in `RESULT`, of the layout `code`,
;; into `RESULT`.
(define df-suffix-length (subr da-assembles (int int) unit)
  (lambda (code slow)
    (let ((n (df-operand-n code)) (size (df-operand-size code)))
      (if (not (= n d-flat-to-the-end))
          (begin
            (df-tagged d-x16 d-result d-tag-suffix-ref slow)
            (da-imm d-result (* 8 n)))
          (begin
            (df-suffix-owner d-result slow)
            (da-mov d-rax d-x13)
            (df-sub d-rax d-x15)
            (da-imm d-x17 size)
            (da-imm d-rdx 0)
            (da-e (x86-div d-x17))
            (df-shl d-rax 3))))))

;; `blobref-index` of the suffix ref in REG1, at REG2, of the layout in
;; REG3, into `RESULT`: the whole element within the suffix.
(define df-suffix-index (subr da-assembles (int) unit)
  (lambda (slow)
    (let ((r1 (da-in-reg 1)) (r2 (da-in-reg 2)) (r3 (da-in-reg 3)))
      (begin
        (df-test-imm r2 7)
        (da-jcc da-c-ne slow)
        (df-suffix-owner r1 slow)
        (da-mov d-x9 r2)
        (df-sar d-x9 3)
        (da-mov d-x17 r3)
        (df-shr d-x17 (+ 3 d-array-operand-length-shift))
        (df-cmp d-x9 d-x17)
        (da-jcc da-c-ae slow)
        (da-ubfx d-x17 r3 3 d-array-operand-size-bits)
        (da-e (x86-imul d-x9 d-x17))
        (da-e (x86-lea-ix d-x16 d-x15 d-x9 1 0))
        (df-add d-x16 d-x17)
        (df-cmp d-x16 d-x13)
        (da-jcc da-c-a slow)
        (df-shl d-x9 d-suffix-offset-shift)
        (da-e (x86-lea-ix d-result r1 d-x9 1 0))))))

;; A narrow load of `w` bytes (1, 2 or 4) at `[base]` into `d`.
(define df-load-narrow (subr da-assembles (int int int) unit)
  (lambda (w d base)
    (case w
      ((1) (da-e (x86-load8-ix d base -1 1 0)))
      ((2) (da-e (x86-load16-ix d base -1 1 0)))
      (else (da-e (x86-load32-ix d base -1 1 0))))))

;; A flat sum's tag at the suffix ref in `RESULT`, into `RESULT`, of layout
;; `code`.
(define df-flat-tag (subr da-assembles (int int) unit)
  (lambda (code slow)
    (let ((w (bitwise-and code 7)))
      (begin
        (df-suffix-owner d-result slow)
        (da-e (x86-lea d-x9 d-x15 w))
        (df-cmp d-x9 d-x13)
        (da-jcc da-c-a slow)
        (da-e (x86-lea-ix d-x14 d-x11 d-x15 1 0))
        (df-load-narrow w d-x13 d-x14)
        (if (not (= (bitwise-and code 8) 0))
            (begin (df-shl d-x13 3) (da-mov d-result d-x13))
            (begin
              (df-add-imm d-x13 2)
              (df-cmp d-x13 d-x16)
              (da-jcc da-c-a slow)
              (df-shl d-x13 3)
              (df-neg d-x13)
              (df-add d-x13 d-x11)
              (da-ld d-result d-x13 0)))))))

;; `blobref-get` of the suffix ref in `RESULT`, a scalar of layout `code`,
;; into `RESULT`.
(define df-suffix-get (subr da-assembles (int bool int) unit)
  (lambda (code raw slow)
    (begin
      (df-suffix-owner d-result slow)
      (da-e (x86-lea d-x9 d-x15 (df-flat-size code)))
      (df-cmp d-x9 d-x13)
      (da-jcc da-c-a slow)
      (df-add d-x11 d-x15)
      (cond ((and (= code d-flat-f64) raw) (da-ld d-result d-x11 0))
            ((= code d-flat-f64) (begin (da-ld d-x9 d-x11 0) (dr-box-bits slow)))
            ((= code d-flat-f32)
             (begin
               (da-e (x86-load32-ix d-x13 d-x11 -1 1 0))
               (df-shl d-x13 32)
               (da-e (x86-lea d-result d-x13 df-f32-tag))))
            ((= code d-flat-i32)
             (begin
               (da-e (x86-load32s-ix d-x13 d-x11 -1 1 0))
               (df-shl d-x13 3)
               (da-mov d-result d-x13)))
            ((= code d-flat-u32)
             (begin
               (da-e (x86-load32-ix d-x13 d-x11 -1 1 0))
               (df-shl d-x13 3)
               (da-mov d-result d-x13)))
            ((= code d-flat-i64)
             (begin
               (da-ld d-x13 d-x11 0)
               (da-mov d-x14 d-x13)
               (df-shl d-x14 3)
               (da-mov d-x15 d-x14)
               (df-sar d-x15 3)
               (df-cmp d-x15 d-x13)
               (da-jcc da-c-ne slow)
               (da-mov d-result d-x14)))
            (else
             (begin
               (da-ld d-x13 d-x11 0)
               (da-mov d-x15 d-x13)
               (df-shr d-x15 60)
               (da-jcc da-c-ne slow)
               (df-shl d-x13 3)
               (da-mov d-result d-x13)))))))

;; Whether the fixnum layout code in `c` is a 64-bit one's, to `wide`.
(define df-wide-layout (subr da-assembles (int int) unit)
  (lambda (c wide)
    (begin
      (df-cmp-imm c (* d-flat-i64 8))
      (da-jcc da-c-e wide)
      (df-cmp-imm c (* d-flat-u64 8))
      (da-jcc da-c-e wide)
      (df-cmp-imm c (* d-flat-f64 8))
      (da-jcc da-c-e wide))))

;; `v`, a value, stored by the layout in `c` (a fixnum) at `[base +
;; index * scale]`, the 64-bit layouts' scale `wide-scale`, the narrow
;; ones' `narrow-scale` (index -1 for none), to `stored`; a 64-bit
;; integer's that is no fixnum, to `slow`. `flat_set`'s and `suffix_set`'s
;; store, the same in both.
(define df-store-by (subr da-assembles (int int int int int int int int) unit)
  (lambda (c v base index wide-scale narrow-scale slow stored)
    (let ((not-f64 (da-label)) (not-f32 (da-label)) (wide (da-label)))
      (begin
        (df-is c d-flat-f64 not-f64)
        (da-ld d-x13 v (- 0 d-tag-bloblet))
        (da-e (x86-store-ix base index wide-scale 0 d-x13))
        (da-jmp stored)
        (da-bind not-f64)
        (df-is c d-flat-f32 not-f32)
        (da-mov d-x13 v)
        (df-shr d-x13 32)
        (da-e (x86-store32-ix base index narrow-scale 0 d-x13))
        (da-jmp stored)
        (da-bind not-f32)
        (df-cmp-imm c (* d-flat-i64 8))
        (da-jcc da-c-e wide)
        (df-cmp-imm c (* d-flat-u64 8))
        (da-jcc da-c-e wide)
        (da-mov d-x13 v)
        (df-sar d-x13 3)
        (da-e (x86-store32-ix base index narrow-scale 0 d-x13))
        (da-jmp stored)
        (da-bind wide)
        (df-test-imm v 7)
        (da-jcc da-c-ne slow)
        (da-mov d-x13 v)
        (df-sar d-x13 3)
        (da-e (x86-store-ix base index wide-scale 0 d-x13))))))

;; `blobref-set!` of the suffix ref in REG1, a scalar of the layout the
;; fixnum in REG2 says, to REG3.
(define df-suffix-set (subr da-assembles (int int) unit)
  (lambda (slow done)
    (let ((r1 (da-in-reg 1)) (c (da-in-reg 2)) (v (da-in-reg 3)))
      (begin
        (df-suffix-writable r1 slow)
        ;; The width: 8 for the 64-bit layouts, else 4.
        (let ((eight (da-label)) (sized (da-label)))
          (begin
            (da-imm d-x9 4)
            (df-wide-layout c eight)
            (da-jmp sized)
            (da-bind eight)
            (da-imm d-x9 8)
            (da-bind sized)))
        (df-add d-x9 d-x15)
        (df-cmp d-x9 d-x13)
        (da-jcc da-c-a slow)
        (df-add d-x11 d-x15)
        (let ((stored (da-label)))
          (begin
            (df-store-by c v d-x11 -1 1 1 slow stored)
            (da-bind stored)
            (da-imm d-result d-unit)
            (da-jmp done)))))))

;; `bytevector-u8-set!` of the bytevector in REG1 at REG2 to the `u8` in
;; REG3: unit into `RESULT`, and to `done`.
(define df-bytes-set (subr da-assembles (int int) unit)
  (lambda (slow done)
    (let ((bv (da-in-reg 1)) (i (da-in-reg 2)) (v (da-in-reg 3)))
      (begin
        (df-test-imm i 7)
        (da-jcc da-c-ne slow)
        (da-mov d-x15 i)
        (df-sar d-x15 3)
        (da-ld d-x14 bv -4)
        (df-cmp d-x15 d-x14)
        (da-jcc da-c-ae slow)
        (da-mov d-x13 v)
        (df-shr d-x13 3)
        (da-e (x86-store8-ix bv d-x15 1 4 d-x13))
        (da-imm d-result d-unit)
        (da-jmp done)))))

;; `flatarray-set!` of the flat array in REG1 at REG2 to REG3; `raw`: the
;; value is an `f64`'s bits.
(define df-flat-set (subr da-assembles (int int bool) unit)
  (lambda (slow done raw)
    (let* ((r1 (da-in-reg 1)) (r2 (da-in-reg 2)) (v (da-in-reg 3)) (stored (da-label)))
      (begin
        (df-flat-element r1 r2 slow)
        (if raw
            (begin
              (da-e (x86-store-ix d-x15 d-x14 8 0 v))
              (da-imm d-result d-unit)
              (da-jmp done))
            (begin
              (df-store-by d-x16 v d-x15 d-x14 8 4 slow stored)
              (da-bind stored)
              (da-imm d-result d-unit)
              (da-jmp done)))))))

;;; ------------------------------------------------------------ shapes

;; The kinds a shape predicate takes a bloblet of, in the order tested;
;; none for one this does not do so.
(define df-shape-kinds (subr da-assembles (string) da-bytes)
  (lambda (name)
    (case name
      (("exact-integer?") (cons d-kind-bignum nil))
      (("symbol?") (cons d-kind-symbol nil))
      (("string?") (cons d-kind-string nil))
      (("%fx26-array?") (cons d-kind-bloblet nil))
      (("%fx26-box?") (cons d-kind-box nil))
      (("%fx26-one?") (cons d-kind-sum nil))
      (("%fx26-tup?") (cons d-kind-product nil))
      (("%fx26-procedure?")
       ;; cons-chain: in `@k`, the assembler's region, which `list` would not be
       (cons d-kind-closure
             (cons d-kind-primitive
                   (cons d-kind-continuation
                         (cons d-kind-cellular-closure
                               (cons d-kind-native-closure
                                     (cons d-kind-cellular-continuation nil)))))))
      (else nil))))

;; To `yes` if the kind in X13 is one of `ks`.
(define df-kinds (subr da-assembles (da-bytes int) unit)
  (lambda (ks yes)
    (if (null? ks)
        #u
        (begin (df-cmp-imm d-x13 (car ks)) (da-jcc da-c-e yes) (df-kinds (cdr ks) yes)))))

;; The kind of the bloblet in `RESULT`, in X13, or to `no` if it is no
;; bloblet, or `slow` if its header is not found or is large. Its header
;; tested for a bloblet's kinds `ks`, `#t` or `#f` into `RESULT` after.
(define df-shape-kind (subr da-assembles (string da-bytes int) unit)
  (lambda (name ks slow)
    (let ((x d-result) (yes (da-label)) (no (da-label)) (have (da-label)) (end (da-label)))
      (begin
        (if (string=? name "exact-integer?")
            (begin (df-test-imm x 7) (da-jcc da-c-e yes))
            #u)
        (df-tagged d-x13 x d-tag-bloblet no)
        (da-ld d-x16 x (da-field-off 1))
        (da-mov d-x13 d-x16)
        (df-and-imm d-x13 7)
        (df-cmp-imm d-x13 d-tag-header)
        (da-jcc da-c-e have)
        (df-cmp-imm d-x13 d-tag-trailer)
        (da-jcc da-c-ne slow)
        (df-sub-imm d-x16 d-tag-trailer)
        (da-mov d-x14 x)
        (df-sub d-x14 d-x16)
        (da-ld d-x16 d-x14 (da-field-off 1))
        (da-bind have)
        (da-mov d-x13 d-x16)
        (df-shr d-x13 d-h-kind-lo)
        (df-and-imm d-x13 (- (arithmetic-shift 1 d-h-kind-width) 1))
        (df-cmp-imm d-x13 d-kind-extension)
        (da-jcc da-c-e slow)
        (df-kinds ks yes)
        (da-bind no)
        (da-imm d-result d-false)
        (da-jmp end)
        (da-bind yes)
        (da-imm d-result d-true)
        (da-bind end)))))

;; A shape predicate of `RESULT`, in line: whether it is one this does.
(define df-shape-fast (subr da-assembles (string int) bool)
  (lambda (name slow)
    (let ((x d-result))
      (cond
        ((string=? name "null?") (begin (da-cmp-k x d-null) (da-flag da-c-e d-x15) #t))
        ((string=? name "pair?")
         (begin (da-mov d-x13 x) (df-and-imm d-x13 7) (df-cmp-imm d-x13 d-tag-pair)
                (da-flag da-c-e d-x15) #t))
        ((or (string=? name "char?") (string=? name "%fx26-f32?"))
         (begin
           (da-e (x86-movzx8 d-x13 x))
           (df-cmp-imm d-x13 (bitwise-and (if (string=? name "char?") d-char0 d-f32-0) 255))
           (da-flag da-c-e d-x15)
           #t))
        ((string=? name "boolean?")
         (begin
           (da-imm d-x15 d-false)
           (da-imm d-x16 d-true)
           (da-mov d-x13 d-x15)
           (df-cmp x d-x15)
           (da-e (x86-cmov da-c-e d-x13 d-x16))
           (df-cmp x d-x16)
           (da-e (x86-cmov da-c-e d-x13 d-x16))
           (da-mov d-result d-x13)
           #t))
        (else
         (let ((ks (df-shape-kinds name)))
           (if (null? ks) #f (begin (df-shape-kind name ks slow) #t))))))))
;;; ------------------------------------------------------------ allocation
;;; `procedure_x64`'s allocations in line: `rcons`, `new`, `make-array`,
;;; `rnew` and `rmake-array`, as its `region_slot` to `array_at`.

;; Room for `n` words from the heap's free space, short of the collection's
;; threshold: at X11, the free space bumped; else `slow` (`bump`).
(define df-bump (subr da-assembles (int int) unit)
  (lambda (n slow)
    (begin
      (da-ld d-x13 d-st d-st-top)
      (da-ld d-x14 d-x13 0)
      (da-e (x86-lea d-x16 d-x14 n))
      (da-e (x86-alu-rm da-cmp d-x16 d-st d-st-alloc-limit))
      (da-jcc da-c-a slow)
      (da-ld d-x9 d-st d-st-words)
      (da-e (x86-lea-ix d-x11 d-x9 d-x14 8 0))
      (da-sto d-x13 0 d-x16))))
;; The region in REG1's slot in the heap's table, at X13, its fill in X14;
;; else `slow`, as for `#f`, the heap's.
(define df-region-slot (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (da-e (x86-test-imm d-rdi 7))
      (da-jcc da-c-ne slow)
      (df-cmp-imm d-rdi (* 8 d-region-slots))
      (da-jcc da-c-ae slow)
      (da-ld d-x13 d-st d-st-region-table)
      (da-e (x86-lea-ix d-x13 d-x13 d-rdi 2 0))
      (da-ld d-x14 d-x13 0))))
;; Room in that region's chunk to the fill in X16: at X11, the fill bumped;
;; else `slow`.
(define df-region-room (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (da-e (x86-alu-rm da-cmp d-x16 d-x13 8))
      (da-jcc da-c-a slow)
      (da-ld d-x9 d-st d-st-words)
      (da-e (x86-lea-ix d-x11 d-x9 d-x14 8 0))
      (da-sto d-x13 0 d-x16))))
;; A box of `v` at X11, its room had.
(define df-box-at (subr da-assembles (int int) unit)
  (lambda (v done)
    (begin
      (da-imm d-x15 (da-header d-kind-box 2 0))
      (da-sto d-x11 0 d-x15)
      (da-sto d-x11 8 v)
      (da-imm d-x15 (da-trailer 2))
      (da-sto d-x11 16 d-x15)
      (da-e (x86-lea d-result d-x11 (+ 24 d-tag-bloblet)))
      (da-jmp done))))
;; An array of `8n` (REG2) at X11, its room had, each field REG3.
(define df-array-at (subr da-assembles (int) unit)
  (lambda (done)
    (begin
      (da-mov d-x15 d-rsi)
      (df-shl d-x15 (- d-h-fields-lo 3))
      (da-imm d-x17 (da-header d-kind-bloblet 1 0))
      (df-add d-x15 d-x17)
      (da-sto d-x11 0 d-x15)
      (da-e (x86-lea d-x15 d-rsi (+ 8 d-tag-trailer)))
      (da-e (x86-store-ix d-x11 d-rsi 1 8 d-x15))
      (let* ((fill (da-label)) (filled (da-label)))
        (begin
          (da-mov d-x9 d-rsi)
          (da-bind fill)
          (da-e (x86-test d-x9 d-x9))
          (da-jcc da-c-e filled)
          (da-e (x86-store-ix d-x11 d-x9 1 0 d-r8))
          (df-sub-imm d-x9 8)
          (da-jmp fill)
          (da-bind filled)))
      (da-e (x86-lea-ix d-result d-x11 d-rsi 1 (+ 16 d-tag-bloblet)))
      (da-jmp done))))
;; `8n` in REG2 a length to make in line: else `slow`.
(define df-array-words (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (da-e (x86-test-imm d-rsi 7))
      (da-jcc da-c-ne slow)
      (df-cmp-imm d-rsi (* 8 d-array-inline))
      (da-jcc da-c-a slow))))
;; The words of the array of `8n` in REG2, `n + 2`, past the fill in X14,
;; in X16.
(define df-array-end (subr da-assembles () unit)
  (lambda ()
    (begin
      (da-mov d-x15 d-rsi)
      (df-shr d-x15 3)
      (da-e (x86-lea-ix d-x16 d-x14 d-x15 1 2)))))
;; The primitive `pname` of `n` arguments made in line, if it is one of these.
(define df-alloc (subr da-assembles (string int int int) unit)
  (lambda (pname n slow done)
    (cond ((and (string=? pname "%region-cons") (= n 3))
           (begin
             (df-region-slot slow)
             (da-e (x86-lea d-x16 d-x14 2))
             (df-region-room slow)
             (da-sto d-x11 0 d-rsi)
             (da-sto d-x11 8 d-r8)
             (da-e (x86-lea d-result d-x11 d-tag-pair))
             (da-jmp done)))
          ((and (string=? pname "%make-box") (= n 1))
           (begin (df-bump 3 slow) (df-box-at d-rdi done)))
          ((and (string=? pname "%make-bloblet-filled") (= n 3))
           (begin
             (da-e (x86-test d-rdi d-rdi))
             (da-jcc da-c-ne slow)
             (df-array-words slow)
             (da-ld d-x13 d-st d-st-top)
             (da-ld d-x14 d-x13 0)
             (df-array-end)
             (da-e (x86-alu-rm da-cmp d-x16 d-st d-st-alloc-limit))
             (da-jcc da-c-a slow)
             (da-ld d-x9 d-st d-st-words)
             (da-e (x86-lea-ix d-x11 d-x9 d-x14 8 0))
             (da-sto d-x13 0 d-x16)
             (df-array-at done)))
          ((and (string=? pname "%region-new") (= n 2))
           (begin
             (df-region-slot slow)
             (da-e (x86-lea d-x16 d-x14 3))
             (df-region-room slow)
             (df-box-at d-rsi done)))
          ((and (string=? pname "%region-make-array") (= n 3))
           (begin
             (df-array-words slow)
             (df-region-slot slow)
             (df-array-end)
             (df-region-room slow)
             (df-array-at done)))
          (else #u))))
)))
