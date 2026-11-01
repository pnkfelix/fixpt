;;; Flat arrays, suffix refs, bytevectors and shapes in line, for the native
;;; convention's compiler to arm64 written in FX-26: `direct.rs`'s
;;; `flat_count` to `flat_set`, `box_bits` and `shape_fast`, step for step
;;; and instruction for instruction, each `adf-` and its Rust name. The Rust
;;; pieces are these' oracle (`tests/native_direct_arm64_flat.rs`).
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

;;; ------------------------------------------------------------ shorthands

;; `cmp r, #imm` and `b.c l`.
(define adf-cmp-imm (subr da-assembles (int int) unit)
  (lambda (r imm) (ada-e (arm-cmp-imm r imm))))
(define adf-cmp (subr da-assembles (int int) unit) (lambda (n m) (ada-e (arm-cmp n m))))
;; Register `r`'s tag `tag`, else to `slow` (uses `t`).
(define adf-tagged (subr da-assembles (int int int int) unit)
  (lambda (t r tag slow)
    (begin (ada-e (arm-and-low t r 3)) (adf-cmp-imm t tag) (ada-bc ada-c-ne slow))))
;; To `slow` unless the bit at `lo` of `r` is clear (uses X9).
(define adf-clear (subr da-assembles (int int int) unit)
  (lambda (r lo slow)
    (begin (ada-e (arm-ubfx d-x9 r lo 1)) (adf-cmp-imm d-x9 0) (ada-bc ada-c-ne slow))))
;; A flat layout's element size in bytes (`flat_size`).
(define adf-flat-size (subr pure (int) int)
  (lambda (code)
    (if (or (= code d-flat-i32) (or (= code d-flat-u32) (= code d-flat-f32))) 4 8)))
;; `layout::array_operand_parts`: a flat array's length, and its element's
;; size.
(define adf-operand-n (subr pure (int) int)
  (lambda (code) (arithmetic-shift code (- 0 d-array-operand-length-shift))))
(define adf-operand-size (subr pure (int) int)
  (lambda (code)
    (bitwise-and code (- (arithmetic-shift 1 d-array-operand-size-bits) 1))))
;; An `f32`'s immediate tag, its low byte.
(define adf-f32-tag int (bitwise-and d-f32-0 255))
;; The 8-byte layouts, as bits of a word: 2 plus that bit is the shift.
(define adf-wide int
  (+ (arithmetic-shift 1 d-flat-i64)
     (+ (arithmetic-shift 1 d-flat-u64) (arithmetic-shift 1 d-flat-f64))))
;; To `not` unless the layout (a fixnum) in `r` is `code`'s.
(define adf-is (subr da-assembles (int int int) unit)
  (lambda (r code not) (begin (adf-cmp-imm r (* code 8)) (ada-bc ada-c-ne not))))

;;; ------------------------------------------------------------ flat arrays

;; `out` := how many elements the flat array in `arr` has (untagged). Uses
;; X11 and X16.
(define adf-flat-count (subr da-assembles (int int) unit)
  (lambda (arr out)
    (begin
      (ada-e (arm-ldur out arr -28))
      (ada-e (arm-lsr-imm out out 32))
      (ada-e (arm-ldur d-x16 arr (ada-field-off 2)))
      (ada-e (arm-lsr-imm d-x16 d-x16 3))
      (ada-e (arm-movz d-x11 adf-wide 0))
      (ada-e (arm-lsrv d-x11 d-x11 d-x16))
      (ada-e (arm-and-low d-x11 d-x11 1))
      (ada-e (arm-add-imm d-x11 d-x11 2))
      (ada-e (arm-lsrv out out d-x11)))))

;; Where a flat array's elements are, and element `y`: X14 the index, X15
;; the suffix, X16 the layout, as a fixnum; to `slow` unless the index is
;; a fixnum in range.
(define adf-flat-element (subr da-assembles (int int int) unit)
  (lambda (arr y slow)
    (begin
      (ada-e (arm-tst-low y 3))
      (ada-bc ada-c-ne slow)
      (ada-e (arm-asr-imm d-x14 y 3))
      (adf-flat-count arr d-x13)
      (adf-cmp d-x14 d-x13)
      (ada-bc ada-c-hs slow)
      (ada-e (arm-ldur d-x16 arr (ada-field-off 2)))
      (ada-e (arm-sub-imm d-x15 arr d-tag-bloblet)))))

;; An `f64` boxed from the free space into `RESULT`, its bits in X9; to
;; `slow` when there is no room. Uses X11 and X13 to X17.
(define adf-box-bits (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (ada-ld d-x13 d-st d-st-top)
      (ada-ld d-x14 d-x13 0)
      (ada-ld d-x15 d-st d-st-alloc-limit)
      (ada-e (arm-add-imm d-x16 d-x14 2))
      (adf-cmp d-x16 d-x15)
      (ada-bc ada-c-hi slow)
      (ada-ld d-x17 d-st d-st-words)
      (ada-e (arm-add-lsl d-x11 d-x17 d-x14 3))
      (ada-imm d-x17 (ada-header d-flonum 0 8))
      (ada-sto d-x17 d-x11 0)
      (ada-sto d-x9 d-x11 8)
      (ada-sto d-x16 d-x13 0)
      (ada-e (arm-add-imm d-result d-x11 (+ 8 d-tag-bloblet))))))

;; An `i64` (or `u64`, by the layout in X16) in X13 into `RESULT` as a
;; fixnum, to `end`; else to `slow`.
(define adf-flat-wide (subr da-assembles (int int) unit)
  (lambda (slow end)
    (let ((unsigned (ada-label)))
      (begin
        (adf-cmp-imm d-x16 (* d-flat-u64 8))
        (ada-bc ada-c-eq unsigned)
        (ada-e (arm-lsl-imm d-x14 d-x13 3))
        (ada-e (arm-asr-imm d-x15 d-x14 3))
        (adf-cmp d-x15 d-x13)
        (ada-bc ada-c-ne slow)
        (ada-mov d-result d-x14)
        (ada-b end)
        (ada-bind unsigned)
        (ada-e (arm-lsr-imm d-x15 d-x13 60))
        (adf-cmp-imm d-x15 0)
        (ada-bc ada-c-ne slow)
        (ada-e (arm-lsl-imm d-result d-x13 3))))))

;; `flatarray-ref` of the flat array in `RESULT` at `y`, into `RESULT`.
(define adf-flat-ref (subr da-assembles (int int) unit)
  (lambda (y slow)
    (let ((end (ada-label)))
      (begin
        (adf-flat-element d-result y slow)
        (let* ((not-f64 (ada-label)) (not-f32 (ada-label)) (not-i32 (ada-label))
               (not-u32 (ada-label)))
          (begin
            (adf-is d-x16 d-flat-f64 not-f64)
            (ada-e (arm-ldr-x8 d-x9 d-x15 d-x14))
            (adf-box-bits slow)
            (ada-b end)
            (ada-bind not-f64)
            (adf-is d-x16 d-flat-f32 not-f32)
            (ada-e (arm-ldr-w4 d-x13 d-x15 d-x14))
            (ada-e (arm-lsl-imm d-x13 d-x13 32))
            (ada-e (arm-add-imm d-result d-x13 adf-f32-tag))
            (ada-b end)
            (ada-bind not-f32)
            (adf-is d-x16 d-flat-i32 not-i32)
            (ada-e (arm-ldrsw-4 d-x13 d-x15 d-x14))
            (ada-e (arm-lsl-imm d-result d-x13 3))
            (ada-b end)
            (ada-bind not-i32)
            (adf-is d-x16 d-flat-u32 not-u32)
            (ada-e (arm-ldr-w4 d-x13 d-x15 d-x14))
            (ada-e (arm-lsl-imm d-result d-x13 3))
            (ada-b end)
            ;; `i64` or `u64`: a fixnum where it fits one.
            (ada-bind not-u32)
            (ada-e (arm-ldr-x8 d-x13 d-x15 d-x14))
            (adf-flat-wide slow end)
            (ada-bind end)))))))

;;; ------------------------------------------------------------ suffix refs

;; The owner's header before the fields the trailer's distance (X16) back
;; from X11: in X12, its suffix's length in X13; to `slow` if it is large.
;; Uses X9.
(define adf-owner-header (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (ada-e (arm-ubfx d-x16 d-x16 d-t-distance-lo 32))
      (ada-e (arm-lsl-imm d-x9 d-x16 3))
      (ada-e (arm-sub d-x9 d-x11 d-x9))
      (ada-e (arm-ldur d-x12 d-x9 -8))
      (adf-clear d-x12 d-h-large-lo slow)
      (ada-e (arm-lsr-imm d-x13 d-x12 d-h-bytes-lo)))))

;; Suffix ref `r` taken apart: X15 its offset, X11 where its owner's suffix
;; starts, X12 the owner's header, X13 the suffix's length, X16 the
;; trailer's distance; to `slow` unless it is one whose owner has a
;; trailer and a header of one word. Uses X9 and X14.
(define adf-suffix-owner (subr da-assembles (int int) unit)
  (lambda (r slow)
    (begin
      (adf-tagged d-x16 r d-tag-suffix-ref slow)
      (ada-e (arm-ubfx d-x14 r 3 d-suffix-owner-bits))
      (ada-e (arm-lsr-imm d-x15 r d-suffix-offset-shift))
      (ada-ld d-x9 d-st d-st-words)
      (ada-e (arm-add-lsl d-x11 d-x9 d-x14 3))
      ;; The trailer, the last field, says how far back the header is.
      (ada-e (arm-ldur d-x16 d-x11 -8))
      (adf-tagged d-x9 d-x16 d-tag-trailer slow)
      (adf-owner-header slow))))

;; The same, to `slow` unless its owner is a program's own bloblet or a
;; flat array whose suffix is not frozen.
(define adf-suffix-writable (subr da-assembles (int int) unit)
  (lambda (r slow)
    (let ((owned (begin (adf-suffix-owner r slow) (ada-label))))
      (begin
        (ada-e (arm-ubfx d-x9 d-x12 d-h-kind-lo d-h-kind-width))
        (adf-cmp-imm d-x9 d-kind-bloblet)
        (ada-bc ada-c-eq owned)
        (adf-cmp-imm d-x9 d-kind-flat-array)
        (ada-bc ada-c-ne slow)
        (ada-bind owned)
        (adf-clear d-x12 d-h-suffix-frozen-lo slow)))))

;; `X9 := X15 + n`, to `slow` past the suffix's length (`hi`, or `hs`).
(define adf-within (subr da-assembles (int int int) unit)
  (lambda (n c slow)
    (begin (ada-e (arm-add-imm d-x9 d-x15 n)) (adf-cmp d-x9 d-x13) (ada-bc c slow))))

;; `blobref-set!` of the suffix ref in `RESULT`, a scalar of layout `code`,
;; to `v` (with `raw`, an `f64`'s bits): unit into `RESULT`.
(define adf-suffix-store (subr da-assembles (int int bool int) unit)
  (lambda (code v raw slow)
    (begin
      (adf-suffix-writable d-result slow)
      (adf-within (adf-flat-size code) ada-c-hi slow)
      (ada-e (arm-add d-x11 d-x11 d-x15))
      (cond ((and (= code d-flat-f64) raw) (ada-e (arm-stur v d-x11 0)))
            ((= code d-flat-f64)
             (begin (ada-e (arm-ldur d-x13 v (- 0 d-tag-bloblet)))
                    (ada-e (arm-stur d-x13 d-x11 0))))
            ((= code d-flat-f32)
             (begin (ada-e (arm-lsr-imm d-x13 v 32)) (ada-e (arm-stur-w d-x13 d-x11 0))))
            ((or (= code d-flat-i64) (= code d-flat-u64))
             (begin
               (ada-e (arm-tst-low v 3))
               (ada-bc ada-c-ne slow)
               (ada-e (arm-asr-imm d-x13 v 3))
               (ada-e (arm-stur d-x13 d-x11 0))))
            (else
             (begin (ada-e (arm-asr-imm d-x13 v 3)) (ada-e (arm-stur-w d-x13 d-x11 0)))))
      (ada-imm d-result d-unit))))

;; The number of trailing zero bits of `n` (> 0).
(define adf-zeros (subr da-reads (int) int)
  (lambda (n) (if (= (modulo n 2) 1) 0 (+ 1 (adf-zeros (quotient n 2))))))

;; `blobref-index` of the suffix ref in `RESULT` at `i`, of layout `code`
;; (`layout::array_operand`), into `RESULT`.
(define adf-blobref-index (subr da-assembles (int int int) unit)
  (lambda (code i slow)
    (let ((n (adf-operand-n code)) (size (adf-operand-size code)))
      (begin
        (ada-e (arm-tst-low i 3))
        (ada-bc ada-c-ne slow)
        (adf-suffix-owner d-result slow)
        (ada-e (arm-asr-imm d-x9 i 3))
        (ada-imm d-x17 n)
        (adf-cmp d-x9 d-x17)
        (ada-bc ada-c-hs slow)
        (if (and (> size 0) (= (bitwise-and size (- size 1)) 0))
            (ada-e (arm-lsl-imm d-x9 d-x9 (adf-zeros size)))
            (begin (ada-imm d-x17 size) (ada-e (arm-mul d-x9 d-x9 d-x17))))
        (ada-e (arm-add d-x16 d-x15 d-x9))
        (adf-cmp d-x16 d-x13)
        (ada-bc ada-c-hs slow)
        (ada-e (arm-lsl-imm d-x9 d-x9 d-suffix-offset-shift))
        (ada-e (arm-add d-result d-result d-x9))))))

;; Fields 2 to the trailer's distance (X16) of the owner, the first that is
;; `l`: its index from 0 in X17; to `slow` if none is.
(define adf-variant-look (subr da-assembles (int int) unit)
  (lambda (l slow)
    (let* ((look (ada-label)) (found (ada-label)))
      (begin
        (ada-e (arm-movz d-x17 2 0))
        (ada-bind look)
        (adf-cmp d-x17 d-x16)
        (ada-bc ada-c-hi slow)
        (ada-e (arm-lsl-imm d-x9 d-x17 3))
        (ada-e (arm-sub d-x9 d-x11 d-x9))
        (ada-e (arm-ldur d-x9 d-x9 0))
        (adf-cmp d-x9 l)
        (ada-bc ada-c-eq found)
        (ada-e (arm-add-imm d-x17 d-x17 1))
        (ada-b look)
        (ada-bind found)
        (ada-e (arm-sub-imm d-x17 d-x17 2))))))

;; `blobref-variant!` of the suffix ref in `RESULT` to label `l`, of layout
;; `code`.
(define adf-flat-variant (subr da-assembles (int int int) unit)
  (lambda (code l slow)
    (let ((w (bitwise-and code 7))
          (p (arithmetic-shift code -8))
          (numeric (not (= (bitwise-and code 8) 0))))
      (begin
        (if numeric
            (begin (ada-e (arm-tst-low l 3)) (ada-bc ada-c-ne slow)
                   (ada-e (arm-asr-imm d-x17 l 3)))
            #u)
        (adf-suffix-writable d-result slow)
        (if numeric #u (adf-variant-look l slow))
        (if (< w 8)
            (begin (ada-e (arm-lsr-imm d-x9 d-x17 (* 8 w))) (adf-cmp-imm d-x9 0)
                   (ada-bc ada-c-ne slow))
            #u)
        (ada-imm d-x9 p)
        (ada-e (arm-add d-x16 d-x15 d-x9))
        (adf-cmp d-x16 d-x13)
        (ada-bc ada-c-hs slow)
        (ada-e (arm-add d-x11 d-x11 d-x15))
        (ada-e (case w
                 ((1) (arm-sturb d-x17 d-x11 0))
                 ((2) (arm-sturh d-x17 d-x11 0))
                 (else (arm-stur-w d-x17 d-x11 0))))
        (ada-e (arm-lsl-imm d-x9 d-x9 d-suffix-offset-shift))
        (ada-e (arm-add d-result d-result d-x9))))))

;; `blobref-at` of the bloblet in `RESULT` at byte `d` of its suffix, into
;; `RESULT`.
(define adf-blobref-at (subr da-assembles (int int) unit)
  (lambda (d slow)
    (begin
      (adf-tagged d-x16 d-result d-tag-bloblet slow)
      (ada-e (arm-sub-imm d-x11 d-result d-tag-bloblet))
      (ada-e (arm-ldur d-x16 d-x11 -8))
      (adf-tagged d-x9 d-x16 d-tag-trailer slow)
      (adf-owner-header slow)
      (ada-imm d-x9 d-suffix-offset-limit)
      (adf-cmp d-x13 d-x9)
      (ada-bc ada-c-hs slow)
      (ada-imm d-x9 d)
      (adf-cmp d-x9 d-x13)
      (ada-bc ada-c-hs slow)
      ;; The owner, the suffix's word in the heap, where it fits its bits.
      (ada-ld d-x9 d-st d-st-words)
      (ada-e (arm-sub d-x11 d-x11 d-x9))
      (ada-e (arm-lsr-imm d-x9 d-x11 (+ 3 d-suffix-owner-bits)))
      (adf-cmp-imm d-x9 0)
      (ada-bc ada-c-ne slow)
      (ada-imm d-x9
               (bitwise-ior (ada-bits (arithmetic-shift (ada-bits d) d-suffix-offset-shift))
                            d-tag-suffix-ref))
      (ada-e (arm-orr d-result d-x11 d-x9)))))

;; Suffix ref `RESULT` moved `d` bytes along, into `RESULT`.
(define adf-suffix-step (subr da-assembles (int int) unit)
  (lambda (d slow)
    (if (= d 0)
        (adf-tagged d-x16 d-result d-tag-suffix-ref slow)
        (begin
          (adf-suffix-owner d-result slow)
          (ada-imm d-x9 d)
          (ada-e (arm-add d-x9 d-x15 d-x9))
          (adf-cmp d-x9 d-x13)
          (ada-bc ada-c-hs slow)
          (ada-imm d-x9 (arithmetic-shift (ada-bits d) d-suffix-offset-shift))
          (ada-e (arm-add d-result d-result d-x9))))))

;; A new blobref (`%fx26-suffix-fits`): to `slow` unless `size` bytes from
;; the suffix ref in `RESULT` lie in its owner's suffix.
(define adf-suffix-fits (subr da-assembles (int int) unit)
  (lambda (size slow)
    (begin
      (adf-suffix-owner d-result slow)
      (ada-imm d-x9 size)
      (ada-e (arm-add d-x9 d-x15 d-x9))
      (adf-cmp d-x9 d-x13)
      (ada-bc ada-c-hi slow))))

;; `blobref-length` of the suffix ref in `RESULT`, of the layout `code`,
;; into `RESULT`.
(define adf-suffix-length (subr da-assembles (int int) unit)
  (lambda (code slow)
    (let ((n (adf-operand-n code)) (size (adf-operand-size code)))
      (if (not (= n d-flat-to-the-end))
          (begin
            (adf-tagged d-x16 d-result d-tag-suffix-ref slow)
            (ada-imm d-result (ada-fixnum n)))
          (begin
            (adf-suffix-owner d-result slow)
            (ada-e (arm-sub d-x9 d-x13 d-x15))
            (ada-imm d-x17 size)
            (ada-e (arm-udiv d-x9 d-x9 d-x17))
            (ada-e (arm-lsl-imm d-result d-x9 3)))))))

;; `blobref-index` of the suffix ref in X1, at X2, of the layout in X3,
;; into `RESULT`: the whole element within the suffix.
(define adf-suffix-index (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (ada-e (arm-tst-low 2 3))
      (ada-bc ada-c-ne slow)
      (adf-suffix-owner 1 slow)
      (ada-e (arm-asr-imm d-x9 2 3))
      ;; The operand a fixnum: its length past the tag and the size.
      (ada-e (arm-lsr-imm d-x17 3 (+ 3 d-array-operand-length-shift)))
      (adf-cmp d-x9 d-x17)
      (ada-bc ada-c-hs slow)
      (ada-e (arm-ubfx d-x17 3 3 d-array-operand-size-bits))
      (ada-e (arm-mul d-x9 d-x9 d-x17))
      (ada-e (arm-add d-x16 d-x15 d-x9))
      (ada-e (arm-add d-x16 d-x16 d-x17))
      (adf-cmp d-x16 d-x13)
      (ada-bc ada-c-hi slow)
      (ada-e (arm-lsl-imm d-x9 d-x9 d-suffix-offset-shift))
      (ada-e (arm-add d-result 1 d-x9)))))

;; A flat sum's tag at the suffix ref in `RESULT`, into `RESULT`, of layout
;; `code`.
(define adf-flat-tag (subr da-assembles (int int) unit)
  (lambda (code slow)
    (let ((w (bitwise-and code 7)))
      (begin
        (adf-suffix-owner d-result slow)
        (adf-within w ada-c-hi slow)
        (ada-e (arm-add d-x14 d-x11 d-x15))
        (ada-e (case w
                 ((1) (arm-ldurb d-x13 d-x14 0))
                 ((2) (arm-ldurh d-x13 d-x14 0))
                 (else (arm-ldur-w d-x13 d-x14 0))))
        (if (not (= (bitwise-and code 8) 0))
            (ada-e (arm-lsl-imm d-result d-x13 3))
            (begin
              (ada-e (arm-add-imm d-x13 d-x13 2))
              (adf-cmp d-x13 d-x16)
              (ada-bc ada-c-hi slow)
              (ada-e (arm-lsl-imm d-x13 d-x13 3))
              (ada-e (arm-sub d-x13 d-x11 d-x13))
              (ada-e (arm-ldur d-result d-x13 0))))))))

;; `blobref-get` of the suffix ref in `RESULT`, a scalar of layout `code`,
;; into `RESULT`.
(define adf-suffix-get (subr da-assembles (int bool int) unit)
  (lambda (code raw slow)
    (begin
      (adf-suffix-owner d-result slow)
      (adf-within (adf-flat-size code) ada-c-hi slow)
      (ada-e (arm-add d-x11 d-x11 d-x15))
      (cond ((and (= code d-flat-f64) raw) (ada-e (arm-ldur d-result d-x11 0)))
            ((= code d-flat-f64)
             (begin (ada-e (arm-ldur d-x9 d-x11 0)) (adf-box-bits slow)))
            ((= code d-flat-f32)
             (begin
               (ada-e (arm-ldur-w d-x13 d-x11 0))
               (ada-e (arm-lsl-imm d-x13 d-x13 32))
               (ada-e (arm-add-imm d-result d-x13 adf-f32-tag))))
            ((= code d-flat-i32)
             (begin
               (ada-e (arm-ldur-w d-x13 d-x11 0))
               (ada-e (arm-lsl-imm d-x13 d-x13 32))
               (ada-e (arm-asr-imm d-result d-x13 29))))
            ((= code d-flat-u32)
             (begin (ada-e (arm-ldur-w d-x13 d-x11 0)) (ada-e (arm-lsl-imm d-result d-x13 3))))
            ((= code d-flat-i64)
             (begin
               (ada-e (arm-ldur d-x13 d-x11 0))
               (ada-e (arm-lsl-imm d-x14 d-x13 3))
               (ada-e (arm-asr-imm d-x15 d-x14 3))
               (adf-cmp d-x15 d-x13)
               (ada-bc ada-c-ne slow)
               (ada-mov d-result d-x14)))
            (else
             (begin
               (ada-e (arm-ldur d-x13 d-x11 0))
               (ada-e (arm-lsr-imm d-x15 d-x13 60))
               (adf-cmp-imm d-x15 0)
               (ada-bc ada-c-ne slow)
               (ada-e (arm-lsl-imm d-result d-x13 3))))))))

;; `v`, a value, stored by the layout in `c` (a fixnum) with `wide` (an
;; 8-byte store of a register) and `narrow` (a 4-byte one), to `stored`; a
;; 64-bit integer's that is no fixnum, to `slow`. `flat_set`'s and
;; `suffix_set`'s store, the same in both but for where.
(define adf-store-by
  (subr da-assembles (int int (subr da-assembles (int) unit) (subr da-assembles (int) unit) int int)
        unit)
  (lambda (c v wide narrow slow stored)
    (let* ((not-f64 (ada-label)) (not-f32 (ada-label)) (wide-l (ada-label)))
      (begin
        (adf-is c d-flat-f64 not-f64)
        (ada-e (arm-ldur d-x13 v (- 0 d-tag-bloblet)))
        (wide d-x13)
        (ada-b stored)
        (ada-bind not-f64)
        (adf-is c d-flat-f32 not-f32)
        (ada-e (arm-lsr-imm d-x13 v 32))
        (narrow d-x13)
        (ada-b stored)
        ;; A 32-bit integer is the fixnum of its value; a 64-bit one may be
        ;; a bignum, the call-out's.
        (ada-bind not-f32)
        (adf-cmp-imm c (* d-flat-i64 8))
        (ada-bc ada-c-eq wide-l)
        (adf-cmp-imm c (* d-flat-u64 8))
        (ada-bc ada-c-eq wide-l)
        (ada-e (arm-asr-imm d-x13 v 3))
        (narrow d-x13)
        (ada-b stored)
        (ada-bind wide-l)
        (ada-e (arm-tst-low v 3))
        (ada-bc ada-c-ne slow)
        (ada-e (arm-asr-imm d-x13 v 3))
        (wide d-x13)
        (ada-bind stored)))))

;; Unit into `RESULT`, and to `done`.
(define adf-unit-to (subr da-assembles (int) unit)
  (lambda (done) (begin (ada-imm d-result d-unit) (ada-b done))))

;; `blobref-set!` of the suffix ref in X1, a scalar of the layout the
;; fixnum in X2 says, to X3.
(define adf-suffix-set (subr da-assembles (int int) unit)
  (lambda (slow done)
    (let ((v 3) (c 2))
      (begin
        (adf-suffix-writable 1 slow)
        ;; The width: 8 for the 64-bit layouts, as bits of a word, else 4.
        (ada-e (arm-lsr-imm d-x16 c 3))
        (ada-e (arm-movz d-x9 adf-wide 0))
        (ada-e (arm-lsrv d-x9 d-x9 d-x16))
        (ada-e (arm-and-low d-x9 d-x9 1))
        (ada-e (arm-lsl-imm d-x9 d-x9 2))
        (ada-e (arm-add-imm d-x9 d-x9 4))
        (ada-e (arm-add d-x9 d-x15 d-x9))
        (adf-cmp d-x9 d-x13)
        (ada-bc ada-c-hi slow)
        (ada-e (arm-add d-x11 d-x11 d-x15))
        (adf-store-by c v
                      (lambda (s) (ada-e (arm-stur s d-x11 0)))
                      (lambda (s) (ada-e (arm-stur-w s d-x11 0)))
                      slow (ada-label))
        (adf-unit-to done)))))

;; `bytevector-u8-set!` of the bytevector in X1 at X2 to the `u8` in X3:
;; unit into `RESULT`, and to `done`.
(define adf-bytes-set (subr da-assembles (int int) unit)
  (lambda (slow done)
    (let ((bv 1) (i 2) (v 3))
      (begin
        (ada-e (arm-tst-low i 3))
        (ada-bc ada-c-ne slow)
        (ada-e (arm-asr-imm d-x15 i 3))
        (ada-e (arm-ldur d-x14 bv -4))
        (adf-cmp d-x15 d-x14)
        (ada-bc ada-c-hs slow)
        (ada-e (arm-lsr-imm d-x13 v 3))
        (ada-e (arm-add d-x11 bv d-x15))
        (ada-e (arm-add-imm d-x11 d-x11 4))
        (ada-e (arm-strb d-x13 d-x11))
        (adf-unit-to done)))))

;; `flatarray-set!` of the flat array in X1 at X2 to X3; `raw`: the value
;; is an `f64`'s bits.
(define adf-flat-set (subr da-assembles (int int bool) unit)
  (lambda (slow done raw)
    (let* ((v 3) (stored (ada-label)))
      (begin
        (adf-flat-element 1 2 slow)
        (if raw
            (begin (ada-e (arm-str-x8 v d-x15 d-x14)) (adf-unit-to done))
            (begin
              (adf-store-by d-x16 v
                            (lambda (s) (ada-e (arm-str-x8 s d-x15 d-x14)))
                            (lambda (s) (ada-e (arm-str-w4 s d-x15 d-x14)))
                            slow stored)
              (adf-unit-to done)))))))

;;; ------------------------------------------------------------ shapes

;; The kinds a shape predicate takes a bloblet of, in the order tested;
;; none for one this does not do so.
(define adf-shape-kinds (subr da-assembles (string) da-bytes)
  (lambda (name)
    (case name
      (("exact-integer?") (cons d-kind-bignum nil))
      (("symbol?") (cons d-kind-symbol nil))
      (("string?") (cons d-kind-string nil))
      (("%fx26-array?") (cons d-kind-bloblet nil))
      (("%fx26-box?") (cons d-kind-box nil))
      (("%fx26-sum?") (cons d-kind-sum nil))
      (("%fx26-product?") (cons d-kind-product nil))
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
(define adf-kinds (subr da-assembles (da-bytes int) unit)
  (lambda (ks yes)
    (if (null? ks)
        #u
        (begin (adf-cmp-imm d-x13 (car ks)) (ada-bc ada-c-eq yes) (adf-kinds (cdr ks) yes)))))

;; The kind of the bloblet in `RESULT`, in X13, or to `no` if it is no
;; bloblet, or `slow` if its header is not found or is large. Its header
;; tested for a bloblet's kinds `ks`, `#t` or `#f` into `RESULT` after.
(define adf-shape-kind (subr da-assembles (string da-bytes int) unit)
  (lambda (name ks slow)
    (let* ((x d-result) (yes (ada-label)) (no (ada-label)) (have (ada-label))
           (end (ada-label)))
      (begin
        ;; A fixnum is an exact integer.
        (if (string=? name "exact-integer?")
            (begin (ada-e (arm-tst-low x 3)) (ada-bc ada-c-eq yes))
            #u)
        (adf-tagged d-x13 x d-tag-bloblet no)
        (ada-e (arm-ldur d-x16 x (ada-field-off 1)))
        (ada-e (arm-and-low d-x13 d-x16 3))
        (adf-cmp-imm d-x13 d-tag-header)
        (ada-bc ada-c-eq have)
        (adf-cmp-imm d-x13 d-tag-trailer)
        (ada-bc ada-c-ne slow)
        (ada-e (arm-sub-imm d-x16 d-x16 d-tag-trailer))
        (ada-e (arm-sub d-x14 x d-x16))
        (ada-e (arm-ldur d-x16 d-x14 (ada-field-off 1)))
        (ada-bind have)
        (ada-e (arm-ubfx d-x13 d-x16 d-h-kind-lo d-h-kind-width))
        (adf-cmp-imm d-x13 d-kind-extension)
        (ada-bc ada-c-eq slow)
        (adf-kinds ks yes)
        (ada-bind no)
        (ada-imm d-result d-false)
        (ada-b end)
        (ada-bind yes)
        (ada-imm d-result d-true)
        (ada-bind end)))))

;; `RESULT` := `#t` where `c` holds, else `#f`.
(define adf-flag (subr da-assembles (int) unit)
  (lambda (c)
    (begin (ada-imm d-x15 d-true) (ada-imm d-x16 d-false)
           (ada-e (arm-csel d-result d-x15 d-x16 c)))))

;; A shape predicate of `RESULT`, in line: whether it is one this does.
(define adf-shape-fast (subr da-assembles (string int) bool)
  (lambda (name slow)
    (let ((x d-result))
      (cond
        ((string=? name "null?")
         (begin (ada-imm d-x13 d-null) (adf-cmp x d-x13) (adf-flag ada-c-eq) #t))
        ((string=? name "pair?")
         (begin (ada-e (arm-and-low d-x13 x 3)) (adf-cmp-imm d-x13 d-tag-pair)
                (adf-flag ada-c-eq) #t))
        ((or (string=? name "char?") (string=? name "%fx26-f32?"))
         (begin
           (ada-e (arm-and-low d-x13 x 8))
           (adf-cmp-imm d-x13 (bitwise-and (if (string=? name "char?") d-char0 d-f32-0) 255))
           (adf-flag ada-c-eq)
           #t))
        ((string=? name "boolean?")
         (begin
           (ada-imm d-x15 d-false)
           (ada-imm d-x16 d-true)
           (adf-cmp x d-x15)
           (ada-e (arm-csel d-x13 d-x16 d-x15 ada-c-eq))
           (adf-cmp x d-x16)
           (ada-e (arm-csel d-result d-x16 d-x13 ada-c-eq))
           #t))
        (else
         (let ((ks (adf-shape-kinds name)))
           (if (null? ks) #f (begin (adf-shape-kind name ks slow) #t))))))))
)))
