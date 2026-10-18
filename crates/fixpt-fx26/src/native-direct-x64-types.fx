;;; The types of the native convention's compiler to x86_64 written in
;;; FX-26 (`native-direct-x64.fx` and the files beside it), and the
;;; signatures of its modules as each other use them: a module file of no
;;; state (`TODO.md` §68).

;; Assembling: the assembler's state read, written and grown; looping.
(define-effect da-assembles (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin))
(define-effect da-reads (maxeff (read @globals) (read @k) spin))
;; Bytes, and lists of ints.
(define-type da-bytes (listof int @k))
(define-type da-ints (arrayof int @k))
(define-type da-bools (arrayof bool @k))
(define-type da-strings (listof string @k))
;; Pairs of ints: a displacement to patch and its label; a trap's label
;; and code.
(define-type da-pairs (listof (productof (1 int) (2 int)) @k))
;; Where the assembler is (`da-mark`).
(define-type da-mark (productof (1 int) (2 int) (3 da-pairs) (4 int)))
;; Something to do with a register, in place (`in_place`).
(define-type da-on-reg (subr da-assembles (int) unit))

;;; ------------------------------------------------------------ signatures

;; The assembler and the machine sequences the compiler's files share
;; (`native-direct-x64-asm.fx`): `direct/x64.rs`'s `Asm`, and its free
;; functions of no procedure.
(define-type native-direct-x64-asm-sig
  (moduleof (val da-c-o int)
            (val da-c-b int)
            (val da-c-ae int)
            (val da-c-e int)
            (val da-c-ne int)
            (val da-c-be int)
            (val da-c-a int)
            (val da-c-s int)
            (val da-c-ns int)
            (val da-c-p int)
            (val da-c-l int)
            (val da-c-ge int)
            (val da-c-le int)
            (val da-c-g int)
            (val da-add int)
            (val da-or int)
            (val da-and int)
            (val da-sub int)
            (val da-xor int)
            (val da-cmp int)
            (val da-shl int)
            (val da-shr int)
            (val da-sar int)
            (val da-signed (subr pure (int) int))
            (val da-reset (subr da-assembles (int) unit))
            (val da-here (subr da-reads () int))
            (val da-e (subr da-assembles (da-bytes) unit))
            (val da-label (subr da-assembles () int))
            (val da-bind (subr da-assembles (int) unit))
            (val da-used? (subr da-reads (int) bool))
            (val da-to (subr da-assembles (int da-bytes) unit))
            (val da-jmp (subr da-assembles (int) unit))
            (val da-jcc (subr da-assembles (int int) unit))
            (val da-call-l (subr da-assembles (int) unit))
            (val da-lea-l (subr da-assembles (int int) unit))
            (val da-field (subr da-assembles (int int) unit))
            (val da-imm (subr da-assembles (int int) unit))
            (val da-cmp-k (subr da-assembles (int int) unit))
            (val da-flag (subr da-assembles (int int) unit))
            (val da-in-reg (subr pure (int) int))
            (val da-reg-off (subr pure (int) int))
            (val da-get (subr da-assembles (int int) int))
            (val da-put (subr da-assembles (int int) unit))
            (val da-store-reg (subr da-assembles (int int int int) unit))
            (val da-load-reg (subr da-assembles (int int int int) unit))
            (val da-regs-to-args (subr da-assembles (int) unit))
            (val da-finish (subr da-assembles () da-bytes))
            (val da-mark (subr da-reads () da-mark))
            (val da-rewind (subr da-assembles (da-mark) unit))
            (val da-fail (subr da-assembles (string) unit))
            (val da-err (subr da-reads () string))
            (val da-ok? (subr da-reads () bool))
            (val da-co (subr pure (int int int) int))
            (val da-callout (subr da-assembles (int) int))
            (val da-callouts (subr da-assembles () da-bytes))
            (val da-stub (subr da-assembles (int int) unit))
            (val da-trap (subr da-assembles (int int) unit))
            (val da-place-stubs (subr da-assembles () unit))
            (val da-ld (subr da-assembles (int int int) unit))
            (val da-sto (subr da-assembles (int int int) unit))
            (val da-mov (subr da-assembles (int int) unit))
            (val da-leave (subr da-assembles () unit))
            (val da-resume (subr da-assembles () unit))
            (val da-call-out (subr da-assembles (int) unit))
            (val da-trapped (subr da-assembles (int) unit))
            (val da-trap-set (subr da-assembles () unit))
            (val da-fail-here (subr da-assembles (int) unit))
            (val da-keep (subr da-assembles (int bool) unit))
            (val da-push-frame (subr da-assembles (int int) unit))
            (val da-push-frame-ret (subr da-assembles (int) unit))
            (val da-pop-frame (subr da-assembles (int) unit))
            (val da-pop-frame-ret (subr da-assembles (int) unit))
            (val da-stub-return (subr da-assembles () unit))
            (val da-preempt (subr da-assembles () unit))
            (val da-pure-call (subr da-assembles (int da-bytes int) unit))
            (val da-in-place (subr da-assembles (int da-on-reg) unit))
            (val da-ubfx (subr da-assembles (int int int int) unit))
            (val da-check-reg (subr da-assembles (int int) unit))
            (val da-check-fixnum (subr da-assembles (int int) unit))
            (val da-card-mark (subr da-assembles (int int int int) unit))
            (val da-field-off (subr pure (int) int))
            (val da-header (subr pure (int int int) int))
            (val da-trailer (subr pure (int) int))
            (val da-continuation-code (subr da-assembles (int) da-bytes))))

;;; ------------------------------------------------------------ representations

;; A procedure's cells as the analysis reads them (`reps.rs`): each one's
;; value as a fixnum (0 for one that is not), and whether it is one.
(define-type nr-cells (productof (1 da-ints) (2 da-bools)))
;; What `reps_of` gives: by instruction, its registers' representations
;; where it starts and where it ends (`nr-reps`, packed).
(define-type nr-in-out (productof (1 da-ints) (2 da-ints)))
;; What `step` gives: the conversions before an instruction (`nr-convert`),
;; and the representations after it.
(define-type nr-stepped (productof (1 da-bytes) (2 int)))
;; A raw operation (`RawOp`): its kind (0 none, 1 an integer's, 2 an
;; `f64`'s), whether signed, and the name after the type (`what`).
(define-type nr-raw-op (productof (1 int) (2 bool) (3 string)))

;; Where native code keeps `i64`, `u64` and `f64` values
;; (`native-reps.fx`): `direct/reps.rs`, step for step. A register's
;; representation (`Rep`) is a number: `nr-undefined` 0, `nr-value` 1,
;; `nr-raw-signed` 2, `nr-raw-unsigned` 3, `nr-f64` 4, `nr-fix` 5; those of
;; `RESULT` and REG1…REG8 (`Reps`) one int, three bits each, `RESULT`'s
;; lowest. A conversion (`Convert`) is 128 times its kind (box 0, unbox 1,
;; check 2), plus 8 times its register (0 to 8), plus its representation. Masks of
;; registers and parameters are ints, bit `r` for register `r` (bit 0 for
;; REG1 in a mask of parameters, as `raw_param` has it). Instructions are
;; numbered by where they are in `starts`, as `reps.rs` numbers them.
(define-type native-reps-sig
  (moduleof (val nr-undefined int)
            (val nr-value int)
            (val nr-raw-signed int)
            (val nr-raw-unsigned int)
            (val nr-f64 int)
            (val nr-fix int)
            (val nr-raw? (subr pure (int) bool))
            (val nr-rep (subr pure (int int) int))
            (val nr-with (subr pure (int int int) int))
            (val nr-all (subr pure (int) int))
            (val nr-join (subr da-reads (int int) int))
            (val nr-unboxes (subr da-assembles (int int) da-bytes))
            (val nr-checks (subr da-assembles (int int int) da-bytes))
            (val nr-raw-op (subr da-assembles (string) nr-raw-op))
            (val nr-is-f64-set? (subr da-reads (nr-cells int) bool))
            (val nr-step (subr da-assembles (nr-cells int bool bool da-bools int int int) nr-stepped))
            (val nr-int-routine? (subr pure (int) bool))
            (val nr-starts (subr da-assembles (nr-cells) da-ints))
            (val nr-reps-of
                 (subr da-assembles (nr-cells da-ints bool da-bools int da-ints) nr-in-out))
            (val nr-raw-refs (subr da-assembles (nr-cells da-ints da-bools) da-bools))
            (val nr-raw-param? (subr pure (int int) bool))
            (val nr-raw-params (subr da-assembles (nr-cells da-ints da-bools) int))
            (val nr-live-in (subr da-assembles (nr-cells da-ints da-bools) da-ints))
            (val nr-raw-slots (subr da-assembles (nr-cells da-ints int) da-bools))
            (val nr-split-slots (subr da-assembles (nr-cells) nr-cells))))

;;; ------------------------------------------------------------ raw values

;; An `int` operation's slow path (`IntSlow`): its labels in, from an
;; overflow (-1 for none) and back; its operands' registers (`y` -1 with
;; an immediate); the immediate; where its value goes; the primitive;
;; whether a difference; and the branch a comparison makes, if it makes
;; one (-1 for none), and whether taken when true.
(define-type dr-int-slow
  (productof (1 int) (2 int) (3 int) (4 int) (5 int) (6 int) (7 int) (8 int) (9 bool)
             (10 int) (11 bool)))

;; Raw values and the operations native code does on them
;; (`native-direct-x64-raw.fx`): `direct/x64.rs`'s `box_reg` to
;; `narrow_fast` and `IntSlow`, step for step, each `dr-` and its Rust
;; name. What makes a call-out numbers it (`da-callout`); what traps, a
;; stub (`da-stub`).
(define-type native-direct-x64-raw-sig
  (moduleof (val dr-box-reg (subr da-assembles (int bool) unit))
            (val dr-unbox-reg (subr da-assembles (int) unit))
            (val dr-unbox-f64 (subr da-assembles (int) unit))
            (val dr-raw-entry (subr da-assembles (int) unit))
            (val dr-raw-entry-skip (subr da-assembles (int) int))
            (val dr-take-raw-f64 (subr da-assembles () unit))
            (val dr-raw-return (subr da-assembles () unit))
            (val dr-box-f64 (subr da-assembles (int) unit))
            (val dr-box-bits (subr da-assembles (int) unit))
            (val dr-unbox-to (subr da-assembles (int int) unit))
            (val dr-convert (subr da-assembles (da-bytes int int) unit))
            (val dr-f64-of-int (subr da-assembles (int) unit))
            (val dr-int-of-f64 (subr da-assembles (int) unit))
            (val dr-float-test (subr da-assembles (bool string) bool))
            (val dr-f64-fast (subr da-assembles (string int) unit))
            (val dr-f32-fast (subr da-assembles (string int) bool))
            (val dr-wrap-small (subr da-assembles (bool int) unit))
            (val dr-raw-fast (subr da-assembles (bool string int) unit))
            (val dr-narrow-fast (subr da-assembles (string int int) bool))
            (val dr-int-slow (subr da-assembles (dr-int-slow) unit))))

;;; ------------------------------------------------------------ the heap's

;; Flat arrays, suffix refs, bytevectors and shapes in line
;; (`native-direct-x64-flat.fx`): `direct/x64.rs`'s `flat_count` to
;; `flat_set` and `shape_fast`, step for step, each `df-` and its Rust name.
(define-type native-direct-x64-flat-sig
  (moduleof (val df-flat-count (subr da-assembles (int int) unit))
            (val df-flat-element (subr da-assembles (int int int) unit))
            (val df-flat-ref (subr da-assembles (int int) unit))
            (val df-suffix-owner (subr da-assembles (int int) unit))
            (val df-suffix-writable (subr da-assembles (int int) unit))
            (val df-suffix-store (subr da-assembles (int int bool int) unit))
            (val df-blobref-index (subr da-assembles (int int int) unit))
            (val df-flat-variant (subr da-assembles (int int int) unit))
            (val df-blobref-at (subr da-assembles (int int) unit))
            (val df-suffix-step (subr da-assembles (int int) unit))
            (val df-suffix-fits (subr da-assembles (int int) unit))
            (val df-suffix-length (subr da-assembles (int int) unit))
            (val df-suffix-index (subr da-assembles (int) unit))
            (val df-flat-tag (subr da-assembles (int int) unit))
            (val df-suffix-get (subr da-assembles (int bool int) unit))
            (val df-wide-layout (subr da-assembles (int int) unit))
            (val df-suffix-set (subr da-assembles (int int) unit))
            (val df-bytes-set (subr da-assembles (int int) unit))
            (val df-flat-set (subr da-assembles (int int bool) unit))
            (val df-shape-fast (subr da-assembles (string int) bool))))
