;;; Register code's fast paths and what it does inline, compiled to arm64
;;; machine code, in FX-26: `fixpt-native/src/cellular/regcode.rs`'s
;;; `pure_call`, `int_fast`, `shape_test`, `bump_words`, `inline_op` and
;;; `inline`, and the helpers they share with the rest of it, which
;;; `native-arm64-regs.fx` is. Of no state of its own: it emits into
;;; `native.fx`'s assembler, as `native-x64-regs-ops.fx` does into
;;; `native-x64.fx`'s.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoders, the layouts and
;;; `native.fx`'s assembler.

(let* ((regs-types (load-module "fx26:native-arm64-regs-types.fx"))
       (arm64-types (load-module "fx26:arm64-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (native-layout-types (load-module "fx26:native-layout-types.fx")))
  (lambda ((arm64 (select arm64-types arm64-sig))
           (layout (select layout-types layout-sig))
           (native-layout (select native-layout-types native-layout-sig))
           (regs-layout (select regs-types native-arm64-regs-layout-sig))
           (asm (select regs-types native-arm64-asm-sig)))
    (module
(hide (include regs-types))
(hide (include arm64) (include layout) (include native-layout) (include regs-layout) (include asm))

;; Conditions, by the hardware's numbers.
(define ar-eq int 0)
(define ar-ne int 1)
(define ar-hs int 2)
(define ar-lo int 3)
(define ar-vs int 6)
(define ar-hi int 8)
(define ar-ls int 9)
(define ar-ge int 10)
(define ar-lt int 11)
(define ar-gt int 12)

;; `REGk`'s machine register (`reg`): `x1`…`x8`, and `REG0` the closure.
(define ar-reg (subr pure (int) int) (lambda (k) (if (= k 0) n-clo k)))
;; Field `f` of the register word, its bits, as `mov_imm64` takes them.
(define ar-bits (subr pure (tword int) int) (lambda (rw f) (tword-bits rw f)))
;; A header of `kind` and `fields` fields, no suffix (`make_header`).
(define ar-header (subr (maxeff (read @globals) spin) (int int) int)
  (lambda (kind fields)
    (+ a-tag-header
       (+ (arithmetic-shift kind header-kind-lo) (arithmetic-shift fields header-fields-lo)))))

;;; ------------------------------------------------------------ helpers

;; `d` := `n − k`, and `n + k`, for a constant `k` of any size (clobbers
;; `x16`).
(define ar-sub-const (subr (maxeff ar-assembles spin) (int int int) unit)
  (lambda (d n k)
    (if (< k 4096)
        (n-e (arm-sub-imm d n k))
        (begin (n-value n-x16 k) (n-e (arm-sub d n n-x16))))))
(define ar-add-const (subr (maxeff ar-assembles spin) (int int int) unit)
  (lambda (d n k)
    (if (< k 4096)
        (n-e (arm-add-imm d n k))
        (begin (n-value n-x16 k) (n-e (arm-add d n n-x16))))))
;; `IP` := the address of the running register word's field `fields`, its
;; last (`pool`).
(define ar-pool (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (fields)
    (begin (n-e (arm-mov n-ip n-cur)) (ar-sub-const n-ip n-ip (+ 4 (* 8 fields))))))
;; `dst` := field `f` of the running register word (`cell`).
(define ar-cell (subr (maxeff ar-assembles spin) (int int int) unit)
  (lambda (dst f fields)
    (let ((off (* 8 (- fields f))))
      (if (< off 32768)
          (n-e (arm-ldr dst n-ip off))
          (begin
            (n-value n-x16 off)
            (n-e (arm-add n-x16 n-ip n-x16))
            (n-e (arm-ldr dst n-x16 0)))))))
;; `dst` := the operand in field `f`: in the instruction if it is
;; immediate, else from the word.
(define ar-constant (subr (maxeff ar-assembles spin) (int tword int int) unit)
  (lambda (dst rw f fields)
    (let ((b (ar-bits rw f)))
      (if (or (tword-int? rw f) (= (modulo b 8) 3)) (n-value dst b) (ar-cell dst f fields)))))
;; `dst` := field `f` of the bloblet whose `suffix + 4` is in `b`
;; (`field_of`).
(define ar-field-of (subr (maxeff ar-assembles spin) (int int int) unit)
  (lambda (dst b f)
    (let ((off (n-field-off f)))
      (if (>= off -256)
          (n-e (arm-ldur dst b off))
          (begin (ar-sub-const n-x16 b (- 0 off)) (n-e (arm-ldr dst n-x16 0)))))))
;; Frame slot `n`, `8n` bytes below `FP`, into `r`, or from it with
;; `store?` (`slot`).
(define ar-slot (subr (maxeff ar-assembles spin) (int int bool) unit)
  (lambda (r n store?)
    (let ((off (* 8 n)))
      (if (<= off 256)
          (n-e (if store? (arm-stur r n-fp (- 0 off)) (arm-ldur r n-fp (- 0 off))))
          (begin
            (ar-sub-const n-x16 n-fp off)
            (n-e (if store? (arm-str r n-x16 0) (arm-ldr r n-x16 0))))))))
;; `IP` := the address of the running word's field `f`, as a cellular ip
;; is (`ip_at`).
(define ar-ip-at (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (f) (begin (n-e (arm-mov n-ip n-cur)) (ar-sub-const n-ip n-ip (+ 4 (* 8 f))))))
;; Push `REG1`…`REGn`, `REG1` deepest; past `REGS`, the rest are a list in
;; the last register (`push_regs`).
(define ar-push-from (subr (maxeff ar-assembles spin) (int int) unit)
  (lambda (k n)
    (if (> k n) #u (begin (n-e (arm-str-pre (ar-reg k) n-dsp -8)) (ar-push-from (+ k 1) n)))))
(define ar-push-list (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (left)
    (if (= left 0)
        #u
        (begin
          (n-e (arm-ldur n-x13 n-x16 -1))
          (n-e (arm-str-pre n-x13 n-dsp -8))
          (n-e (arm-ldur n-x16 n-x16 7))
          (ar-push-list (- left 1))))))
(define ar-push-regs (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (n)
    (if (<= n a-regs)
        (ar-push-from 1 n)
        (begin
          (ar-push-from 1 (- a-regs 1))
          (n-e (arm-mov n-x16 (ar-reg a-regs)))
          (ar-push-list (+ (- n a-regs) 1))))))

;; `RESULT` := primitive `p` of `RESULT`, `y` and, unless it is -1, `z`,
;; called in Rust (`pure_call`) with no safepoint, REG1…REG8 and the link
;; kept on the machine stack around it; its failure a trap.
(define ar-pair-regs (subr (maxeff ar-assembles spin) (int int) unit)
  (lambda (r store?)
    (if (or (< r 1) (> r 7))
        #u
        (begin
          (n-e (if (= store? 1) (arm-stp-pre r (+ r 1) a-sp -16) (arm-ldp-post r (+ r 1) a-sp 16)))
          (ar-pair-regs (+ r (* 2 store?)) store?)))))
(define ar-pure-call3 (subr (maxeff ar-assembles spin) (int int int) unit)
  (lambda (p y z)
    (begin
      (n-e (arm-mov n-x14 y))
      (if (>= z 0) (n-e (arm-mov n-x15 z)) #u)
      ;; x1…x8 pushed from x1 up, popped from x7 down.
      (ar-pair-regs 1 1)
      (n-e (arm-stp-pre a-lr 31 a-sp -16))
      (n-e (arm-mov 3 n-x14))
      (if (>= z 0) (n-e (arm-mov 4 n-x15)) #u)
      (n-e (arm-mov 2 a-result))
      (n-e (arm-mov 0 n-st))
      (n-value 1 p)
      (n-e (arm-ldr n-x16 n-st a-st-pure))
      (n-e (arm-blr n-x16))
      (n-e (arm-mov n-x13 1))
      (n-e (arm-ldp-post a-lr 31 a-sp 16))
      (ar-pair-regs 7 -1)
      (n-e (arm-cmp-imm n-x13 0))
      (n-trap-if ar-ne a-trap-prim 0))))
(define ar-pure-call (subr (maxeff ar-assembles spin) (int int) unit)
  (lambda (p y) (ar-pure-call3 p y -1)))

;;; ------------------------------------------------------------ fast paths

;; `modulo`, `quotient`, `*` and `arithmetic-shift` of the fixnums in
;; `RESULT` and `y`, into `RESULT`, as `int_fast` does them: whether this
;; is one, its fast path emitted, to `slow` for what it leaves.
(define ar-int-fast (subr (maxeff ar-assembles spin) (string int int) bool)
  (lambda (name y slow)
    (if (not (or (string=? name "modulo") (string=? name "%fx26-quotient")
                 (string=? name "%fx26-mul") (string=? name "%fx26-arithmetic-shift")))
        #f
        (let ((x a-result))
          (begin
            (n-e (arm-orr n-x15 x y))
            (n-e (arm-tst-low n-x15 3))
            (n-b-cond ar-ne slow)
            (cond
              ;; A product in 61 bits: the high word only the low's sign.
              ((string=? name "%fx26-mul")
               (begin
                 (n-e (arm-asr-imm n-x14 y 3))
                 (n-e (arm-mul n-x15 x n-x14))
                 (n-e (arm-smulh n-x16 x n-x14))
                 (n-e (arm-asr-imm n-x14 n-x15 63))
                 (n-e (arm-cmp n-x16 n-x14))
                 (n-b-cond ar-ne slow)
                 (n-e (arm-mov a-result n-x15))))
              ;; A quotient past a fixnum is the primitive's; a remainder is
              ;; `modulo`'s when it has the divisor's sign, or is 0.
              ((or (string=? name "%fx26-quotient") (string=? name "modulo"))
               (begin
                 (n-e (arm-cmp-imm y 0))
                 (n-b-cond ar-eq slow)
                 (n-e (arm-sdiv n-x15 x y))
                 (if (string=? name "%fx26-quotient")
                     (begin
                       (n-e (arm-lsl-imm n-x14 n-x15 3))
                       (n-e (arm-asr-imm n-x16 n-x14 3))
                       (n-e (arm-cmp n-x16 n-x15))
                       (n-b-cond ar-ne slow))
                     (let ((signed (n-label)))
                       (begin
                         (n-e (arm-msub n-x14 n-x15 y x))
                         (n-e (arm-cmp-imm n-x14 0))
                         (n-b-cond ar-eq signed)
                         (n-e (arm-eor n-x16 n-x14 y))
                         (n-e (arm-cmp-imm n-x16 0))
                         (n-b-cond ar-ge signed)
                         (n-e (arm-add n-x14 n-x14 y))
                         (n-bind signed))))
                 (n-e (arm-mov a-result n-x14))))
              ;; Left while the result stays a fixnum; right (floor) by
              ;; fewer than 63.
              (else
               (let ((right (n-label)) (done (n-label)))
                 (begin
                   (n-e (arm-asr-imm n-x14 y 3))
                   (n-e (arm-cmp n-x14 a-xzr))
                   (n-b-cond ar-lt right)
                   (n-e (arm-cmp-imm n-x14 61))
                   (n-b-cond ar-ge slow)
                   (n-e (arm-lslv n-x15 x n-x14))
                   (n-e (arm-asrv n-x16 n-x15 n-x14))
                   (n-e (arm-cmp n-x16 x))
                   (n-b-cond ar-ne slow)
                   (n-e (arm-mov a-result n-x15))
                   (n-b done)
                   (n-bind right)
                   (n-e (arm-sub n-x14 a-xzr n-x14))
                   (n-e (arm-cmp-imm n-x14 63))
                   (n-b-cond ar-hs slow)
                   (n-e (arm-asrv n-x15 x n-x14))
                   (n-e (arm-asr-imm n-x15 n-x15 3))
                   (n-e (arm-lsl-imm a-result n-x15 3))
                   (n-bind done)))))
            #t)))))

;; `RESULT` := `#t` if condition `c` holds, else `#f`, by `x15` and `x16`.
(define ar-boolean (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (c)
    (begin
      (n-value n-x15 n-true)
      (n-value n-x16 n-false)
      (n-e (arm-csel a-result n-x15 n-x16 c)))))
;; Compare the kind in `x13` with shape `name`'s, from its `i`th on, to
;; `yes` on any.
(define ar-kinds (subr (maxeff ar-assembles spin) (string int int) unit)
  (lambda (name i yes)
    (let ((c (a-shape-kind name i)))
      (if (< c 0)
          #u
          (begin (n-e (arm-cmp-imm n-x13 c)) (n-b-cond ar-eq yes) (ar-kinds name (+ i 1) yes))))))
;; `RESULT` := `#t` at `yes`, `#f` at `no`, and on at `end`.
(define ar-yes-no (subr (maxeff ar-assembles spin) (int int int) unit)
  (lambda (yes no end)
    (begin
      (n-bind yes)
      (n-value a-result n-true)
      (n-b end)
      (n-bind no)
      (n-value a-result n-false)
      (n-bind end))))

;; Shape predicate `name` of `src` into `RESULT` (`shape_test`): whether
;; this is one. Uses x11 and x13 to x16.
(define ar-shape-test (subr (maxeff ar-assembles spin) (int string int) bool)
  (lambda (src name slow)
    (cond
      ((or (string=? name "pair?") (string=? name "char?")
           (string=? name "%fx26-f32?") (string=? name "null?"))
       (begin
         (cond ((string=? name "pair?")
                (begin (n-e (arm-and-low n-x13 src 3)) (n-e (arm-cmp-imm n-x13 n-tag-pair))))
               ((string=? name "null?")
                (begin (n-value n-x13 a-null) (n-e (arm-cmp src n-x13))))
               (else
                (begin
                  (n-e (arm-and-low n-x13 src 8))
                  (n-e (arm-cmp-imm n-x13
                                    (modulo (if (string=? name "char?") a-char0 a-f32-0) 256))))))
         (ar-boolean ar-eq)
         #t))
      ((string=? name "boolean?")
       (begin
         (n-value n-x15 n-false)
         (n-value n-x16 n-true)
         (n-e (arm-cmp src n-x15))
         (n-e (arm-csel n-x13 n-x16 n-x15 ar-eq))
         (n-e (arm-cmp src n-x16))
         (n-e (arm-csel a-result n-x16 n-x13 ar-eq))
         #t))
      ((< (a-shape-kind name 0) 0) #f)
      (else
       (let ((yes (n-label)) (no (n-label)) (have (n-label)) (end (n-label)))
         (begin
           (if (string=? name "exact-integer?")
               (begin (n-e (arm-tst-low src 3)) (n-b-cond ar-eq yes))
               #u)
           (n-e (arm-and-low n-x13 src 3))
           (n-e (arm-cmp-imm n-x13 n-tag-bloblet))
           (n-b-cond ar-ne no)
           (n-e (arm-ldur n-x16 src (n-field-off 1)))
           (n-e (arm-and-low n-x13 n-x16 3))
           (n-e (arm-cmp-imm n-x13 a-tag-header))
           (n-b-cond ar-eq have)
           (n-e (arm-cmp-imm n-x13 n-tag-trailer))
           (n-b-cond ar-ne slow)
           (n-e (arm-sub-imm n-x16 n-x16 n-tag-trailer))
           (n-e (arm-sub n-x11 src n-x16))
           (n-e (arm-ldur n-x16 n-x11 (n-field-off 1)))
           (n-bind have)
           (n-e (arm-ubfx n-x13 n-x16 header-kind-lo header-kind-width))
           (n-e (arm-cmp-imm n-x13 a-kind-extension))
           (n-b-cond ar-eq slow)
           (ar-kinds name 0 yes)
           (n-bind no)
           (n-value a-result n-false)
           (n-b end)
           (n-bind yes)
           (n-value a-result n-true)
           (n-bind end)
           #t))))))

;;; ------------------------------------------------------------ inline

;; Room for `n` words, from the heap's free space or, with `region?`, from
;; the current chunk of the region whose handle is in `REG1`: its address
;; in `x11`, the free space bumped; to `slow` if there is none
;; (`bump_words`).
(define ar-bump-words (subr (maxeff ar-assembles spin) (int bool int) unit)
  (lambda (n region? slow)
    (begin
      (if region?
          (begin
            (n-e (arm-tst-low 1 3))
            (n-b-cond ar-ne slow)
            (n-e (arm-cmp-imm 1 (* 8 a-region-slots)))
            (n-b-cond ar-hs slow)
            (n-e (arm-ldr n-x13 n-st a-st-regions))
            (n-e (arm-add-lsl n-x13 n-x13 1 1))
            (n-e (arm-ldp n-x14 n-x15 n-x13 0)))
          (begin
            (n-e (arm-ldr n-x13 n-st a-st-top))
            (n-e (arm-ldr n-x14 n-x13 0))
            (n-e (arm-ldr n-x15 n-st a-st-alloc-limit))))
      (n-e (arm-add-imm n-x16 n-x14 n))
      (n-e (arm-cmp n-x16 n-x15))
      (n-b-cond ar-hi slow)
      (n-e (arm-ldr n-w n-st a-st-words))
      (n-e (arm-add-lsl n-x11 n-w n-x14 3))
      (n-e (arm-str n-x16 n-x13 0)))))
;; A bloblet of `total` fields at `x11`, its header in `x15`: the header,
;; its trailer, and `RESULT` its pointer (`bloblet_at`).
(define ar-bloblet-at (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (total)
    (begin
      (n-e (arm-str n-x15 n-x11 0))
      (n-value n-x15 (+ n-tag-trailer (* 8 total)))
      (n-e (arm-str n-x15 n-x11 (* 8 total)))
      (n-e (arm-add-imm a-result n-x11 (+ (* 8 (+ 1 total)) n-tag-bloblet))))))
;; `r` as field `k` of the bloblet of `total` fields at `x11` (`field_at`).
(define ar-field-at (subr (maxeff ar-assembles spin) (int int int) unit)
  (lambda (r k total) (n-e (arm-str r n-x11 (* 8 (- (+ 1 total) k))))))
;; `REGj` as field `j`, for `j` from `j` to `count` (`frozen`, `bloblet`).
(define ar-reg-fields (subr (maxeff ar-assembles spin) (int int int) unit)
  (lambda (j count total)
    (if (> j count)
        #u
        (begin (ar-field-at (ar-reg j) j total) (ar-reg-fields (+ j 1) count total)))))
;; The free values `REGj`… as a closure's, the `i`th first.
(define ar-frees (subr (maxeff ar-assembles spin) (int int int int) unit)
  (lambda (j last i total)
    (if (> j last)
        #u
        (begin
          (ar-field-at (ar-reg j) (+ n-closure-free0 i) total)
          (ar-frees (+ j 1) last (+ i 1) total)))))
;; The bloblet in `REG1` has a trailer, in `x16` less its tag, and `REG2`
;; (8k) is one of its fields, 2 ≤ k ≤ F: else `slow`.
(define ar-field-check (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (slow)
    (begin
      (n-e (arm-ldur n-x16 1 (n-field-off 1)))
      (n-e (arm-and-low n-x13 n-x16 3))
      (n-e (arm-cmp-imm n-x13 n-tag-trailer))
      (n-b-cond ar-ne slow)
      (n-e (arm-cmp-imm 2 16))
      (n-b-cond ar-lt slow)
      (n-e (arm-sub-imm n-x16 n-x16 n-tag-trailer))
      (n-e (arm-cmp 2 n-x16))
      (n-b-cond ar-gt slow))))
;; The ASCII character in `REG1`'s code in `x13`, else `slow`; then `x15`
;; and `x16` `#t` and `#f`.
(define ar-ascii (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (slow)
    (begin
      (n-e (arm-asr-imm n-x13 1 8))
      (n-e (arm-cmp-imm n-x13 128))
      (n-b-cond ar-hs slow)
      (n-value n-x15 n-true)
      (n-value n-x16 n-false))))

;; The shape predicate an inline type test names.
(define ar-shape-name (subr pure (string) string)
  (lambda (what)
    (cond ((string=? what "f32?") "%fx26-f32?")
          ((string=? what "array?") "%fx26-array?")
          ((string=? what "box?") "%fx26-box?")
          ((string=? what "sum?") "%fx26-sum?")
          ((string=? what "product?") "%fx26-product?")
          ((string=? what "procedure?") "%fx26-procedure?")
          (else what))))

;; `what` on `REG1`…`REGn` (`count` of them) into `RESULT`, without calling
;; out (`inline_op`); to `slow` when it cannot be done so. `word` is the
;; field of a closure's word, for `closure`.
(define ar-inline-op (subr (maxeff ar-assembles spin) (string int int int int) unit)
  (lambda (what count word fields slow)
    (cond
      ((or (string=? what "closure") (string=? what "region-closure"))
       (let* ((region? (string=? what "region-closure"))
              (first (if region? 2 1))
              (last (if region? (- count 1) count))
              (total (+ (+ (- last first) 1) 2)))
         (begin
           (ar-bump-words (+ 1 total) region? slow)
           (n-value n-x15 (ar-header n-kind-closure total))
           (ar-bloblet-at total)
           (if region?
               (ar-field-at (ar-reg count) n-closure-word total)
               (begin (ar-cell n-x15 word fields) (ar-field-at n-x15 n-closure-word total)))
           (ar-frees first last 0 total))))
      ((string=? what "frozen")
       (begin
         (ar-bump-words (+ 1 count) #f slow)
         (n-value n-x15 (+ (ar-header 0 count)
                           (+ (arithmetic-shift 1 header-fields-frozen-lo)
                              (arithmetic-shift 1 header-suffix-frozen-lo))))
         (n-e (arm-add n-x15 n-x15 1))
         (ar-bloblet-at count)
         (ar-reg-fields 2 count count)))
      ((string=? what "bloblet")
       (begin
         (n-cbnz 1 slow)
         (ar-bump-words (+ 1 count) #f slow)
         (n-value n-x15 (ar-header kind-bloblet count))
         (ar-bloblet-at count)
         (ar-reg-fields 2 count count)))
      ((or (string=? what "rnew") (string=? what "box"))
       (let ((region? (string=? what "rnew")))
         (begin
           (ar-bump-words 3 region? slow)
           (n-value n-x15 (ar-header kind-box 2))
           (ar-bloblet-at 2)
           (ar-field-at (if region? 2 1) 2 2))))
      ((string=? what "field@")
       (begin
         (ar-field-check slow)
         (n-e (arm-sub n-x11 1 2))
         (n-e (arm-ldur a-result n-x11 -4))))
      ((string=? what "fields")
       (begin
         (n-e (arm-ldur n-x16 1 (n-field-off 1)))
         (n-e (arm-and-low n-x13 n-x16 3))
         (n-e (arm-cmp-imm n-x13 n-tag-trailer))
         (n-b-cond ar-ne slow)
         (n-e (arm-sub-imm a-result n-x16 n-tag-trailer))))
      ((string=? what "field!")
       (begin
         (ar-field-check slow)
         ;; The header: F + 1 words before the suffix.
         (n-e (arm-sub n-x11 1 n-x16))
         (n-e (arm-ldur n-x13 n-x11 -12))
         (n-e (arm-ubfx n-x13 n-x13 header-fields-frozen-lo 1))
         (n-cbnz n-x13 slow)
         (n-e (arm-sub n-x11 1 2))
         (n-e (arm-stur 3 n-x11 -4))
         (n-card-mark n-x11 -4)
         (n-value a-result a-unspecified)))
      ((string=? what "whitespace")
       (begin
         (ar-ascii slow)
         (n-e (arm-sub-imm n-x14 n-x13 9))
         (n-e (arm-cmp-imm n-x14 4))
         (n-e (arm-csel a-result n-x15 n-x16 ar-ls))
         (n-e (arm-cmp-imm n-x13 32))
         (n-e (arm-csel a-result n-x15 a-result ar-eq))))
      ((string=? what "symbol-hash") (n-e (arm-ldur a-result 1 (n-field-off 3))))
      ((string=? what "fixnum?") (begin (n-e (arm-tst-low 1 3)) (ar-boolean ar-eq)))
      ((string=? what "boolean?")
       (begin
         (n-value n-x15 n-false)
         (n-value n-x16 n-true)
         (n-e (arm-cmp 1 n-x15))
         (n-e (arm-csel a-result n-x16 n-x15 ar-eq))
         (n-e (arm-cmp 1 n-x16))
         (n-e (arm-csel a-result n-x16 a-result ar-eq))))
      ((or (string=? what "bit-and") (string=? what "bit-ior") (string=? what "bit-xor"))
       (begin
         (n-e (arm-orr n-x13 1 2))
         (n-e (arm-tst-low n-x13 3))
         (n-b-cond ar-ne slow)
         (n-e (cond ((string=? what "bit-and") (arm-and a-result 1 2))
                    ((string=? what "bit-ior") (arm-orr a-result 1 2))
                    (else (arm-eor a-result 1 2))))))
      ((string=? what "bit-not")
       (begin
         (n-e (arm-tst-low 1 3))
         (n-b-cond ar-ne slow)
         (n-e (arm-sub a-result a-xzr 1))
         (n-e (arm-sub-imm a-result a-result 8))))
      ((string=? what "numeric")
       (begin
         (ar-ascii slow)
         (n-e (arm-sub-imm n-x14 n-x13 48))
         (n-e (arm-cmp-imm n-x14 9))
         (n-e (arm-csel a-result n-x15 n-x16 ar-ls))))
      ((string=? what "char-in")
       (let ((again (n-label)) (yes (n-label)) (no (n-label)) (end (n-label)))
         (begin
           (n-e (arm-asr-imm n-x13 1 8))
           (n-e (arm-ldur n-x15 2 -4))
           (n-e (arm-mov n-x14 2))
           (n-bind again)
           (n-cbz n-x15 no)
           (n-e (arm-ldur-w n-x10 n-x14 4))
           (n-e (arm-cmp n-x10 n-x13))
           (n-b-cond ar-eq yes)
           (n-e (arm-add-imm n-x14 n-x14 4))
           (n-e (arm-sub-imm n-x15 n-x15 1))
           (n-b again)
           (ar-yes-no yes no end))))
      ((string=? what "string=")
       (let ((again (n-label)) (yes (n-label)) (no (n-label)) (end (n-label)))
         (begin
           (n-e (arm-ldur n-x15 1 -4))
           (n-e (arm-ldur n-x16 2 -4))
           (n-e (arm-cmp n-x15 n-x16))
           (n-b-cond ar-ne no)
           (n-e (arm-mov n-x13 1))
           (n-e (arm-mov n-x14 2))
           (n-bind again)
           (n-cbz n-x15 yes)
           (n-e (arm-ldur-w n-x10 n-x13 4))
           (n-e (arm-ldur-w n-x11 n-x14 4))
           (n-e (arm-cmp n-x10 n-x11))
           (n-b-cond ar-ne no)
           (n-e (arm-add-imm n-x13 n-x13 4))
           (n-e (arm-add-imm n-x14 n-x14 4))
           (n-e (arm-sub-imm n-x15 n-x15 1))
           (n-b again)
           (ar-yes-no yes no end))))
      ((string=? what "modulo")
       (let ((end (n-label)))
         (begin
           (n-e (arm-orr n-x13 1 2))
           (n-e (arm-tst-low n-x13 3))
           (n-b-cond ar-ne slow)
           (n-cbz 2 slow)
           (n-e (arm-sdiv n-x13 1 2))
           (n-e (arm-msub a-result n-x13 2 1))
           (n-cbz a-result end)
           (n-e (arm-eor n-x14 a-result 2))
           (n-e (arm-cmp-imm n-x14 0))
           (n-b-cond ar-ge end)
           (n-e (arm-add a-result a-result 2))
           (n-bind end))))
      ;; `inline`'s: a pair from the heap's free space, `top` bumped by
      ;; two words; the pair's address, and, off the path from `top` to
      ;; the result, its tag added to the base first.
      ((string=? what "cons")
       (begin
         (n-e (arm-ldr n-w n-st a-st-words))
         (n-e (arm-ldr n-x13 n-st a-st-top))
         (n-e (arm-ldr n-x14 n-x13 0))
         (n-e (arm-ldr n-x15 n-st a-st-alloc-limit))
         (n-e (arm-add-imm n-x16 n-x14 2))
         (n-e (arm-cmp n-x16 n-x15))
         (n-b-cond ar-hi slow)
         (n-e (arm-add-lsl n-x11 n-w n-x14 3))
         (n-e (arm-add-imm n-w n-w n-tag-pair))
         (n-e (arm-stp 1 2 n-x11 0))
         (n-e (arm-str n-x16 n-x13 0))
         (n-e (arm-add-lsl a-result n-w n-x14 3))))
      ;; A string's length is its suffix's first word; its characters
      ;; follow, two to a word.
      ((string=? what "string-length")
       (begin
         (n-e (arm-mov n-x11 1))
         (n-e (arm-ldur n-x15 n-x11 -4))
         (n-e (arm-add-lsl a-result a-xzr n-x15 3))))
      ((string=? what "string-ref")
       (begin
         (n-e (arm-mov n-x11 1))
         (n-e (arm-ldur n-x15 n-x11 -4))
         (n-e (arm-asr-imm n-x13 2 3))
         (n-e (arm-cmp n-x13 n-x15))
         (n-b-cond ar-hs slow)
         (n-e (arm-add-lsl n-x14 n-x11 n-x13 2))
         (n-e (arm-ldur-w n-x15 n-x14 4))
         (n-value n-x16 a-char0)
         (n-e (arm-add-lsl a-result n-x16 n-x15 8))))
      ;; A pair in a region's current chunk, if the handle has a slot in
      ;; the heap's table and the chunk has room: its fill bumped by two
      ;; words.
      ((string=? what "rcons")
       (begin
         (n-e (arm-tst-low 1 3))
         (n-b-cond ar-ne slow)
         (n-e (arm-cmp-imm 1 (* 8 a-region-slots)))
         (n-b-cond ar-hs slow)
         (n-e (arm-ldr n-x13 n-st a-st-regions))
         (n-e (arm-add-lsl n-x13 n-x13 1 1))
         (n-e (arm-ldp n-x14 n-x15 n-x13 0))
         (n-e (arm-add-imm n-x16 n-x14 2))
         (n-e (arm-cmp n-x16 n-x15))
         (n-b-cond ar-hi slow)
         (n-e (arm-ldr n-x15 n-st a-st-words))
         (n-e (arm-add-lsl n-x11 n-x15 n-x14 3))
         (n-e (arm-stp 2 3 n-x11 0))
         (n-e (arm-str n-x16 n-x13 0))
         (n-e (arm-add-imm a-result n-x11 n-tag-pair))))
      ;; Type tests: `shape_test`'s, of `REG1`.
      (else (if (ar-shape-test 1 (ar-shape-name what) slow) #u #u)))))

;; What `prim`, `lambda` or `cellular` does inline, if anything ("").
(define ar-inline-name (subr pure (int int int) string)
  (lambda (op k0 count)
    (cond
      ((= op rop-lambda) "closure")
      ((= op rop-cellular)
       (cond ((and (= count 2) (= k0 routine-cons)) "cons")
             ((and (= count 2) (= k0 routine-field-ref)) "field@")
             (else "")))
      ((not (= op rop-prim)) "")
      (else
       (let ((p (a-prim-name k0)))
         (cond
           ((= count 1)
            (cond ((string=? p "string-length") "string-length")
                  ((string=? p "%bloblet-fields") "fields")
                  ((string=? p "char-whitespace?") "whitespace")
                  ((string=? p "char-numeric?") "numeric")
                  ((string=? p "%symbol-hash") "symbol-hash")
                  ((string=? p "%fx26-fixnum?") "fixnum?")
                  ((string=? p "char?") "char?")
                  ((string=? p "boolean?") "boolean?")
                  ((string=? p "symbol?") "symbol?")
                  ((string=? p "string?") "string?")
                  ((string=? p "pair?") "pair?")
                  ((string=? p "%fx26-bitwise-not") "bit-not")
                  ((string=? p "exact-integer?") "exact-integer?")
                  ((string=? p "%fx26-array?") "array?")
                  ((string=? p "%fx26-f32?") "f32?")
                  ((string=? p "%fx26-box?") "box?")
                  ((string=? p "%fx26-sum?") "sum?")
                  ((string=? p "%fx26-product?") "product?")
                  ((string=? p "%fx26-procedure?") "procedure?")
                  ((string=? p "%make-box") "box")
                  ((string=? p "%make-frozen") "frozen")
                  ((string=? p "%make-bloblet") "bloblet")
                  (else "")))
           ((= count 2)
            (cond ((string=? p "string-ref") "string-ref")
                  ((string=? p "%fx26-bitwise-and") "bit-and")
                  ((string=? p "%fx26-bitwise-ior") "bit-ior")
                  ((string=? p "%fx26-bitwise-xor") "bit-xor")
                  ((string=? p "%fx26-char-in?") "char-in")
                  ((string=? p "string=?") "string=")
                  ((string=? p "modulo") "modulo")
                  ((string=? p "%region-new") "rnew")
                  ((string=? p "%region-closure") "region-closure")
                  ((string=? p "%make-frozen") "frozen")
                  ((string=? p "%make-bloblet") "bloblet")
                  (else "")))
           ((= count 3)
            (cond ((string=? p "%region-cons") "rcons")
                  ((string=? p "%bloblet-set!") "field!")
                  ((and (<= count a-regs) (string=? p "%region-closure")) "region-closure")
                  ((string=? p "%make-frozen") "frozen")
                  ((string=? p "%make-bloblet") "bloblet")
                  (else "")))
           (else
            (cond ((and (>= count 2) (<= count a-regs) (string=? p "%region-closure"))
                   "region-closure")
                  ((and (>= count 1) (string=? p "%make-frozen")) "frozen")
                  ((and (>= count 1) (string=? p "%make-bloblet")) "bloblet")
                  (else "")))))))))
)))
