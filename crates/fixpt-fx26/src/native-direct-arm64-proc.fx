;;; The procedure the native convention's compiler to arm64 written in
;;; FX-26 is compiling: what `procedure` (`fixpt-native/src/direct.rs`)
;;; knows of it before and while it makes its code, as state its other
;;; files share (`native-direct-arm64-ops.fx`, its instructions,
;;; `-prims.fx`, the primitives', and `native-direct-arm64.fx`, the rest):
;;; what Rust gave of it (`FxRequest`, `direct/fx.rs`), its cells, the
;;; analysis `procedure` makes first, its code bloblet's fields, the version
;;; being made, and what is placed after the code. x86_64's
;;; (`native-direct-x64-proc.fx`), its steps the Rust names with `adp-`
;;; before them.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the layouts, the assembler and
;;; the analysis of representations (`native-reps.fx`).

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (arm-direct-types (load-module "fx26:native-direct-arm64-types.fx"))
       (direct-layout-types (load-module "fx26:native-direct-arm64-layout-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx")))
  (lambda ((dl (select direct-layout-types native-direct-arm64-layout-sig))
           (layout (select layout-types layout-sig))
           (asm (select arm-direct-types native-direct-arm64-asm-sig))
           (reps (select direct-types native-reps-sig)))
    (module
(hide (include direct-types) (include arm-direct-types))
(hide (include dl) (include layout) (include asm) (include reps))

;; `b`, 64 bits, as signed.
(define adp-signed (subr pure (int) int)
  (lambda (b) (if (>= b 9223372036854775808) (- b 18446744073709551616) b)))

;;; ------------------------------------------------------------ what Rust gave

;; Its name; the messages a failure noted at an instruction names; and by
;; cell (`FxRequest`): its bits, the number of the heap value it is (-1 for
;; none), and what Rust found for the instruction there (`kind`, `a`, `b`,
;; and `c`, a global's count of writes, as bits).
(define adp-name (ref string @k) (new ""))
(define adp-errors (ref da-strings @k) (new nil))
(define adp-bits (ref da-ints @k) (new (make-array 1 0)))
(define adp-ids (ref da-ints @k) (new (make-array 1 0)))
(define adp-kind (ref da-ints @k) (new (make-array 1 0)))
(define adp-a (ref da-ints @k) (new (make-array 1 0)))
(define adp-b (ref da-ints @k) (new (make-array 1 0)))
(define adp-c (ref da-ints @k) (new (make-array 1 0)))
;; `FxRequest::head`: the call-outs' count so far, the overflow's info with
;; and without the closure, and the number of the cellular word compiled
;; (its SSE4.1 is x86_64's).
(define adp-info-captures (ref int @k) (new 0))
(define adp-info (ref int @k) (new 0))
(define adp-word-id (ref int @k) (new 0))

;; The procedure's cells as compiled (`register_cells`: a slot of an `f64`
;; and something else split), how many, and where each instruction starts
;; (by index, as `starts`), with each cell's instruction's index (-1 for an
;; operand's).
(define adp-cells (ref nr-cells @k) (new (product (1 (make-array 1 0)) (2 (make-array 1 #f)))))
(define adp-n (ref int @k) (new 0))
(define adp-starts (ref da-ints @k) (new (make-array 1 0)))
(define adp-si-at (ref da-ints @k) (new (make-array 1 0)))

(define adp-si-of (subr da-reads (int) int) (lambda (i) (array-ref (get adp-si-at) i)))
(define adp-ns (subr da-reads () int) (lambda () (array-length (get adp-starts))))
(define adp-start (subr da-reads (int) int) (lambda (si) (array-ref (get adp-starts) si)))
;; Cell `i` as a fixnum, and whether it is one.
(define adp-fix (subr da-reads (int) int) (lambda (i) (array-ref (extract (get adp-cells) 1) i)))
(define adp-fix? (subr da-reads (int) bool) (lambda (i) (array-ref (extract (get adp-cells) 2) i)))
;; The instruction at cell `i`, by number, and operand `j` of it, as a
;; fixnum and as bits.
(define adp-op (subr da-reads (int) int) (lambda (i) (adp-fix i)))
(define adp-o (subr da-reads (int int) int) (lambda (i j) (adp-fix (+ i (+ 1 j)))))
(define adp-ob (subr da-reads (int int) int)
  (lambda (i j) (array-ref (get adp-bits) (+ i (+ 1 j)))))
(define adp-oid (subr da-reads (int int) int)
  (lambda (i j) (array-ref (get adp-ids) (+ i (+ 1 j)))))
;; Whether operand `j` of the instruction at `i` is a fixnum, or an
;; immediate (a fixnum or bits tagged 3), which needs no field.
(define adp-ofix? (subr da-reads (int int) bool) (lambda (i j) (adp-fix? (+ i (+ 1 j)))))
(define adp-oimm? (subr da-reads (int int) bool)
  (lambda (i j) (or (adp-ofix? i j) (= (bitwise-and (adp-ob i j) 7) 3))))
;; Where a branch at `i` goes: its last operand counts from past it.
(define adp-branch-to (subr da-reads (int) int)
  (lambda (i) (let ((n (d-operands (adp-op i)))) (+ (+ i (+ 1 n)) (adp-fix (+ i n))))))
(define adp-branch? (subr pure (int) bool)
  (lambda (op)
    (or (= op rop-branch) (= op rop-branchf) (= op rop-brancht) (= op rop-global-guard))))

;; Whether bit `k` of `mask` is set.
(define adp-bit? (subr pure (int int) bool)
  (lambda (mask k) (= (bitwise-and (arithmetic-shift mask (- 0 k)) 1) 1)))
;; Bit `k` as a mask, none past 63 (`checked_shl`).
(define adp-bit (subr pure (int) int)
  (lambda (k) (if (and (>= k 0) (< k 64)) (arithmetic-shift 1 k) 0)))

;; Why it cannot be compiled, as `decline` says it.
(define adp-decline (subr da-assembles (string) unit)
  (lambda (what)
    (ada-fail (string-append "`" (string-append (get adp-name) (string-append "`: " what))))))

;;; ------------------------------------------------------------ the analysis

;; Whether it has a frame (its slots, -1 for none), calls, or reads its
;; closure; what a branch goes back to, and goes to; and whether its frame
;; is pushed where each instruction starts.
(define adp-frame (ref int @k) (new -1))
(define adp-calls (ref bool @k) (new #f))
(define adp-captures (ref bool @k) (new #f))
(define adp-back-to (ref da-bools @k) (new (make-array 1 #f)))
(define adp-target (ref da-bools @k) (new (make-array 1 #f)))
(define adp-framed (ref da-bools @k) (new (make-array 1 #f)))
;; Its raw slots, how many values, the parameters it takes raw, and each
;; known callee's, by instruction.
(define adp-raw (ref da-bools @k) (new (make-array 0 #f)))
(define adp-values (ref int @k) (new 0))
(define adp-params (ref int @k) (new 0))
(define adp-callees (ref da-ints @k) (new (make-array 1 0)))
;; Each slot's place in the frame, and its value's index (-1 for a raw
;; one's); whether the frame is too large for a map; its fields; its size
;; (-1 for none); where it keeps the code bloblet and the closure.
(define adp-slot-off (ref da-ints @k) (new (make-array 0 0)))
(define adp-value-index (ref da-ints @k) (new (make-array 0 0)))
(define adp-unmapped (ref bool @k) (new #f))
(define adp-nfields (ref int @k) (new 0))
(define adp-size (ref int @k) (new -1))
(define adp-self-slot (ref int @k) (new -1))
(define adp-clo-slot (ref int @k) (new -1))
;; By instruction: the slots live after it (a mask); whether an element or
;; value there is taken raw (`raw_refs`); what registers are live where it
;; starts (`reps::live_in`, a mask).
(define adp-live-out (ref da-ints @k) (new (make-array 1 0)))
(define adp-raw-refs (ref da-bools @k) (new (make-array 1 #f)))
(define adp-live (ref da-ints @k) (new (make-array 1 0)))
;; Whether it has a fixnum version (an `int` operation in it).
(define adp-has-int (ref bool @k) (new #f))

;; The instructions, each `f` of its cell, in order.
(define adp-each (subr da-assembles ((subr da-assembles (int) unit) int) unit)
  (lambda (f si)
    (if (= si (adp-ns)) #u (begin (f (adp-start si)) (adp-each f (+ si 1))))))

;; `starts`, `back_to`, `target`, the frame, calls and captures.
(define adp-scan (subr da-assembles () unit)
  (lambda ()
    (let ((n (get adp-n)))
      (begin
        (set adp-starts (nr-starts (get adp-cells)))
        (set adp-si-at (the da-ints (make-array (+ n 1) -1)))
        (set adp-back-to (the da-bools (make-array (+ n 1) #f)))
        (set adp-target (the da-bools (make-array (+ n 1) #f)))
        (set adp-frame -1)
        (set adp-calls #f)
        (set adp-captures #f)
        (letrec ((at (subr da-assembles (int) unit)
                   (lambda (si)
                     (if (= si (adp-ns))
                         #u
                         (begin (array-set! (get adp-si-at) (adp-start si) si) (at (+ si 1)))))))
          (at 0))
        (adp-each
         (lambda (i)
           (let ((op (adp-op i)))
             (cond ((adp-branch? op)
                    (let ((to (adp-branch-to i)))
                      (begin (array-set! (get adp-target) to #t)
                             (if (<= to i) (array-set! (get adp-back-to) to #t) #u))))
                   ((= op rop-save) (set adp-frame (adp-o i 0)))
                   ((or (= op rop-invoke) (or (= op rop-tailinvoke) (= op rop-invokeself)))
                    (set adp-calls #t))
                   ((= op rop-lexical) (set adp-captures #t))
                   (else #u))))
         0)))))

;; `framed`: after `save`, pushed; after `pop`, not; where a branch goes,
;; as at the branch (the first branch there to say).
(define adp-frames (subr da-assembles () unit)
  (lambda ()
    (let ((known (the da-ints (make-array (+ (get adp-n) 1) -1))))
      (letrec ((go (subr da-assembles (int bool) unit)
                 (lambda (si was)
                   (if (= si (adp-ns))
                       #u
                       (let* ((i (adp-start si)) (op (adp-op i))
                              (cur (if (>= (array-ref known i) 0) (= (array-ref known i) 1) was)))
                         (begin
                           (array-set! (get adp-framed) i cur)
                           (if (and (adp-branch? op) (< (array-ref known (adp-branch-to i)) 0))
                               (array-set! known (adp-branch-to i) (if cur 1 0))
                               #u)
                           (go (+ si 1)
                               (cond ((= op rop-save) #t) ((= op rop-pop) #f) (else cur)))))))))
        (begin
          (set adp-framed (the da-bools (make-array (+ (get adp-n) 1) #f)))
          (go 0 #f))))))

;; Where raw slot `r` is in the frame: after the values, the code bloblet
;; and the closure.
(define adp-raw-off (subr da-reads (int) int)
  (lambda (r) (+ 24 (* 8 (+ (get adp-values) (+ 2 r))))))
;; The frame as `procedure` lays it out: the slots' places, the values'
;; indexes, its size, and where its code bloblet and closure are.
(define adp-layout (subr da-assembles () unit)
  (lambda ()
    (let* ((raw (get adp-raw)) (m (array-length raw)))
      (letrec ((count (subr da-reads (int int) int)
                 (lambda (k acc)
                   (if (= k m) acc (count (+ k 1) (if (array-ref raw k) acc (+ acc 1))))))
               (place (subr da-assembles (int int int) unit)
                 (lambda (k v r)
                   (cond ((= k m) #u)
                         ((array-ref raw k)
                          (begin
                            (array-set! (get adp-slot-off) k (adp-raw-off r))
                            (array-set! (get adp-value-index) k -1)
                            (place (+ k 1) v (+ r 1))))
                         (else
                          (begin
                            (array-set! (get adp-slot-off) k (+ 24 (* 8 v)))
                            (array-set! (get adp-value-index) k v)
                            (place (+ k 1) (+ v 1) r)))))))
        (begin
          (set adp-values (count 0 0))
          (set adp-slot-off (the da-ints (make-array m 0)))
          (set adp-value-index (the da-ints (make-array m -1)))
          (place 0 0 0)
          (let ((f (get adp-frame)) (values (get adp-values)))
            (begin
              (set adp-unmapped (and (>= f 0) (> (+ values 2) d-map-bits)))
              (set adp-nfields (+ values 5))
              (set adp-size (if (< f 0) -1 (* 16 (quotient (+ (+ 32 (* 8 (+ f 2))) 15) 16))))
              (set adp-self-slot (if (< f 0) -1 (+ 24 (* 8 values))))
              (set adp-clo-slot (if (< f 0) -1 (+ 24 (* 8 (+ values 1))))))))))))

;; The values of the slots in `mask` (bit `k` for slot `k`), as a mask of
;; their values' indexes.
(define adp-value-mask (subr da-reads (int) int)
  (lambda (mask)
    (let ((m (array-length (get adp-raw))))
      (letrec ((go (subr da-reads (int int) int)
                 (lambda (k acc)
                   (if (or (= k m) (>= k 64))
                       acc
                       (let ((v (array-ref (get adp-value-index) k)))
                         (go (+ k 1)
                             (if (and (>= v 0) (adp-bit? mask k))
                                 (bitwise-ior acc (arithmetic-shift 1 v))
                                 acc)))))))
        (go 0 0)))))
;; The stack map for a site whose live slots are `live`.
(define adp-map-word (subr da-reads (int) int)
  (lambda (live)
    (if (get adp-unmapped)
        (- 0 (get adp-nfields))
        (bitwise-ior
         (bitwise-ior (adp-value-mask live) (arithmetic-shift 1 (get adp-values)))
         (bitwise-ior (if (get adp-captures) (arithmetic-shift 1 (+ (get adp-values) 1)) 0)
                      (arithmetic-shift (get adp-nfields) d-map-bits))))))

;; Which slots are live after each instruction: uses, definitions and
;; successors, and the backward fixpoint (`procedure`'s pass).
(define adp-slot-liveness (subr da-assembles () unit)
  (lambda ()
    (let* ((ns (adp-ns))
           (uses (the da-ints (make-array ns 0)))
           (defs (the da-ints (make-array ns 0)))
           (succ1 (the da-ints (make-array ns -1)))
           (succ2 (the da-ints (make-array ns -1)))
           (live-in (the da-ints (make-array ns 0)))
           (live-out (the da-ints (make-array ns 0))))
      (letrec ((facts (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (let* ((i (adp-start si))
                              (op (adp-op i))
                              (to (if (adp-branch? op) (adp-si-of (adp-branch-to i)) -1)))
                         (begin
                           (cond ((= op rop-stack) (array-set! uses si (adp-bit (adp-o i 0))))
                                 ((= op rop-load) (array-set! uses si (adp-bit (adp-o i 1))))
                                 ((= op rop-setstk) (array-set! defs si (adp-bit (adp-o i 0))))
                                 ((= op rop-store) (array-set! defs si (adp-bit (adp-o i 1))))
                                 (else #u))
                           (cond ((or (= op rop-return) (= op rop-tailinvoke)) #u)
                                 ((= op rop-branch) (array-set! succ1 si to))
                                 ((adp-branch? op)
                                  (begin (array-set! succ1 si (+ si 1)) (array-set! succ2 si to)))
                                 ((< (+ si 1) ns) (array-set! succ1 si (+ si 1)))
                                 (else #u))
                           (facts (+ si 1)))))))
               (in-of (subr da-reads (int) int)
                 (lambda (t) (if (< t 0) 0 (array-ref live-in t))))
               (pass (subr da-assembles (int bool) bool)
                 (lambda (si changed)
                   (if (< si 0)
                       changed
                       (let* ((out (bitwise-ior (in-of (array-ref succ1 si))
                                                (in-of (array-ref succ2 si))))
                              (inn (bitwise-ior (bitwise-and out (bitwise-not (array-ref defs si)))
                                                (array-ref uses si))))
                         (if (and (= out (array-ref live-out si)) (= inn (array-ref live-in si)))
                             (pass (- si 1) changed)
                             (begin (array-set! live-out si out) (array-set! live-in si inn)
                                    (pass (- si 1) #t)))))))
               (fix (subr da-assembles () unit)
                 (lambda () (if (pass (- ns 1) #f) (fix) #u))))
        (begin (facts 0) (fix) (set adp-live-out live-out))))))

;; Whether an `op2` or `op2imm` at `i` is of an `int` routine.
(define adp-int-op? (subr da-reads (int) bool)
  (lambda (i)
    (let ((op (adp-op i)))
      (and (or (= op rop-op2) (= op rop-op2imm)) (nr-int-routine? (adp-o i 0))))))

;; The analysis, before any code, or why not: the frame's size, its raw
;; slots and values, the parameters and callees, and the passes.
(define adp-analyse (subr da-assembles () unit)
  (lambda ()
    (begin
      (adp-scan)
      (adp-frames)
      ;; At most `MOST_FRAME`, 16 KiB: a quarter of the stack's slack.
      (if (and (>= (get adp-frame) 0) (> (+ 32 (* 8 (+ (get adp-frame) 2))) 16384))
          (adp-decline "a frame too large")
          (let ((starts (get adp-starts)) (cells (get adp-cells)))
            (begin
              (set adp-raw (if (< (get adp-frame) 0)
                              (the da-bools (make-array 0 #f))
                              (nr-raw-slots cells starts (get adp-frame))))
              (adp-layout)
              (set adp-params (nr-raw-params cells starts (get adp-raw)))
              (set adp-callees (the da-ints (make-array (adp-ns) 0)))
              (letrec ((callee (subr da-assembles (int) unit)
                         (lambda (si)
                           (if (= si (adp-ns))
                               #u
                               (let* ((i (adp-start si)) (op (adp-op i)))
                                 (begin
                                   (if (or (= op rop-invoke) (= op rop-tailinvoke))
                                       (array-set! (get adp-callees) si (array-ref (get adp-a) i))
                                       #u)
                                   (callee (+ si 1))))))))
                (callee 0))
              (adp-slot-liveness)
              (set adp-raw-refs (nr-raw-refs cells starts (get adp-raw)))
              (set adp-live (nr-live-in cells starts (get adp-raw)))
              (set adp-has-int #f)
              (adp-each (lambda (i) (if (adp-int-op? i) (set adp-has-int #t) #u)) 0)))))))

;;; ------------------------------------------------------------ fields

;; Its code bloblet's fields, as `direct/fx.rs` reads them (`field_of`),
;; newest first, and how many.
(define adp-fields (ref da-bytes @k) (new nil))
(define adp-nfields-made (ref int @k) (new 0))

;; The field holding `f`: its index from 1, shared with an equal one.
(define adp-field (subr da-assembles (int) int)
  (lambda (f)
    (letrec ((find (subr da-reads (da-bytes int) int)
               (lambda (fs k)
                 (cond ((null? fs) -1) ((= (car fs) f) k) (else (find (cdr fs) (- k 1)))))))
      (let ((k (find (get adp-fields) (get adp-nfields-made))))
        (if (> k 0)
            k
            (begin (set adp-fields (cons f (get adp-fields)))
                   (set adp-nfields-made (+ 1 (get adp-nfields-made)))
                   (get adp-nfields-made)))))))
;; The fields as `field_of` codes them.
(define adp-myself int 0)
(define adp-code-of (subr pure (int) int) (lambda (q) (+ 1 (* 8 q))))
(define adp-const-of (subr pure (int) int) (lambda (id) (+ 2 (* 8 id))))
(define adp-cell-of (subr pure (int) int) (lambda (id) (+ 3 (* 8 id))))
(define adp-closure-of (subr pure (int int) int)
  (lambda (q free) (+ 4 (* 8 (+ q (* 1048576 free))))))
(define adp-callout-of (subr pure (int) int) (lambda (n) (+ 5 (* 8 n))))

;;; ------------------------------------------------------------ the version made

;; Each cell's label in the general version, and in the fixnum version;
;; whether the fixnum version is the one being made; each instruction's
;; registers where it starts and where it ends, in it.
(define adp-labels-g (ref da-ints @k) (new (make-array 1 0)))
(define adp-labels-f (ref da-ints @k) (new (make-array 1 0)))
(define adp-fast (ref bool @k) (new #f))
(define adp-reps-in (ref da-ints @k) (new (make-array 1 0)))
(define adp-reps-out (ref da-ints @k) (new (make-array 1 0)))
;; Where `RESULT`'s value is (`src`); the field a call just after this
;; instruction calls (`pending`, -1 for none); and the global it is bound
;; by, if bound (`bound`: its cell's field, -1 for none, and its count of
;; writes as compiled).
(define adp-src (ref int @k) (new 0))
(define adp-pending (ref int @k) (new -1))
(define adp-bound-cell (ref int @k) (new -1))
(define adp-bound-writes (ref int @k) (new 0))
;; The map last stored in the frame (`map_stored`), if one is.
(define adp-map-stored? (ref bool @k) (new #f))
(define adp-map-stored (ref int @k) (new 0))
;; What `RESULT` and REG1…REG8 hold of the frame (`held`, `TODO.md` §121):
;; a slot each, or -1; and which labels a way from the fixnum version goes
;; to (`entered`).
(define adp-held (ref da-ints @k) (new (make-array 9 -1)))
(define adp-entered (ref da-bools @k) (new (make-array 1 #f)))
;; The instruction being compiled, by index, which a join may move on.
(define adp-si (ref int @k) (new 0))
;; The entry, past its unboxing of raw parameters (`entry_checked`), and
;; where an abort's resumption is placed, if one is used.
(define adp-entry-checked (ref int @k) (new 0))
(define adp-resume-at (ref int @k) (new 0))
(define adp-uses-resume (ref bool @k) (new #f))

;; Cell `i`'s label in the version being made, and in the general one.
(define adp-label (subr da-reads (int) int)
  (lambda (i) (array-ref (if (get adp-fast) (get adp-labels-f) (get adp-labels-g)) i)))
(define adp-label-g (subr da-reads (int) int) (lambda (i) (array-ref (get adp-labels-g) i)))
;; Instruction `si`'s registers where it starts and ends.
(define adp-in (subr da-reads (int) int) (lambda (si) (array-ref (get adp-reps-in) si)))
(define adp-out (subr da-reads (int) int) (lambda (si) (array-ref (get adp-reps-out) si)))

;;; ------------------------------------------------------------ placed after

;; What is placed after the code: the ways in that unbox or test
;; (`edge_stubs`), the `int` operations' slow paths, the polls' ways out
;; (`NPoll`), the stack cache's overflows, the calls through cells whose
;; global was written (`cell_slows`), and the calls of what is not native
;; code (`foreign`); each newest first.
(define adp-edges (ref adp-edge-list @k) (new nil))
(define adp-int-slows (ref adp-int-slow-list @k) (new nil))
(define adp-polls (ref adp-poll-list @k) (new nil))
(define adp-overflows (ref adp-overflow-list @k) (new nil))
(define adp-cell-slows (ref adp-cell-slow-list @k) (new nil))
(define adp-foreign (ref adp-foreign-list @k) (new nil))

;; The next instruction if no branch goes to it (`joinable`), else -1.
(define adp-joinable (subr da-reads (int) int)
  (lambda (si)
    (if (>= (+ si 1) (adp-ns))
        -1
        (let ((j (adp-start (+ si 1)))) (if (array-ref (get adp-target) j) -1 j)))))
;; The way from instruction `from` to cell `to` (`edge`): its label, or a
;; stub's that first unboxes what is raw there and, in the fixnum version,
;; tests what is known there.
(define adp-edge (subr da-assembles (int int) int)
  (lambda (from to)
    (let ((t (adp-si-of to)))
      (let ((unbox (if (< t 0) (the da-bytes nil) (nr-unboxes (adp-out from) (adp-in t))))
            (check (if (or (< t 0) (not (get adp-fast)))
                       (the da-bytes nil)
                       (nr-checks (adp-out from) (adp-in t) (array-ref (get adp-live) t)))))
        (if (and (null? unbox) (null? check))
            (adp-label to)
            (let ((l (ada-label)))
              (begin
                (set adp-edges (cons (product (1 l) (2 unbox) (3 check) (4 (adp-label to))
                                             (5 (adp-label-g to)))
                                    (get adp-edges)))
                l)))))))

;; The branch just after the instruction at index `si`, where nothing
;; after it reads the boolean that instruction makes (`branch_on`): its
;; cell, or -1. A test there branches on the flags.
(define adp-result-live? (subr da-reads (int) bool)
  (lambda (si) (= (bitwise-and (array-ref (get adp-live) si) 1) 1)))
(define adp-branch-on (subr da-reads (int) int)
  (lambda (si)
    (let ((j (adp-joinable si)))
      (if (and (>= j 0)
               (or (= (adp-op j) rop-branchf) (= (adp-op j) rop-brancht))
               (or (>= (+ si 2) (adp-ns)) (not (adp-result-live? (+ si 2))))
               (not (adp-result-live? (adp-si-of (adp-branch-to j)))))
          j
          -1))))

;; Element `k` of `l`.
(define adp-nth (subr da-reads ((listof da-bytes @k) int) da-bytes)
  (lambda (l k) (if (= k 0) (car l) (adp-nth (cdr l) (- k 1)))))
(define adp-nth-int (subr da-reads (da-bytes int) int)
  (lambda (l k) (if (= k 0) (car l) (adp-nth-int (cdr l) (- k 1)))))
;; Cells `i` on of `vals`, as an array.
(define adp-array (subr da-assembles (da-bytes int) da-ints)
  (lambda (vals n)
    (let ((a (the da-ints (make-array n 0))))
      (letrec ((fill (subr da-assembles (da-bytes int) unit)
                 (lambda (vs i)
                   (if (null? vs) #u (begin (array-set! a i (car vs)) (fill (cdr vs) (+ i 1)))))))
        (begin (fill vals 0) a)))))

;; A procedure begins: what Rust gave of it (`FxRequest`, its lists in
;; order: `head`, `hi`, `lo`, `ids`, `kind`, `a`, `b`, `c_hi`, `c_lo`), its
;; cells split, and everything else as nothing has been made.
(define adp-begin (subr da-assembles (string (listof da-bytes @k) da-strings) unit)
  (lambda (name lists errors)
    (let* ((head (adp-nth lists 0)) (hi (adp-nth lists 1)) (lo (adp-nth lists 2))
           (n (list-length hi))
           (bits (the da-ints (make-array n 0)))
           (fix (the da-ints (make-array n 0)))
           (fix? (the da-bools (make-array n #f)))
           (c-hi (adp-array (adp-nth lists 7) n))
           (c-lo (adp-array (adp-nth lists 8) n))
           (c (the da-ints (make-array n 0))))
      (letrec ((cells (subr da-assembles (da-bytes da-bytes int) unit)
                 (lambda (hs ls i)
                   (if (null? hs)
                       #u
                       (let ((b (+ (* (car hs) 4294967296) (car ls))))
                         (begin
                           (array-set! bits i b)
                           (array-set! fix? i (= (bitwise-and b 7) 0))
                           (array-set! fix i (if (= (bitwise-and b 7) 0)
                                                 (arithmetic-shift (adp-signed b) -3)
                                                 0))
                           (array-set! c i (+ (* (array-ref c-hi i) 4294967296) (array-ref c-lo i)))
                           (cells (cdr hs) (cdr ls) (+ i 1))))))))
        (begin
          (ada-reset (adp-nth-int head 0))
          (set adp-name name)
          (set adp-errors errors)
          (set adp-info-captures (adp-nth-int head 1))
          (set adp-info (adp-nth-int head 2))
          (set adp-word-id (adp-nth-int head 4))
          (cells hi lo 0)
          (set adp-bits bits)
          (set adp-c c)
          (set adp-ids (adp-array (adp-nth lists 3) n))
          (set adp-kind (adp-array (adp-nth lists 4) n))
          (set adp-a (adp-array (adp-nth lists 5) n))
          (set adp-b (adp-array (adp-nth lists 6) n))
          (set adp-n n)
          (set adp-cells (nr-split-slots (product (1 fix) (2 fix?))))
          ;; cons-chain: in `@k`, which `list` would not be
          (set adp-fields (cons (adp-const-of (adp-nth-int head 4)) (cons adp-myself nil)))
          (set adp-nfields-made 2)
          (set adp-edges nil)
          (set adp-int-slows nil)
          (set adp-polls nil)
          (set adp-overflows nil)
          (set adp-cell-slows nil)
          (set adp-foreign nil)
          (set adp-uses-resume #f))))))
)))
