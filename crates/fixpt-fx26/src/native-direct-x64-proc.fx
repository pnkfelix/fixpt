;;; The procedure the native convention's compiler to x86_64 written in
;;; FX-26 is compiling: what `procedure_x64` (`fixpt-native/src/direct/
;;; x64.rs`) knows of it before and while it makes its code, as state its
;;; other files share (`native-direct-x64-ops.fx`, its instructions, and
;;; `native-direct-x64.fx`, the rest): what Rust gave of it (`FxRequest`,
;;; `direct/fx.rs`), its cells, the analysis `procedure_x64` makes first,
;;; its code bloblet's fields, the version being made, and what is placed
;;; after the code. Its steps have the Rust names, with `dp-` before them.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the layouts, the assembler and
;;; the analysis of representations (`native-reps.fx`).

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (direct-layout-types (load-module "fx26:native-direct-x64-layout-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx")))
  (lambda ((dl (select direct-layout-types native-direct-x64-layout-sig))
           (layout (select layout-types layout-sig))
           (asm (select direct-types native-direct-x64-asm-sig))
           (reps (select direct-types native-reps-sig)))
    (module
(hide (include direct-types))
(hide (include dl) (include layout) (include asm) (include reps))

;;; ------------------------------------------------------------ what Rust gave

;; Its name; the messages a failure noted at an instruction names; and by
;; cell (`FxRequest`): its bits, the number of the heap value it is (-1 for
;; none), and what Rust found for the instruction there (`kind`, `a`, `b`,
;; and `c`, a global's count of writes, as bits).
(define dp-name (ref string @k) (new ""))
(define dp-errors (ref da-strings @k) (new nil))
(define dp-bits (ref da-ints @k) (new (make-array 1 0)))
(define dp-ids (ref da-ints @k) (new (make-array 1 0)))
(define dp-kind (ref da-ints @k) (new (make-array 1 0)))
(define dp-a (ref da-ints @k) (new (make-array 1 0)))
(define dp-b (ref da-ints @k) (new (make-array 1 0)))
(define dp-c (ref da-ints @k) (new (make-array 1 0)))
;; `FxRequest::head`: the call-outs' count so far, the overflow's info with
;; and without the closure, whether the processor has SSE4.1, and the
;; number of the cellular word compiled.
(define dp-info-captures (ref int @k) (new 0))
(define dp-info (ref int @k) (new 0))
(define dp-sse41 (ref bool @k) (new #f))
(define dp-word-id (ref int @k) (new 0))

;; The procedure's cells as compiled (`register_cells`: a slot of an `f64`
;; and something else split), how many, and where each instruction starts
;; (by index, as `starts`), with each cell's instruction's index (-1 for an
;; operand's).
(define dp-cells (ref nr-cells @k) (new (product (1 (make-array 1 0)) (2 (make-array 1 #f)))))
(define dp-n (ref int @k) (new 0))
(define dp-starts (ref da-ints @k) (new (make-array 1 0)))
(define dp-si-at (ref da-ints @k) (new (make-array 1 0)))

(define dp-si-of (subr da-reads (int) int) (lambda (i) (array-ref (get dp-si-at) i)))
(define dp-ns (subr da-reads () int) (lambda () (array-length (get dp-starts))))
(define dp-start (subr da-reads (int) int) (lambda (si) (array-ref (get dp-starts) si)))
;; Cell `i` as a fixnum, and whether it is one.
(define dp-fix (subr da-reads (int) int) (lambda (i) (array-ref (extract (get dp-cells) 1) i)))
(define dp-fix? (subr da-reads (int) bool) (lambda (i) (array-ref (extract (get dp-cells) 2) i)))
;; The instruction at cell `i`, by number, and operand `j` of it, as a
;; fixnum and as bits.
(define dp-op (subr da-reads (int) int) (lambda (i) (dp-fix i)))
(define dp-o (subr da-reads (int int) int) (lambda (i j) (dp-fix (+ i (+ 1 j)))))
(define dp-ob (subr da-reads (int int) int) (lambda (i j) (array-ref (get dp-bits) (+ i (+ 1 j)))))
(define dp-oid (subr da-reads (int int) int) (lambda (i j) (array-ref (get dp-ids) (+ i (+ 1 j)))))
;; Whether operand `j` of the instruction at `i` is a fixnum, or an
;; immediate (a fixnum or bits tagged 3), which needs no field.
(define dp-ofix? (subr da-reads (int int) bool) (lambda (i j) (dp-fix? (+ i (+ 1 j)))))
(define dp-oimm? (subr da-reads (int int) bool)
  (lambda (i j) (or (dp-ofix? i j) (= (bitwise-and (dp-ob i j) 7) 3))))
;; Where a branch at `i` goes: its last operand counts from past it.
(define dp-branch-to (subr da-reads (int) int)
  (lambda (i) (let ((n (d-operands (dp-op i)))) (+ (+ i (+ 1 n)) (dp-fix (+ i n))))))
(define dp-branch? (subr pure (int) bool)
  (lambda (op)
    (or (= op rop-branch) (= op rop-branchf) (= op rop-brancht) (= op rop-global-guard))))

;; Whether bit `k` of `mask` is set.
(define dp-bit? (subr pure (int int) bool)
  (lambda (mask k) (= (bitwise-and (arithmetic-shift mask (- 0 k)) 1) 1)))
;; Bit `k` as a mask, none past 63 (`checked_shl`).
(define dp-bit (subr pure (int) int)
  (lambda (k) (if (and (>= k 0) (< k 64)) (arithmetic-shift 1 k) 0)))

;; Why it cannot be compiled, as `decline` says it.
(define dp-decline (subr da-assembles (string) unit)
  (lambda (what)
    (da-fail (string-append "`" (string-append (get dp-name) (string-append "`: " what))))))

;;; ------------------------------------------------------------ the analysis

;; Whether it has a frame (its slots, -1 for none), calls, or reads its
;; closure; what a branch goes back to, and goes to; and whether its frame
;; is pushed where each instruction starts.
(define dp-frame (ref int @k) (new -1))
(define dp-calls (ref bool @k) (new #f))
(define dp-captures (ref bool @k) (new #f))
(define dp-back-to (ref da-bools @k) (new (make-array 1 #f)))
(define dp-target (ref da-bools @k) (new (make-array 1 #f)))
(define dp-framed (ref da-bools @k) (new (make-array 1 #f)))
;; Its raw slots, how many values, the parameters it takes raw, and each
;; known callee's, by instruction.
(define dp-raw (ref da-bools @k) (new (make-array 0 #f)))
(define dp-values (ref int @k) (new 0))
(define dp-params (ref int @k) (new 0))
(define dp-callees (ref da-ints @k) (new (make-array 1 0)))
;; Each slot's place in the frame, and its value's index (-1 for a raw
;; one's); whether the frame is too large for a map; its fields; its size
;; (-1 for none); where it keeps the code bloblet and the closure.
(define dp-slot-off (ref da-ints @k) (new (make-array 0 0)))
(define dp-value-index (ref da-ints @k) (new (make-array 0 0)))
(define dp-unmapped (ref bool @k) (new #f))
(define dp-nfields (ref int @k) (new 0))
(define dp-size (ref int @k) (new -1))
(define dp-self-slot (ref int @k) (new -1))
(define dp-clo-slot (ref int @k) (new -1))
;; By instruction: the slots live after it (a mask); whether an element or
;; value there is taken raw (`raw_refs`); what registers are live where it
;; starts (`reps::live_in`, a mask).
(define dp-live-out (ref da-ints @k) (new (make-array 1 0)))
(define dp-raw-refs (ref da-bools @k) (new (make-array 1 #f)))
(define dp-live (ref da-ints @k) (new (make-array 1 0)))
;; Whether it has a fixnum version (an `int` operation in it).
(define dp-has-int (ref bool @k) (new #f))

;; The instructions, each `f` of its cell, in order.
(define dp-each (subr da-assembles ((subr da-assembles (int) unit) int) unit)
  (lambda (f si)
    (if (= si (dp-ns)) #u (begin (f (dp-start si)) (dp-each f (+ si 1))))))

;; `starts`, `back_to`, `target`, the frame, calls and captures.
(define dp-scan (subr da-assembles () unit)
  (lambda ()
    (let ((n (get dp-n)))
      (begin
        (set dp-starts (nr-starts (get dp-cells)))
        (set dp-si-at (the da-ints (make-array (+ n 1) -1)))
        (set dp-back-to (the da-bools (make-array (+ n 1) #f)))
        (set dp-target (the da-bools (make-array (+ n 1) #f)))
        (set dp-frame -1)
        (set dp-calls #f)
        (set dp-captures #f)
        (letrec ((at (subr da-assembles (int) unit)
                   (lambda (si)
                     (if (= si (dp-ns))
                         #u
                         (begin (array-set! (get dp-si-at) (dp-start si) si) (at (+ si 1)))))))
          (at 0))
        (dp-each
         (lambda (i)
           (let ((op (dp-op i)))
             (cond ((dp-branch? op)
                    (let ((to (dp-branch-to i)))
                      (begin (array-set! (get dp-target) to #t)
                             (if (<= to i) (array-set! (get dp-back-to) to #t) #u))))
                   ((= op rop-save) (set dp-frame (dp-o i 0)))
                   ((or (= op rop-invoke) (or (= op rop-tailinvoke) (= op rop-invokeself)))
                    (set dp-calls #t))
                   ((= op rop-lexical) (set dp-captures #t))
                   (else #u))))
         0)))))

;; `framed`: after `save`, pushed; after `pop`, not; where a branch goes,
;; as at the branch (the first branch there to say).
(define dp-frames (subr da-assembles () unit)
  (lambda ()
    (let ((known (the da-ints (make-array (+ (get dp-n) 1) -1))))
      (letrec ((go (subr da-assembles (int bool) unit)
                 (lambda (si was)
                   (if (= si (dp-ns))
                       #u
                       (let* ((i (dp-start si)) (op (dp-op i))
                              (cur (if (>= (array-ref known i) 0) (= (array-ref known i) 1) was)))
                         (begin
                           (array-set! (get dp-framed) i cur)
                           (if (and (dp-branch? op) (< (array-ref known (dp-branch-to i)) 0))
                               (array-set! known (dp-branch-to i) (if cur 1 0))
                               #u)
                           (go (+ si 1)
                               (cond ((= op rop-save) #t) ((= op rop-pop) #f) (else cur)))))))))
        (begin
          (set dp-framed (the da-bools (make-array (+ (get dp-n) 1) #f)))
          (go 0 #f))))))

;; Where raw slot `r` is in the frame: after the values, the code bloblet
;; and the closure.
(define dp-raw-off (subr da-reads (int) int) (lambda (r) (+ 24 (* 8 (+ (get dp-values) (+ 2 r))))))
;; The frame as `procedure` lays it out: the slots' places, the values'
;; indexes, its size, and where its code bloblet and closure are.
(define dp-layout (subr da-assembles () unit)
  (lambda ()
    (let* ((raw (get dp-raw)) (m (array-length raw)))
      (letrec ((count (subr da-reads (int int) int)
                 (lambda (k acc)
                   (if (= k m) acc (count (+ k 1) (if (array-ref raw k) acc (+ acc 1))))))
               (place (subr da-assembles (int int int) unit)
                 (lambda (k v r)
                   (cond ((= k m) #u)
                         ((array-ref raw k)
                          (begin
                            (array-set! (get dp-slot-off) k (dp-raw-off r))
                            (array-set! (get dp-value-index) k -1)
                            (place (+ k 1) v (+ r 1))))
                         (else
                          (begin
                            (array-set! (get dp-slot-off) k (+ 24 (* 8 v)))
                            (array-set! (get dp-value-index) k v)
                            (place (+ k 1) (+ v 1) r)))))))
        (begin
          (set dp-values (count 0 0))
          (set dp-slot-off (the da-ints (make-array m 0)))
          (set dp-value-index (the da-ints (make-array m -1)))
          (place 0 0 0)
          (let ((f (get dp-frame)) (values (get dp-values)))
            (begin
              (set dp-unmapped (and (>= f 0) (> (+ values 2) d-map-bits)))
              (set dp-nfields (+ values 5))
              (set dp-size (if (< f 0) -1 (* 16 (quotient (+ (+ 32 (* 8 (+ f 2))) 15) 16))))
              (set dp-self-slot (if (< f 0) -1 (+ 24 (* 8 values))))
              (set dp-clo-slot (if (< f 0) -1 (+ 24 (* 8 (+ values 1))))))))))))

;; The values of the slots in `mask` (bit `k` for slot `k`), as a mask of
;; their values' indexes.
(define dp-value-mask (subr da-reads (int) int)
  (lambda (mask)
    (let ((m (array-length (get dp-raw))))
      (letrec ((go (subr da-reads (int int) int)
                 (lambda (k acc)
                   (if (or (= k m) (>= k 64))
                       acc
                       (let ((v (array-ref (get dp-value-index) k)))
                         (go (+ k 1)
                             (if (and (>= v 0) (dp-bit? mask k))
                                 (bitwise-ior acc (arithmetic-shift 1 v))
                                 acc)))))))
        (go 0 0)))))
;; The stack map for a site whose live slots are `live`.
(define dp-map-word (subr da-reads (int) int)
  (lambda (live)
    (if (get dp-unmapped)
        (- 0 (get dp-nfields))
        (bitwise-ior
         (bitwise-ior (dp-value-mask live) (arithmetic-shift 1 (get dp-values)))
         (bitwise-ior (if (get dp-captures) (arithmetic-shift 1 (+ (get dp-values) 1)) 0)
                      (arithmetic-shift (get dp-nfields) d-map-bits))))))

;; Which slots are live after each instruction: uses, definitions and
;; successors, and the backward fixpoint (`procedure`'s pass).
(define dp-slot-liveness (subr da-assembles () unit)
  (lambda ()
    (let* ((ns (dp-ns))
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
                       (let* ((i (dp-start si))
                              (op (dp-op i))
                              (to (if (dp-branch? op) (dp-si-of (dp-branch-to i)) -1)))
                         (begin
                           (cond ((= op rop-stack) (array-set! uses si (dp-bit (dp-o i 0))))
                                 ((= op rop-load) (array-set! uses si (dp-bit (dp-o i 1))))
                                 ((= op rop-setstk) (array-set! defs si (dp-bit (dp-o i 0))))
                                 ((= op rop-store) (array-set! defs si (dp-bit (dp-o i 1))))
                                 (else #u))
                           (cond ((or (= op rop-return) (= op rop-tailinvoke)) #u)
                                 ((= op rop-branch) (array-set! succ1 si to))
                                 ((dp-branch? op)
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
        (begin (facts 0) (fix) (set dp-live-out live-out))))))

;; Whether an `op2` or `op2imm` at `i` is of an `int` routine.
(define dp-int-op? (subr da-reads (int) bool)
  (lambda (i)
    (let ((op (dp-op i)))
      (and (or (= op rop-op2) (= op rop-op2imm)) (nr-int-routine? (dp-o i 0))))))

;; The analysis, before any code, or why not: the frame's size, its raw
;; slots and values, the parameters and callees, and the passes.
(define dp-analyse (subr da-assembles () unit)
  (lambda ()
    (begin
      (dp-scan)
      (dp-frames)
      (if (and (>= (get dp-frame) 0) (> (+ 32 (* 8 (+ (get dp-frame) 2))) 4080))
          (dp-decline "a frame too large")
          (let ((starts (get dp-starts)) (cells (get dp-cells)))
            (begin
              (set dp-raw (if (< (get dp-frame) 0)
                              (the da-bools (make-array 0 #f))
                              (nr-raw-slots cells starts (get dp-frame))))
              (dp-layout)
              (set dp-params (nr-raw-params cells starts (get dp-raw)))
              (set dp-callees (the da-ints (make-array (dp-ns) 0)))
              (letrec ((callee (subr da-assembles (int) unit)
                         (lambda (si)
                           (if (= si (dp-ns))
                               #u
                               (let* ((i (dp-start si)) (op (dp-op i)))
                                 (begin
                                   (if (or (= op rop-invoke) (= op rop-tailinvoke))
                                       (array-set! (get dp-callees) si (array-ref (get dp-a) i))
                                       #u)
                                   (callee (+ si 1))))))))
                (callee 0))
              (dp-slot-liveness)
              (set dp-raw-refs (nr-raw-refs cells starts (get dp-raw)))
              (set dp-live (nr-live-in cells starts (get dp-raw)))
              (set dp-has-int #f)
              (dp-each (lambda (i) (if (dp-int-op? i) (set dp-has-int #t) #u)) 0)))))))

;;; ------------------------------------------------------------ fields

;; Its code bloblet's fields, as `direct/fx.rs` reads them (`field_of`),
;; newest first, and how many.
(define dp-fields (ref da-bytes @k) (new nil))
(define dp-nfields-made (ref int @k) (new 0))

;; The field holding `f`: its index from 1, shared with an equal one.
(define dp-field (subr da-assembles (int) int)
  (lambda (f)
    (letrec ((find (subr da-reads (da-bytes int) int)
               (lambda (fs k)
                 (cond ((null? fs) -1) ((= (car fs) f) k) (else (find (cdr fs) (- k 1)))))))
      (let ((k (find (get dp-fields) (get dp-nfields-made))))
        (if (> k 0)
            k
            (begin (set dp-fields (cons f (get dp-fields)))
                   (set dp-nfields-made (+ 1 (get dp-nfields-made)))
                   (get dp-nfields-made)))))))
;; The fields as `field_of` codes them.
(define dp-myself int 0)
(define dp-code-of (subr pure (int) int) (lambda (q) (+ 1 (* 8 q))))
(define dp-const-of (subr pure (int) int) (lambda (id) (+ 2 (* 8 id))))
(define dp-cell-of (subr pure (int) int) (lambda (id) (+ 3 (* 8 id))))
(define dp-closure-of (subr pure (int int) int)
  (lambda (q free) (+ 4 (* 8 (+ q (* 1048576 free))))))

;;; ------------------------------------------------------------ the version made

;; Each cell's label in the general version, and in the fixnum version;
;; whether the fixnum version is the one being made; each instruction's
;; registers where it starts and where it ends, in it.
(define dp-labels-g (ref da-ints @k) (new (make-array 1 0)))
(define dp-labels-f (ref da-ints @k) (new (make-array 1 0)))
(define dp-fast (ref bool @k) (new #f))
(define dp-reps-in (ref da-ints @k) (new (make-array 1 0)))
(define dp-reps-out (ref da-ints @k) (new (make-array 1 0)))
;; Where `RESULT`'s value is (`src`); the field a call just after this
;; instruction calls (`pending`, -1 for none); and the global it is bound
;; by, if bound (`bound`: its cell's field, -1 for none, and its count of
;; writes as compiled).
(define dp-src (ref int @k) (new 0))
(define dp-pending (ref int @k) (new -1))
(define dp-bound-cell (ref int @k) (new -1))
(define dp-bound-writes (ref int @k) (new 0))
;; The map last stored in the frame (`map_stored`), if one is.
(define dp-map-stored? (ref bool @k) (new #f))
(define dp-map-stored (ref int @k) (new 0))
;; What `RESULT` and REG1…REG3 hold of the frame (`held`, `TODO.md` §121):
;; a slot each, or -1; and which labels a way from the fixnum version goes
;; to (`entered`).
(define dp-held (ref da-ints @k) (new (make-array 4 -1)))
(define dp-entered (ref da-bools @k) (new (make-array 1 #f)))
;; The instruction being compiled, by index, which a join may move on.
(define dp-si (ref int @k) (new 0))
;; The entry, past its unboxing of raw parameters (`entry_checked`), and
;; where an abort's resumption is placed, if one is used.
(define dp-entry-checked (ref int @k) (new 0))
(define dp-resume-at (ref int @k) (new 0))
(define dp-uses-resume (ref bool @k) (new #f))

;; Cell `i`'s label in the version being made, and in the general one.
(define dp-label (subr da-reads (int) int)
  (lambda (i) (array-ref (if (get dp-fast) (get dp-labels-f) (get dp-labels-g)) i)))
(define dp-label-g (subr da-reads (int) int) (lambda (i) (array-ref (get dp-labels-g) i)))
;; Instruction `si`'s registers where it starts and ends.
(define dp-in (subr da-reads (int) int) (lambda (si) (array-ref (get dp-reps-in) si)))
(define dp-out (subr da-reads (int) int) (lambda (si) (array-ref (get dp-reps-out) si)))

;;; ------------------------------------------------------------ placed after

;; What is placed after the code: the ways in that unbox or test
;; (`edge_stubs`), the `int` operations' slow paths, the polls' ways out
;; (`NPoll`), the stack cache's overflows, the calls through cells whose
;; global was written (`cell_slows`), and the calls of what is not native
;; code (`foreign`); each newest first.
(define dp-edges (ref dp-edge-list @k) (new nil))
(define dp-int-slows (ref dp-int-slow-list @k) (new nil))
(define dp-polls (ref dp-poll-list @k) (new nil))
(define dp-overflows (ref dp-overflow-list @k) (new nil))
(define dp-cell-slows (ref dp-cell-slow-list @k) (new nil))
(define dp-foreign (ref dp-foreign-list @k) (new nil))

;; The next instruction if no branch goes to it (`joinable`), else -1.
(define dp-joinable (subr da-reads (int) int)
  (lambda (si)
    (if (>= (+ si 1) (dp-ns))
        -1
        (let ((j (dp-start (+ si 1)))) (if (array-ref (get dp-target) j) -1 j)))))
;; The way from instruction `from` to cell `to` (`edge`): its label, or a
;; stub's that first unboxes what is raw there and, in the fixnum version,
;; tests what is known there.
(define dp-edge (subr da-assembles (int int) int)
  (lambda (from to)
    (let ((t (dp-si-of to)))
      (let ((unbox (if (< t 0) (the da-bytes nil) (nr-unboxes (dp-out from) (dp-in t))))
            (check (if (or (< t 0) (not (get dp-fast)))
                       (the da-bytes nil)
                       (nr-checks (dp-out from) (dp-in t) (array-ref (get dp-live) t)))))
        (if (and (null? unbox) (null? check))
            (dp-label to)
            (let ((l (da-label)))
              (begin
                (set dp-edges (cons (product (1 l) (2 unbox) (3 check) (4 (dp-label to))
                                             (5 (dp-label-g to)))
                                    (get dp-edges)))
                l)))))))

;; The branch just after the instruction at index `si`, where nothing
;; after it reads the boolean that instruction makes (`branch_on`): its
;; cell, or -1. A test there branches on the flags.
(define dp-result-live? (subr da-reads (int) bool)
  (lambda (si) (= (bitwise-and (array-ref (get dp-live) si) 1) 1)))
(define dp-branch-on (subr da-reads (int) int)
  (lambda (si)
    (let ((j (dp-joinable si)))
      (if (and (>= j 0)
               (or (= (dp-op j) rop-branchf) (= (dp-op j) rop-brancht))
               (or (>= (+ si 2) (dp-ns)) (not (dp-result-live? (+ si 2))))
               (not (dp-result-live? (dp-si-of (dp-branch-to j)))))
          j
          -1))))

;; Element `k` of `l`.
(define dp-nth (subr da-reads ((listof da-bytes @k) int) da-bytes)
  (lambda (l k) (if (= k 0) (car l) (dp-nth (cdr l) (- k 1)))))
(define dp-nth-int (subr da-reads (da-bytes int) int)
  (lambda (l k) (if (= k 0) (car l) (dp-nth-int (cdr l) (- k 1)))))
;; Cells `i` on of `vals`, as an array.
(define dp-array (subr da-assembles (da-bytes int) da-ints)
  (lambda (vals n)
    (let ((a (the da-ints (make-array n 0))))
      (letrec ((fill (subr da-assembles (da-bytes int) unit)
                 (lambda (vs i)
                   (if (null? vs) #u (begin (array-set! a i (car vs)) (fill (cdr vs) (+ i 1)))))))
        (begin (fill vals 0) a)))))

;; A procedure begins: what Rust gave of it (`FxRequest`, its lists in
;; order: `head`, `hi`, `lo`, `ids`, `kind`, `a`, `b`, `c_hi`, `c_lo`), its
;; cells split, and everything else as nothing has been made.
(define dp-begin (subr da-assembles (string (listof da-bytes @k) da-strings) unit)
  (lambda (name lists errors)
    (let* ((head (dp-nth lists 0)) (hi (dp-nth lists 1)) (lo (dp-nth lists 2))
           (n (list-length hi))
           (bits (the da-ints (make-array n 0)))
           (fix (the da-ints (make-array n 0)))
           (fix? (the da-bools (make-array n #f)))
           (c-hi (dp-array (dp-nth lists 7) n))
           (c-lo (dp-array (dp-nth lists 8) n))
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
                                                 (arithmetic-shift (da-signed b) -3)
                                                 0))
                           (array-set! c i (+ (* (array-ref c-hi i) 4294967296) (array-ref c-lo i)))
                           (cells (cdr hs) (cdr ls) (+ i 1))))))))
        (begin
          (da-reset (dp-nth-int head 0))
          (set dp-name name)
          (set dp-errors errors)
          (set dp-info-captures (dp-nth-int head 1))
          (set dp-info (dp-nth-int head 2))
          (set dp-sse41 (= (dp-nth-int head 3) 1))
          (set dp-word-id (dp-nth-int head 4))
          (cells hi lo 0)
          (set dp-bits bits)
          (set dp-c c)
          (set dp-ids (dp-array (dp-nth lists 3) n))
          (set dp-kind (dp-array (dp-nth lists 4) n))
          (set dp-a (dp-array (dp-nth lists 5) n))
          (set dp-b (dp-array (dp-nth lists 6) n))
          (set dp-n n)
          (set dp-cells (nr-split-slots (product (1 fix) (2 fix?))))
          ;; cons-chain: in `@k`, which `list` would not be
          (set dp-fields (cons (dp-const-of (dp-nth-int head 4)) (cons dp-myself nil)))
          (set dp-nfields-made 2)
          (set dp-edges nil)
          (set dp-int-slows nil)
          (set dp-polls nil)
          (set dp-overflows nil)
          (set dp-cell-slows nil)
          (set dp-foreign nil)
          (set dp-uses-resume #f))))))
)))
