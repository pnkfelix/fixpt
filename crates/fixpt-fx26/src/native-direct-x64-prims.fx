;;; The primitives, control and call-outs of the native convention's
;;; compiler to x86_64 written in FX-26: `procedure_x64`'s arms for
;;; `prim1`, `prim2`, `prim2imm`, `prim3imm`, control (`cellular` of a
;;; prompt, a mark, an abort, a capture or marks), and `prim`, `cellular`
;;; and `lambda` (`fixpt-native/src/direct/x64.rs`), with `pure_fast`, step
;;; for step, each `dq-` and its Rust name, over the procedure's state
;;; (`native-direct-x64-proc.fx`).
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder, the layouts, the
;;; assembler, the analysis, the raw values' and the heap's pieces, and the
;;; procedure.

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

(define dq-fld (subr pure (int) int) (lambda (k) (da-field-off k)))
;; The registers REG1…REG3 are in.
(define dq-r1 int 7)
(define dq-r2 int 6)
(define dq-r3 int 8)

;; Whether `s` ends with `end`.
(define dq-ends? (subr da-reads (string string) bool)
  (lambda (s end)
    (let ((n (string-length s)) (m (string-length end)))
      (and (>= n m) (string=? (substring s (- n m) n) end)))))
;; Strings joined.
(define dq-cat (subr pure (string string) string) (lambda (a b) (string-append a b)))
(define dq-cat4 (subr pure (string string string string) string)
  (lambda (a b c d) (string-append a (string-append b (string-append c d)))))
;; `RESULT` := the fixnum of the integer in `r`.
(define dq-fixnum-of (subr da-assembles (int) unit)
  (lambda (r) (begin (da-e (x86-shift-imm da-shl r 3)) (da-mov d-result r))))
;; Whether the element or value this instruction gives is taken raw.
(define dq-raw-ref? (subr da-reads () bool)
  (lambda () (array-ref (get dp-raw-refs) (- (get dp-si) 1))))
;; A primitive's call-out that never collects (`Callout::Pure`).
(define dq-pure (subr pure (int int) int) (lambda (p n) (da-co d-co-pure p n)))
;; Its value tested for a trap.
(define dq-checked (subr da-assembles () unit) (lambda () (da-trap-set)))

;;; ------------------------------------------------------------ `pure_fast`

;; `procedure`'s `pure_fast`, of what x86_64 has: the shape predicates,
;; fixnums' `*`, `quotient`, `modulo`, `arithmetic-shift`, bytevectors,
;; flat arrays, suffix refs and a bloblet's count of fields; the rest
;; `narrow_fast`'s. `RESULT` and `y` as they were on the way to `slow`.
(define dq-fixnums (subr da-assembles (int int) unit)
  (lambda (y slow)
    (begin (da-mov d-x13 d-result) (da-e (x86-alu da-or d-x13 y)) (da-e (x86-test-imm d-x13 7))
           (da-jcc da-c-ne slow))))
(define dq-pure-fast (subr da-assembles (string int int) bool)
  (lambda (name y slow)
    (let ((x d-result))
      (cond
        ((df-shape-fast name slow) #t)
        ;; A product in 61 bits: the 64-bit one did not overflow.
        ((string=? name "%fx26-mul")
         (begin (dq-fixnums y slow)
                (da-mov d-x14 y) (da-e (x86-shift-imm da-sar d-x14 3))
                (da-mov d-x13 x) (da-e (x86-imul d-x13 d-x14))
                (da-jcc da-c-o slow)
                (da-mov d-result d-x13)
                #t))
        ((string=? name "%fx26-remainder")
         (begin (dq-fixnums y slow)
                (da-e (x86-test y y)) (da-jcc da-c-e slow)
                (da-e (x86-cqo)) (da-e (x86-idiv y))
                (da-mov d-result d-rdx)
                #t))
        ((or (string=? name "%fx26-quotient") (string=? name "modulo"))
         (begin (dq-fixnums y slow)
                (da-e (x86-test y y)) (da-jcc da-c-e slow)
                (da-mov d-x16 x) (da-e (x86-cqo)) (da-e (x86-idiv y))
                (if (string=? name "%fx26-quotient") (dq-quotient slow) (dq-modulo y))
                #t))
        ((string=? name "%fx26-arithmetic-shift") (begin (dq-shift y slow) #t))
        ((or (string=? name "bytevector-length") (string=? name "string-length"))
         (begin (da-ld d-x13 x -4) (dq-fixnum-of d-x13) #t))
        ;; A character's code point, from its bits, the tag tested; a symbol's
        ;; hash, its first field; two strings' order.
        ((string=? name "char->integer")
         (begin (dq-char-point x d-x13 slow) (da-e (x86-shift-imm da-shl d-x13 3))
                (da-mov d-result d-x13) #t))
        ((string=? name "%symbol-hash") (begin (da-ld d-result x (dq-fld 3)) #t))
        ((string=? name "%fx26-string<?") (begin (dq-string-lt x y) #t))
        ;; A string's character at its index, 32 bits each after its length.
        ((string=? name "string-ref")
         (begin
           (da-e (x86-test-imm y 7)) (da-jcc da-c-ne slow)
           (da-ld d-x14 x -4)
           (da-mov d-x15 y) (da-e (x86-shift-imm da-sar d-x15 3))
           (da-e (x86-alu da-cmp d-x15 d-x14)) (da-jcc da-c-ae slow)
           (da-e (x86-load32-ix d-x16 x d-x15 4 4))
           (da-e (x86-shift-imm da-shl d-x16 8))
           (da-e (x86-alu-imm da-add d-x16 d-char0))
           (da-mov d-result d-x16)
           #t))
        ((string=? name "bytevector-u8-ref")
         (begin
           (da-e (x86-test-imm y 7)) (da-jcc da-c-ne slow)
           (da-ld d-x14 x -4)
           (da-mov d-x15 y) (da-e (x86-shift-imm da-sar d-x15 3))
           (da-e (x86-alu da-cmp d-x15 d-x14)) (da-jcc da-c-ae slow)
           (da-e (x86-load8-ix d-x16 x d-x15 1 4))
           (da-e (x86-shift-imm da-shl d-x16 3))
           (da-mov d-result d-x16)
           #t))
        ((string=? name "%fx26-flatarray-length")
         (begin (df-flat-count x d-x13) (dq-fixnum-of d-x13) #t))
        ((string=? name "%fx26-flatarray-ref") (begin (df-flat-ref y slow) #t))
        ((or (string=? name "%suffix-ref-offset") (string=? name "%suffix-ref-owner"))
         (begin (dq-suffix-part name slow) #t))
        ((string=? name "%suffix-ref+") (begin (dq-suffix-plus y slow) #t))
        ((string=? name "%bloblet-fields") (begin (dq-bloblet-fields slow) #t))
        (else (dr-narrow-fast name y slow))))))

;; The quotient, if it is a fixnum: else `RESULT` back, and slow.
(define dq-quotient (subr da-assembles (int) unit)
  (lambda (slow)
    (let ((ok (da-label)) (restore (da-label)))
      (begin
        (da-mov d-x13 d-rax)
        (da-e (x86-shift-imm da-shl d-x13 3))
        (da-e (x86-shift-imm da-sar d-x13 3))
        (da-e (x86-alu da-cmp d-x13 d-rax)) (da-jcc da-c-ne restore)
        (da-e (x86-shift-imm da-shl d-rax 3))
        (da-jmp ok)
        (da-bind restore)
        (da-mov d-result d-x16)
        (da-jmp slow)
        (da-bind ok)))))
;; The remainder, with the divisor's sign.
(define dq-modulo (subr da-assembles (int) unit)
  (lambda (y)
    (let ((signed (da-label)))
      (begin
        (da-e (x86-test d-rdx d-rdx)) (da-jcc da-c-e signed)
        (da-mov d-x13 d-rdx) (da-e (x86-alu da-xor d-x13 y)) (da-jcc da-c-ns signed)
        (da-e (x86-alu da-add d-rdx y))
        (da-bind signed)
        (da-mov d-result d-rdx)))))
;; Left while the result stays a fixnum; right (floor) by fewer than 63.
(define dq-shift (subr da-assembles (int int) unit)
  (lambda (y slow)
    (let ((right (da-label)) (done (da-label)) (x d-result))
      (begin
        (dq-fixnums y slow)
        (da-mov d-rcx y) (da-e (x86-shift-imm da-sar d-rcx 3))
        (da-e (x86-test d-rcx d-rcx)) (da-jcc da-c-l right)
        (da-e (x86-alu-imm da-cmp d-rcx 61)) (da-jcc da-c-ge slow)
        (da-mov d-x14 x) (da-e (x86-shift-cl da-shl d-x14))
        (da-mov d-x16 d-x14) (da-e (x86-shift-cl da-sar d-x16))
        (da-e (x86-alu da-cmp d-x16 x)) (da-jcc da-c-ne slow)
        (da-mov d-result d-x14)
        (da-jmp done)
        (da-bind right)
        (da-e (x86-neg d-rcx))
        (da-e (x86-alu-imm da-cmp d-rcx 63)) (da-jcc da-c-ae slow)
        (da-mov d-x14 x) (da-e (x86-shift-cl da-sar d-x14))
        (da-e (x86-shift-imm da-sar d-x14 3)) (da-e (x86-shift-imm da-shl d-x14 3))
        (da-mov d-result d-x14)
        (da-bind done)))))
;; A suffix ref's offset, and its owner, a bloblet.
(define dq-suffix-part (subr da-assembles (string int) unit)
  (lambda (name slow)
    (begin
      (da-mov d-x16 d-result) (da-e (x86-alu-imm da-and d-x16 7))
      (da-e (x86-alu-imm da-cmp d-x16 d-tag-suffix-ref)) (da-jcc da-c-ne slow)
      (if (string=? name "%suffix-ref-offset")
          (begin (da-mov d-x13 d-result) (da-e (x86-shift-imm da-shr d-x13 d-suffix-offset-shift))
                 (da-e (x86-shift-imm da-shl d-x13 3)) (da-mov d-result d-x13))
          (begin (da-ubfx d-x14 d-result 3 d-suffix-owner-bits)
                 (da-ld d-x9 d-st d-st-words)
                 (da-e (x86-lea-ix d-result d-x9 d-x14 8 d-tag-bloblet)))))))
;; `y` bytes along: still in the owner's suffix, the offset rebuilt.
(define dq-suffix-plus (subr da-assembles (int int) unit)
  (lambda (y slow)
    (begin
      (da-e (x86-test-imm y 7)) (da-jcc da-c-ne slow)
      (df-suffix-owner d-result slow)
      (da-mov d-x9 y) (da-e (x86-shift-imm da-sar d-x9 3))
      (da-e (x86-alu da-add d-x9 d-x15))
      (da-e (x86-alu da-cmp d-x9 d-x13)) (da-jcc da-c-ae slow)
      (da-ubfx d-x14 d-result 0 d-suffix-offset-shift)
      (da-e (x86-shift-imm da-shl d-x9 d-suffix-offset-shift))
      (da-mov d-result d-x14)
      (da-e (x86-alu da-or d-result d-x9)))))
;; A bloblet's count of fields: its trailer's distance.
(define dq-bloblet-fields (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (da-mov d-x13 d-result) (da-e (x86-alu-imm da-and d-x13 7))
      (da-e (x86-alu-imm da-cmp d-x13 d-tag-bloblet)) (da-jcc da-c-ne slow)
      (da-ld d-x16 d-result (dq-fld 1))
      (da-mov d-x13 d-x16) (da-e (x86-alu-imm da-and d-x13 7))
      (da-e (x86-alu-imm da-cmp d-x13 d-tag-trailer)) (da-jcc da-c-ne slow)
      (da-e (x86-shift-imm da-shr d-x16 d-t-distance-lo))
      (da-mov d-x13 d-x16)
      (da-e (x86-shift-imm da-shl d-x13 32)) (da-e (x86-shift-imm da-shr d-x13 29))
      (da-mov d-result d-x13))))
;;; ------------------------------------------------------------ `prim1`, `prim2`, `prim2imm`

;; The instruction after this one, by number (-1 past the last).
(define dq-next-op (subr da-reads () int)
  (lambda () (if (< (get dp-si) (dp-ns)) (dp-op (dp-start (get dp-si))) -1)))
;; `REGk`, or a copy of `RESULT` for REG0, in a register apart from
;; `RESULT`: its own, or `X17`.
(define dq-apart (subr da-assembles (int) int)
  (lambda (k) (if (= k 0) (begin (da-mov d-x17 d-result) d-x17) (da-get k d-x17))))
;; The constant operand `j` of the instruction at `i` in `X17`: as it is,
;; or from a field.
(define dq-constant (subr da-assembles (int int) unit)
  (lambda (i j)
    (if (dp-oimm? i j)
        (da-imm d-x17 (dp-ob i j))
        (da-field d-x17 (dp-field (dp-const-of (dp-oid i j)))))))
;; A flat array's index, apart from `RESULT` (`index`).
(define dq-index (subr da-assembles (int int) int)
  (lambda (i op)
    (if (= op rop-prim2) (dq-apart (dp-o i 1)) (begin (da-imm d-x17 (dp-ob i 1)) d-x17))))
;; The primitive's call-out on `args` with no collection, its value into
;; `RESULT`, and its trap.
(define dq-pure-call (subr da-assembles (int int da-bytes) unit)
  (lambda (pn n args) (begin (da-pure-call (dq-pure pn n) args d-result) (dq-checked))))

;; A primitive that never collects, on `RESULT` and `REGk` or a constant:
;; in line, where its fast path can; else a call-out with no collection.
(define dq-prim12 (subr da-assembles (int int) unit)
  (lambda (i op)
    (let* ((pn (dp-o i 0)) (pname (d-prim-name pn)))
      (cond ((not (d-never-collects? pn))
             (dp-decline
              (dq-cat4 "`" (d-op-name op) "` of `" (dq-cat pname "`, which may collect"))))
            ;; Rounding is SSE4.1's, which a few early processors lack.
            ((and (not (get dp-sse41))
                  (or (dq-ends? pname "floor") (dq-ends? pname "ceiling")
                      (dq-ends? pname "truncate") (dq-ends? pname "round")))
             (dp-decline (dq-cat4 "`" pname "` needs SSE4.1, " "which this processor lacks")))
            ;; What an `nclosure` made: here, the closure itself.
            ((string=? pname "%fx26-adapted") #u)
            (else
             (begin
               ;; An element returned: an `f64`'s bits returned raw, where the
               ;; caller takes them so; any other, as below.
               (if (and (string=? pname "%fx26-flatarray-ref") (= (dq-next-op) rop-return))
                   (let* ((y (dq-index i op)) (generic (da-label)))
                     (begin
                       (df-flat-element d-result y generic)
                       (da-e (x86-alu-imm da-cmp d-x16 (* 8 d-flat-f64)))
                       (da-jcc da-c-ne generic)
                       (da-e (x86-load-ix d-result d-x15 d-x14 8 0))
                       (dr-raw-return)
                       (da-bind generic)))
                   #u)
               (dq-prim12-rest i op pn pname)))))))

(define dq-prim12-rest (subr da-assembles (int int int string) unit)
  (lambda (i op pn pname)
    (let ((imm (and (= op rop-prim2imm) (dp-ofix? i 1))) (v (dp-o i 1)) (rop (nr-raw-op pname)))
      (cond
        ;; An element only `f64` operations use: its bits.
        ((and (string=? pname "%fx26-flatarray-ref") (dq-raw-ref?))
         (let* ((y (dq-index i op)) (slow (da-label)) (done (da-label)))
           (begin
             (df-flat-element d-result y slow)
             (da-e (x86-load-ix d-result d-x15 d-x14 8 0))
             (da-jmp done)
             (da-bind slow)
             (dq-pure-call pn 2 (da-args2 d-result y))
             (dr-unbox-f64 d-result)
             (da-bind done))))
        ;; A blobref's read of a scalar the layout of which is the constant.
        ((and (string=? pname "%fx26-suffix-ref-get") imm)
         (let ((raw (dq-raw-ref?)) (slow (da-label)) (done (da-label)))
           (begin
             (df-suffix-get v raw slow)
             (da-jmp done)
             (da-bind slow)
             (da-imm d-x17 (dp-ob i 1))
             (dq-pure-call pn 2 (da-args2 d-result d-x17))
             (if raw (dr-unbox-f64 d-result) #u)
             (da-bind done))))
        ;; A blobref stepped, a flat sum's numeric tag, a blobref made, its
        ;; room tested, or its length: in line.
        ((and imm (dq-suffix-imm? pname v)) (dq-suffix-imm i pn pname v))
        ((= (extract rop 1) 2) (dq-f64 i op pn (extract rop 3)))
        ((= (extract rop 1) 1) (dq-int i op (extract rop 2) (extract rop 3)))
        (else (dq-general i op pn pname))))))

;; Which of `%suffix-ref+`, `%fx26-flat-tag`, `%suffix-ref`,
;; `%fx26-suffix-fits` and `%fx26-suffix-ref-length` of the constant `v`
;; is done in line.
(define dq-suffix-imm? (subr da-reads (string int) bool)
  (lambda (pname v)
    (or (and (string=? pname "%suffix-ref+") (>= v 0) (< v 16777216))
        (string=? pname "%fx26-flat-tag")
        (and (string=? pname "%suffix-ref") (>= v 0) (< v 67108864))
        (and (string=? pname "%fx26-suffix-fits") (>= v 0) (< v 16777216))
        (and (string=? pname "%fx26-suffix-ref-length") (> (bitwise-and v 4294967295) 0)))))
(define dq-suffix-imm (subr da-assembles (int int string int) unit)
  (lambda (i pn pname v)
    (let ((slow (da-label)) (done (da-label)))
      (begin
        (cond ((string=? pname "%suffix-ref+") (df-suffix-step v slow))
              ((string=? pname "%fx26-flat-tag") (df-flat-tag v slow))
              ((string=? pname "%fx26-suffix-fits") (df-suffix-fits v slow))
              ((string=? pname "%fx26-suffix-ref-length") (df-suffix-length v slow))
              (else (df-blobref-at v slow)))
        (da-jmp done)
        (da-bind slow)
        (da-imm d-x17 (dp-ob i 1))
        (dq-pure-call pn 2 (da-args2 d-result d-x17))
        (da-bind done)))))

;; An `f64` operation the machine does.
(define dq-f64 (subr da-assembles (int int int string) unit)
  (lambda (i op pn what)
    (cond ((string=? what "from-int") (dr-f64-of-int pn))
          ((string=? what "->int") (dr-int-of-f64 pn))
          (else (dr-f64-fast what (if (= op rop-prim2) (dq-apart (dp-o i 1)) d-result))))))

;; An `i64` or `u64` operation: a shift's count is an `int`, a bignum
;; maybe, its low bits, as a fixnum's are, in a copy.
(define dq-count-of (subr da-assembles () unit)
  (lambda () (begin (dr-unbox-reg d-x17) (da-e (x86-shift-imm da-shl d-x17 3)))))
(define dq-int (subr da-assembles (int int bool string) unit)
  (lambda (i op signed what)
    (let* ((count (or (string=? what "-shl") (string=? what "-shr")))
           (y (cond ((and (= op rop-prim2) count)
                     (let ((r (dq-apart (dp-o i 1))))
                       (begin (if (= r d-x17) #u (da-mov d-x17 r)) (dq-count-of) d-x17)))
                    ((= op rop-prim2) (dq-apart (dp-o i 1)))
                    ((= op rop-prim2imm)
                     (begin
                       (cond ((and (dp-ofix? i 1) (not count)) (da-imm d-x17 (dp-o i 1)))
                             ((dp-oimm? i 1) (da-imm d-x17 (dp-ob i 1)))
                             (else
                              (begin (da-field d-x17 (dp-field (dp-const-of (dp-oid i 1))))
                                     (if count (dq-count-of) (dr-unbox-reg d-x17)))))
                       d-x17))
                    (else d-x17))))
      (let ((c (dr-compare what signed))
            (j (dp-branch-on (- (get dp-si) 1))))
        (cond ((string=? what "->int") (dr-box-reg d-result signed))
              ;; A test that only a branch reads, as `op2`'s.
              ((and (>= c 0) (>= j 0))
               (begin
                 (da-e (x86-alu da-cmp d-result y))
                 (da-bind (dp-label j))
                 (da-jcc (if (= (dp-op j) rop-brancht) c (bitwise-xor c 1))
                         (dp-edge (get dp-si) (dp-branch-to j)))
                 (set dp-si (+ (get dp-si) 1))))
              (else (dr-raw-fast signed what y)))))))

;; Any other: its fast path in line, else, and when that fails, the call-out.
(define dq-general (subr da-assembles (int int int string) unit)
  (lambda (i op pn pname)
    (let* ((y (cond ((= op rop-prim2) (dq-apart (dp-o i 1)))
                    ((= op rop-prim2imm) (begin (dq-constant i 1) d-x17))
                    (else d-x17)))
           (slow (da-label))
           (done (da-label))
           (fast-path (dq-pure-fast pname y slow)))
      (begin
        (if (or (not fast-path) (da-used? slow))
            (begin
              (if fast-path (da-jmp done) #u)
              (da-bind slow)
              (if (= op rop-prim1)
                  (dq-pure-call pn 1 (da-args1 d-result))
                  (dq-pure-call pn 2 (da-args2 d-result y))))
            #u)
        (da-bind done)))))

;;; ------------------------------------------------------------ `prim3imm`

;; Of three, `RESULT`, a constant and `REGk`: a blobref's index, write or
;; variant in line, with `REGk` in a register of its own; else the
;; primitive, a raw `f64` boxed for it in a copy.
(define dq-prim3 (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((pn (dp-o i 0)) (pname (d-prim-name pn)) (k (dp-o i 2)))
      (if (not (d-never-collects? pn))
          (dp-decline (dq-cat4 "`prim3imm` of `" pname "`, " "which may collect"))
          (let* ((z (if (= k 0) (begin (da-mov d-x12 d-result) d-x12) (da-get k d-x12)))
                 (raw (and (nr-is-f64-set? (get dp-cells) i)
                           (= (nr-rep (dp-in (- (get dp-si) 1)) k) nr-f64)))
                 (slow (da-label))
                 (done (da-label))
                 (inline (and (dp-ofix? i 1) (>= k 1) (<= k 3)))
                 (c (dp-o i 1)))
            (begin
              (cond ((not inline) #u)
                    ((string=? pname "%fx26-blobref-index") (df-blobref-index c z slow))
                    ((string=? pname "%fx26-suffix-ref-set!") (df-suffix-store c z raw slow))
                    ((string=? pname "%fx26-flat-variant!") (df-flat-variant c z slow))
                    (else #u))
              (if (da-used? slow) (da-jmp done) #u)
              (da-bind slow)
              (let ((z (if raw
                           (begin (if (= z d-x12) #u (da-mov d-x12 z)) (dr-box-f64 d-x12) d-x12)
                           z)))
                (begin
                  (dq-constant i 1)
                  (dq-pure-call pn 3 (da-args3 d-result d-x17 z))))
              (da-bind done)))))))
;;; ------------------------------------------------------------ control

;; A call of the closure in `CLO`, `n` arguments in registers, back at
;; `after`: its code runs, native code or a stub that enters `foreign`
;; with the count (`call_clo`).
(define dq-call-clo (subr da-assembles (int int) unit)
  (lambda (n after)
    (begin
      (da-ld d-x16 d-clo (dq-fld d-closure-word))
      (da-imm d-x9 n)
      (da-e (x86-alu-rm da-add d-x16 d-st d-st-delta))
      (da-e (x86-call-r d-x16))
      (da-bind after))))
;; Call-out `code` of `arity` arguments, from the registers, and its trap.
(define dq-callout (subr da-assembles (int int) unit)
  (lambda (code arity)
    (let ((n (da-callout code)))
      (begin
        (da-regs-to-args (min arity 8))
        (da-call-out n)
        (dq-checked)))))
;; A control frame: its header, the link, `second` (a register, or -1 for
;; nothing), the marker, REG1 and REG2, and `last` (the state's word at
;; that offset, or -1 for nothing).
(define dq-control-frame (subr da-assembles (int int int) unit)
  (lambda (second marker last)
    (begin
      (da-e (x86-alu-imm da-sub d-sp d-control-frame))
      (da-sto d-sp 8 d-frame)
      (if (< second 0) (da-e (x86-store-imm d-sp -1 1 16 0)) (da-sto d-sp 16 second))
      (da-e (x86-lea d-frame d-sp 8))
      ;; A control frame may pass the cache's limit by half the slack: the
      ;; next procedure's frame flushes it with the rest.
      (da-e (x86-lea d-x16 d-sp (quotient d-stack-slack 2)))
      (da-e (x86-alu-rm da-cmp d-x16 d-st d-st-stack-limit))
      (da-trap d-stack-overflow da-c-b)
      (da-imm d-x16 marker)
      (da-sto d-frame 16 d-x16)
      (da-sto d-frame 24 dq-r1)
      (da-sto d-frame 32 dq-r2)
      (if (< last 0)
          (da-e (x86-store-imm d-frame -1 1 40 0))
          (begin (da-ld d-x16 d-st last) (da-sto d-frame 40 d-x16))))))
(define dq-pop-control (subr da-assembles () unit)
  (lambda () (begin (da-ld d-frame d-sp 8) (da-e (x86-alu-imm da-add d-sp d-control-frame)))))

;; Control, on the native stack, as `procedure` does it: a prompt, a mark,
;; a mark in tail position, an abort, a continuation taken, and marks.
(define dq-control (subr da-assembles (int) unit)
  (lambda (i)
    (let ((r (dp-o i 0)))
      (cond
        ((< (get dp-frame) 0) (dp-decline "a call-out outside a frame"))
        ;; REG1 the tag, REG2 the handler, REG3 the thunk. An abort resumes
        ;; at the landing, the prompt's frame on top, with the value: the
        ;; handler called with it.
        ((= r routine-prompt)
         (let ((land (da-label)) (after (da-label)) (done (da-label)) (handled (da-label)))
           (begin
             (da-lea-l d-x9 land)
             (dq-control-frame d-x9 d-prompt-mark d-st-regions)
             (da-mov d-clo dq-r3)
             (dq-call-clo 0 after)
             (dq-pop-control)
             (da-jmp done)
             (da-bind land)
             (da-mov dq-r1 d-result)
             (da-ld d-clo d-sp 40)
             (dq-pop-control)
             (dq-call-clo 1 handled)
             (da-bind done))))
        ((= r routine-withmark)
         (let ((after (da-label)))
           (begin
             (dq-control-frame -1 d-mark-mark -1)
             (da-mov d-clo dq-r3)
             (dq-call-clo 0 after)
             (dq-pop-control))))
        ((= r routine-withmark-tail) (dq-withmark-tail))
        ((= r routine-abort)
         (begin
           (dq-callout (da-co d-co-abort 0 0) 2)
           (set dp-uses-resume #t)
           (da-jmp (get dp-resume-at))))
        ((or (= r routine-callcc) (= r routine-callcomp) (= r routine-ncallcc)
             (= r routine-ncallcomp) (= r routine-callone) (= r routine-ncallone))
         (dq-capture i r))
        ((= r routine-firstmark) (dq-callout (da-co d-co-first-mark 0 0) 2))
        ((= r routine-currentmarks) (dq-callout (da-co d-co-current-marks 0 0) 1))
        (else (dq-callout (da-co d-co-marks-of 0 0) 2))))))

;; In tail position, this frame popped (the return address on top): the
;; thunk tail-called with the mark's frame under it, returning through
;; `mark_ret`; a mark's frame there already, for the same key, has its
;; value replaced.
(define dq-withmark-tail (subr da-assembles () unit)
  (lambda ()
    (let ((push- (da-label)) (call (da-label)))
      (begin
        (da-ld d-x9 d-st d-st-mark-ret)
        (da-e (x86-alu-rm da-cmp d-x9 d-sp 0))
        (da-jcc da-c-ne push-)
        (da-ld d-x16 d-sp (+ 8 32))
        (da-e (x86-alu da-cmp d-x16 dq-r1))
        (da-jcc da-c-ne push-)
        (da-sto d-sp (+ 8 40) dq-r2)
        (da-jmp call)
        (da-bind push-)
        (da-e (x86-pop d-x11))
        (dq-control-frame d-x11 d-mark-mark -1)
        (da-e (x86-push-m d-st d-st-mark-ret))
        (da-bind call)
        (da-mov d-clo dq-r3)
        (da-ld d-x16 d-clo (dq-fld d-closure-word))
        (da-imm d-x9 0)
        (da-e (x86-alu-rm da-add d-x16 d-st d-st-delta))
        (da-e (x86-jmp-r d-x16))))))

;; A continuation taken (native here, so `ncallcc`'s too): where it
;; resumes, the continuation procedure, the capture, and the receiver
;; called with it.
(define dq-capture (subr da-assembles (int int) unit)
  (lambda (i r)
    (let ((after (da-label))
          (whole (or (= r routine-callcc) (= r routine-ncallcc)))
          (once (or (= r routine-callone) (= r routine-ncallone))))
      (begin
        (da-lea-l d-x9 after)
        (da-sto d-st d-st-ret-pc d-x9)
        (da-field d-x9 (dp-field (dp-code-of (array-ref (get dp-b) i))))
        (da-sto d-st d-st-aux d-x9)
        (dq-callout (da-co d-co-capture (if whole 1 0) (if once 1 0)) (if whole 1 2))
        (da-mov dq-r1 d-result)
        (da-ld d-clo d-st d-st-args)
        (dq-call-clo 1 after)))))
;;; ------------------------------------------------------------ call-outs

;; What a `prim`, `cellular` or `lambda` calls out to, as a call-out's code
;; (`fx::callout_code`) and its arity; -1 where it cannot be compiled (and
;; why noted). A `lambda`'s code field noted in `dq-code-field`.
(define dq-code-field (ref int @k) (new -1))
(define dq-what (subr da-assembles (int int) (productof (1 int) (2 int)))
  (lambda (i op)
    (let ((k0 (dp-o i 0)) (n (dp-o i 1)) (none (product (1 -1) (2 0))))
      (cond
        ((= op rop-lambda)
         (if (= (array-ref (get dp-kind) i) -1)
             (begin (dq-error-at i) none)
             (begin (set dq-code-field (dp-field (dp-code-of (array-ref (get dp-a) i))))
                    (product (1 (da-co d-co-closure n 0)) (2 n)))))
        ((and (= op rop-cellular) (= k0 routine-cons) (= n 2))
         (product (1 (da-co d-co-cons 0 0)) (2 2)))
        ((and (= op rop-cellular) (string=? (d-routine-name k0) "rest") (= n 0))
         (product (1 (da-co d-co-rest 0 0)) (2 0)))
        ((and (= op rop-cellular) (string=? (d-routine-name k0) "field@") (= n 2))
         (product (1 (da-co d-co-field-ref 0 0)) (2 2)))
        ((= op rop-prim)
         (let ((name (d-prim-name k0)))
           (cond ((or (string=? name "%region-closure") (string=? name "%region-nclosure"))
                  (product (1 (da-co d-co-region-closure n 0)) (2 n)))
                 ((string=? name "%stay-cellular")
                  (begin (dp-decline "it calls `stay-cellular`") none))
                 ((and (>= (d-prim-min k0) 0) (>= n (d-prim-min k0))
                       (or (< (d-prim-max k0) 0) (<= n (d-prim-max k0))))
                  (product (1 (da-co d-co-prim k0 n)) (2 n)))
                 ((string=? name "?")
                  (begin (dp-decline (string-append "primitive " (int->string k0))) none))
                 (else (begin (dp-decline (dq-cat4 "the primitive `" name "`" "")) none)))))
        (else (begin (dp-decline (dq-cat4 "the routine `" (d-routine-name k0) "`" "")) none))))))
;; The procedure's error at cell `i`, as Rust found it.
(define dq-error-at (subr da-assembles (int) unit)
  (lambda (i)
    (letrec ((nth (subr da-reads (da-strings int) string)
               (lambda (l k) (if (= k 0) (car l) (nth (cdr l) (- k 1))))))
      (da-fail (nth (get dp-errors) (array-ref (get dp-a) i))))))

;; Room for `n` words from the heap's free space (`df-bump`), short of the
;; collection's threshold: at X11, the free space bumped; else `slow`.
(define dq-bump df-bump)
;; Fields REG2…REGn of the bloblet of `total` fields at X11 (uses X17).
(define dq-fields-from (subr da-assembles (int int int) unit)
  (lambda (j n total)
    (if (> j n)
        #u
        (begin (da-store-reg d-x11 (* 8 (- (+ 1 total) j)) j d-x17)
               (dq-fields-from (+ j 1) n total)))))
;; Its trailer, and `RESULT` the bloblet.
(define dq-bloblet-done (subr da-assembles (int int) unit)
  (lambda (total t)
    (begin
      (da-imm t (da-trailer total))
      (da-sto d-x11 (* 8 total) t)
      (da-e (x86-lea d-result d-x11 (+ (* 8 (+ 1 total)) d-tag-bloblet))))))

;; A call-out: to Rust, on Rust's stack, which may collect; everything
;; live is in the frame by then, and the arguments go through the state.
;; What can be is done in line first.
(define dq-callouts (subr da-assembles (int int) unit)
  (lambda (i op)
    (begin
      (set dq-code-field -1)
      (let ((w (dq-what i op)))
        (if (< (extract w 1) 0)
            #u
            (let* ((c (extract w 1))
                   (leaf-closure (and (< (get dp-frame) 0) (= (bitwise-and c 31) d-co-closure))))
              (if (and (< (get dp-frame) 0) (not leaf-closure))
                  (dp-decline "a call-out outside a frame")
                  (dq-callouts-made i c (extract w 2) leaf-closure))))))))

;; Whether call-out `c` is a primitive's named `want` of `n` arguments.
(define dq-prim-is? (subr da-reads (int string int) bool)
  (lambda (c want n)
    (and (= (bitwise-and c 31) d-co-prim)
         (= (quotient c (* 32 4096)) n)
         (string=? (d-prim-name (bitwise-and (quotient c 32) 4095)) want))))
(define dq-prim-name-of (subr da-reads (int) string)
  (lambda (c)
    (if (= (bitwise-and c 31) d-co-prim) (d-prim-name (bitwise-and (quotient c 32) 4095)) "")))

(define dq-callouts-made (subr da-assembles (int int int bool) unit)
  (lambda (i c arity leaf-closure)
    (let ((done (da-label))
          (slow (da-label))
          (raw-store (= (nr-rep (dp-in (- (get dp-si) 1)) 3) nr-f64))
          (kind (bitwise-and c 31))
          (n (bitwise-and (quotient c 32) 4095))
          (pname (dq-prim-name-of c)))
      (begin
        (dq-inline c kind pname arity raw-store slow done)
        (da-bind slow)
        (if (and raw-store (dq-prim-is? c "%fx26-flatarray-set!" 3)) (dr-box-f64 dq-r3) #u)
        (if (and (= kind d-co-closure) (>= (get dq-code-field) 0))
            (begin
              ;; A frame for the collector to walk, with nothing in it, the
              ;; return address its second.
              (if leaf-closure (da-push-frame-ret d-stub-frame) #u)
              (da-field d-x17 (get dq-code-field))
              (da-imm d-x9 n)
              (da-e (x86-call-m d-st d-st-closure))
              (if leaf-closure (da-pop-frame-ret d-stub-frame) #u))
            (dq-callout c arity))
        (da-bind done)))))

;; What is done in line before the call-out, to `done`, or on to `slow`.
(define dq-inline (subr da-assembles (int int string int bool int int) unit)
  (lambda (c kind pname arity raw-store slow done)
    (let ((r1 dq-r1) (r2 dq-r2))
      (begin
        ;; `rcons`, `new`, `make-array`, `rnew` and `rmake-array`.
        (df-alloc pname arity slow done)
        (if (dq-prim-is? c "%fx26-flatarray-set!" 3) (df-flat-set slow done raw-store) #u)
        (if (dq-prim-is? c "%fx26-bytevector-u8-set!" 3) (df-bytes-set slow done) #u)
        (if (dq-prim-is? c "%fx26-suffix-ref-set!" 3) (df-suffix-set slow done) #u)
        (if (dq-prim-is? c "string=?" 2) (begin (dq-string-eq r1 r2) (da-jmp done)) #u)
        (if (dq-prim-is? c "char-whitespace?" 1)
            (begin (dq-char-whitespace r1 slow) (da-jmp done))
            #u)
        (if (dq-prim-is? c "%fx26-char-in?" 2) (begin (dq-char-in r1 r2) (da-jmp done)) #u)
        (if (dq-prim-is? c "%fx26-suffix-ref-index" 3)
            (begin (df-suffix-index slow) (da-jmp done))
            #u)
        ;; `int`'s bit operations of fixnums.
        (if (or (string=? pname "%fx26-bitwise-and") (string=? pname "%fx26-bitwise-ior")
                (string=? pname "%fx26-bitwise-xor") (string=? pname "%fx26-bitwise-not"))
            (dq-bitwise pname arity slow done)
            #u)
        ;; A mutable bloblet of no suffix (`%make-bloblet`).
        (if (and (string=? pname "%make-bloblet") (>= arity 1) (<= arity d-regs))
            (begin
              (da-e (x86-test r1 r1))
              (da-jcc da-c-ne slow)
              (dq-bump (+ 1 arity) slow)
              (da-imm d-x15 (da-header d-kind-bloblet arity 0))
              (da-sto d-x11 0 d-x15)
              (dq-fields-from 2 arity arity)
              (dq-bloblet-done arity d-x15)
              (da-jmp done))
            #u)
        ;; A sum or product (`%make-frozen`).
        (if (and (string=? pname "%make-frozen") (>= arity 2) (<= arity d-regs))
            (dq-frozen arity slow done)
            #u)
        (if (= kind d-co-cons)
            (begin
              (dq-bump 2 slow)
              (da-sto d-x11 0 r1)
              (da-sto d-x11 8 r2)
              (da-e (x86-lea d-result d-x11 d-tag-pair))
              (da-jmp done))
            #u)
        ;; Field REG2 (8k) of the bloblet in REG1, 2 ≤ k ≤ F.
        (if (= kind d-co-field-ref)
            (begin
              (dq-field-in-range slow)
              (da-mov d-x11 r1)
              (da-e (x86-alu da-sub d-x11 r2))
              (da-ld d-result d-x11 -4)
              (da-jmp done))
            #u)
        ;; `%bloblet-set!`: REG3 into field REG2 (8k) of the bloblet in
        ;; REG1, its fields not frozen.
        (if (dq-prim-is? c "%bloblet-set!" 3) (dq-bloblet-set slow done) #u)
        ;; A native closure over REG1…REGn from the free space.
        (if (and (= kind d-co-closure) (>= (get dq-code-field) 0) (<= arity 8))
            (dq-closure arity slow done)
            #u)))))

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
        (da-bind end)))))

;; `int`'s bit operations of fixnums.
(define dq-bitwise (subr da-assembles (string int int int) unit)
  (lambda (name n slow done)
    (begin
      (if (= n 2)
          (begin (da-mov d-x13 dq-r1)
                 (da-e (x86-alu da-or d-x13 dq-r2))
                 (da-e (x86-test-imm d-x13 7)))
          (da-e (x86-test-imm dq-r1 7)))
      (da-jcc da-c-ne slow)
      (da-mov d-result dq-r1)
      (cond ((string=? name "%fx26-bitwise-and") (da-e (x86-alu da-and d-result dq-r2)))
            ((string=? name "%fx26-bitwise-ior") (da-e (x86-alu da-or d-result dq-r2)))
            ((string=? name "%fx26-bitwise-xor") (da-e (x86-alu da-xor d-result dq-r2)))
            (else (begin (da-e (x86-neg d-result)) (da-e (x86-alu-imm da-sub d-result 8)))))
      (da-jmp done))))

;; A sum or product (`%make-frozen`) of `total` fields, frozen.
(define dq-frozen-header (subr pure (int int) int)
  (lambda (kind total)
    (+ (da-header kind total 0)
       (+ (arithmetic-shift 1 d-h-fields-frozen-lo) (arithmetic-shift 1 d-h-suffix-frozen-lo)))))
(define dq-frozen (subr da-assembles (int int int) unit)
  (lambda (total slow done)
    (let ((sum (da-label)) (kinded (da-label)))
      (begin
        (da-cmp-k dq-r1 (* 8 d-kind-sum))
        (da-jcc da-c-e sum)
        (da-cmp-k dq-r1 (* 8 d-kind-product))
        (da-jcc da-c-ne slow)
        (da-imm d-x17 (dq-frozen-header d-kind-product total))
        (da-jmp kinded)
        (da-bind sum)
        (da-imm d-x17 (dq-frozen-header d-kind-sum total))
        (da-bind kinded)
        (dq-bump (+ 1 total) slow)
        (da-sto d-x11 0 d-x17)
        (dq-fields-from 2 total total)
        (dq-bloblet-done total d-x15)
        (da-jmp done)))))

;; Field REG2 (8k) of the bloblet in REG1 in range, 2 ≤ k ≤ F, its
;; trailer's distance in X16; else `slow`.
(define dq-field-in-range (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (da-ld d-x16 dq-r1 (dq-fld 1))
      (da-mov d-x13 d-x16)
      (da-e (x86-alu-imm da-and d-x13 7))
      (da-e (x86-alu-imm da-cmp d-x13 d-tag-trailer))
      (da-jcc da-c-ne slow)
      (da-e (x86-alu-imm da-cmp dq-r2 16))
      (da-jcc da-c-l slow)
      (da-e (x86-alu-imm da-sub d-x16 d-tag-trailer))
      (da-e (x86-alu da-cmp dq-r2 d-x16))
      (da-jcc da-c-g slow))))
(define dq-bloblet-set (subr da-assembles (int int) unit)
  (lambda (slow done)
    (begin
      (dq-field-in-range slow)
      (da-mov d-x11 dq-r1)
      (da-e (x86-alu da-sub d-x11 d-x16))
      (da-ld d-x13 d-x11 -12)
      (da-e (x86-shift-imm da-shr d-x13 d-h-fields-frozen-lo))
      (da-e (x86-test-imm d-x13 1))
      (da-jcc da-c-ne slow)
      (da-mov d-x11 dq-r1)
      (da-e (x86-alu da-sub d-x11 dq-r2))
      (da-sto d-x11 -4 dq-r3)
      (da-card-mark d-x11 -4 d-x13 d-x16)
      (da-imm d-result d-unspecified)
      (da-jmp done))))

;; A native closure over REG1…REGn from the free space.
(define dq-closure (subr da-assembles (int int int) unit)
  (lambda (n slow done)
    (let ((total (+ n 2)))
      (letrec ((frees (subr da-assembles (int) unit)
                 (lambda (k)
                   (if (= k n)
                       #u
                       (begin (da-store-reg d-x11 (* 8 (- n k)) (+ 1 k) d-x17) (frees (+ k 1)))))))
        (begin
          (dq-bump (+ total 1) slow)
          (da-imm d-x17 (da-header d-kind-native-closure total 0))
          (da-sto d-x11 0 d-x17)
          (frees 0)
          (da-field d-x17 (get dq-code-field))
          (da-sto d-x11 (* 8 (+ n 1)) d-x17)
          (da-imm d-x17 (da-trailer total))
          (da-sto d-x11 (* 8 total) d-x17)
          (da-e (x86-lea d-result d-x11 (+ (* 8 (+ total 1)) d-tag-bloblet)))
          (da-jmp done))))))
)))
