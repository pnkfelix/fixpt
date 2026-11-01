;;; The primitives, control and call-outs of the native convention's
;;; compiler to arm64 written in FX-26: `procedure`'s arms for `prim1`,
;;; `prim2`, `prim2imm`, `prim3imm`, control (`cellular` of a prompt, a
;;; mark, an abort, a capture or marks), and `prim`, `cellular` and
;;; `lambda` (`fixpt-native/src/direct.rs`), step for step, each `adq-`
;;; and its Rust name, over the procedure's state
;;; (`native-direct-arm64-proc.fx`).
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder, the layouts, the
;;; assembler, the analysis, the raw values' and the heap's pieces, and the
;;; procedure.

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (arm-direct-types (load-module "fx26:native-direct-arm64-types.fx"))
       (direct-layout-types (load-module "fx26:native-direct-arm64-layout-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (arm64-types (load-module "fx26:arm64-types.fx")))
  (lambda ((arm (select arm64-types arm64-direct-sig))
           (dl (select direct-layout-types native-direct-arm64-layout-sig))
           (layout (select layout-types layout-sig))
           (asm (select arm-direct-types native-direct-arm64-asm-sig))
           (reps (select direct-types native-reps-sig))
           (raw (select arm-direct-types native-direct-arm64-raw-sig))
           (flat (select arm-direct-types native-direct-arm64-flat-sig))
           (proc (select arm-direct-types native-direct-arm64-proc-sig)))
    ;; `pure_fast` and `string_eq` in a file of their own
    ;; (`native-direct-arm64-strings.fx`), made of what it is given.
    (let ((native-direct-arm64-strings
           ((load-input "fx26:native-direct-arm64-strings.fx") arm dl asm raw flat)))
      (module
(hide (include direct-types) (include arm-direct-types))
(hide (include arm) (include dl) (include layout) (include asm) (include reps) (include raw)
      (include flat) (include proc))

;; Given on, what `native-direct-arm64-strings.fx` defines.
(import native-direct-arm64-strings adq-pure-fast adq-string-eq)

;; Strings joined.
(define adq-cat (subr pure (string string) string) (lambda (a b) (string-append a b)))
(define adq-cat4 (subr pure (string string string string) string)
  (lambda (a b c d) (string-append a (string-append b (string-append c d)))))
;; Whether the element or value this instruction gives is taken raw.
(define adq-raw-ref? (subr da-reads () bool)
  (lambda () (array-ref (get adp-raw-refs) (- (get adp-si) 1))))
;; A primitive's call-out that never collects (`Callout::Pure`).
(define adq-pure (subr pure (int int) int) (lambda (p n) (ada-co d-co-pure p n)))
;; Its call on `args`, its value into `RESULT`, and its trap.
(define adq-pure-call (subr da-assembles (int int da-bytes) unit)
  (lambda (pn n args) (begin (ada-pure-call (adq-pure pn n) args d-result) (ada-trap-set))))
;; `t` := the constant operand `j` of the instruction at `i`: as it is, or
;; from a field.
(define adq-constant (subr da-assembles (int int int) unit)
  (lambda (t i j)
    (if (adp-oimm? i j)
        (ada-imm t (adp-ob i j))
        (ada-ldr-field t (adp-field (adp-const-of (adp-oid i j)))))))

;;; ------------------------------------------------------------ control

;; A call of the closure in `CLO`, `n` arguments in registers, back at
;; `after`: its code runs, native code or a stub that enters `foreign`
;; with the count (`call_clo`).
(define adq-call-clo (subr da-assembles (int int) unit)
  (lambda (n after)
    (begin
      (ada-e (arm-ldur d-x16 d-clo (ada-field-off d-closure-word)))
      (ada-e (arm-movz d-x9 n 0))
      (ada-e (arm-add d-x16 d-x16 d-delta))
      (ada-e (arm-blr d-x16))
      (ada-bind after))))
;; Call-out `code` of `arity` arguments, from the registers, and its trap
;; (`callout`).
(define adq-callout (subr da-assembles (int int) unit)
  (lambda (code arity)
    (let ((n (ada-callout code)))
      (letrec ((args (subr da-assembles (int) unit)
                 (lambda (j)
                   (if (>= j (min arity 8))
                       #u
                       (begin (ada-sto (+ 1 j) d-st (+ d-st-args (* 8 j))) (args (+ j 1)))))))
        (begin (args 0) (ada-call-out n) (ada-trap-set))))))
;; A control frame: the link, `second` (the landing, or nothing), the
;; marker, `x1` and `x2`, and `last` (the state's word at that offset, or
;; -1 for nothing).
(define adq-control-frame (subr da-assembles (int int int) unit)
  (lambda (second marker last)
    (begin
      (ada-push-frame second d-control-frame)
      ;; A control frame may pass the cache's limit by half the slack: the
      ;; next procedure's frame flushes it with the rest.
      (ada-e (arm-add-imm-pages d-x16 d-sp (quotient d-stack-slack 8192)))
      (ada-e (arm-cmp d-x16 d-limit))
      (ada-trap d-stack-overflow ada-c-lo)
      (ada-imm d-x16 marker)
      (ada-sto d-x16 d-frame 16)
      (ada-sto 1 d-frame 24)
      (ada-sto 2 d-frame 32)
      (if (< last 0)
          (ada-sto d-xzr d-frame 40)
          (begin (ada-ld d-x16 d-st last) (ada-sto d-x16 d-frame 40))))))
(define adq-pop-control (subr da-assembles () unit)
  (lambda () (begin (ada-ld d-frame d-sp 8) (ada-e (arm-add-imm d-sp d-sp d-control-frame)))))

;; Control, on the native stack: a prompt, a mark, a mark in tail
;; position, an abort, a continuation taken, and marks.
(define adq-control (subr da-assembles (int) unit)
  (lambda (i)
    (let ((r (adp-o i 0)))
      (cond
        ((< (get adp-frame) 0) (adp-decline "a call-out outside a frame"))
        ;; `x1` the tag, `x2` the handler, `x3` the thunk. An abort resumes
        ;; at the landing, the prompt's frame on top, with the value: the
        ;; handler called with it.
        ((= r routine-prompt)
         (let* ((land (ada-label)) (after (ada-label)) (done (ada-label)) (handled (ada-label)))
           (begin
             (ada-adr d-x9 land)
             (adq-control-frame d-x9 d-prompt-mark d-st-regions)
             (ada-mov d-clo 3)
             (adq-call-clo 0 after)
             (adq-pop-control)
             (ada-b done)
             (ada-bind land)
             (ada-mov 1 d-result)
             (ada-ld d-clo d-sp 40)
             (adq-pop-control)
             (adq-call-clo 1 handled)
             (ada-bind done))))
        ;; `x1` the key, `x2` the value, `x3` the thunk.
        ((= r routine-withmark)
         (let ((after (ada-label)))
           (begin
             (adq-control-frame d-xzr d-mark-mark -1)
             (ada-mov d-clo 3)
             (adq-call-clo 0 after)
             (adq-pop-control))))
        ((= r routine-withmark-tail) (adq-withmark-tail))
        ((= r routine-abort)
         (begin
           (adq-callout (ada-co d-co-abort 0 0) 2)
           (set adp-uses-resume #t)
           (ada-b (get adp-resume-at))))
        ((or (= r routine-callcc) (= r routine-callcomp) (= r routine-ncallcc)
             (= r routine-ncallcomp) (= r routine-callone) (= r routine-ncallone))
         (adq-capture i r))
        ((= r routine-firstmark) (adq-callout (ada-co d-co-first-mark 0 0) 2))
        ((= r routine-currentmarks) (adq-callout (ada-co d-co-current-marks 0 0) 1))
        (else (adq-callout (ada-co d-co-marks-of 0 0) 2))))))

;; In tail position, this frame popped: the thunk tail-called with the
;; mark's frame under it, returning through `mark_ret`; a mark's frame on
;; top already, for the same key, has its value replaced.
(define adq-withmark-tail (subr da-assembles () unit)
  (lambda ()
    (let* ((push- (ada-label)) (call (ada-label)))
      (begin
        (ada-ld d-x9 d-st d-st-mark-ret)
        (ada-e (arm-cmp d-link d-x9))
        (ada-bc ada-c-ne push-)
        (ada-ld d-x16 d-sp 32)
        (ada-e (arm-cmp d-x16 1))
        (ada-bc ada-c-ne push-)
        (ada-sto 2 d-sp 40)
        (ada-b call)
        (ada-bind push-)
        (adq-control-frame d-link d-mark-mark -1)
        (ada-ld d-link d-st d-st-mark-ret)
        (ada-bind call)
        (ada-mov d-clo 3)
        (ada-e (arm-ldur d-x16 d-clo (ada-field-off d-closure-word)))
        (ada-e (arm-movz d-x9 0 0))
        (ada-e (arm-add d-x16 d-x16 d-delta))
        (ada-e (arm-br d-x16))))))

;; A continuation taken (native here, so `ncallcc`'s too): where it
;; resumes, the continuation procedure, the capture, and `f` called with
;; it.
(define adq-capture (subr da-assembles (int int) unit)
  (lambda (i r)
    (let ((after (ada-label))
          (whole (or (= r routine-callcc) (= r routine-ncallcc)))
          (once (or (= r routine-callone) (= r routine-ncallone))))
      (begin
        (ada-adr d-x9 after)
        (ada-sto d-x9 d-st d-st-ret-pc)
        (ada-ldr-field d-x9 (adp-field (adp-code-of (array-ref (get adp-b) i))))
        (ada-sto d-x9 d-st d-st-aux)
        (adq-callout (ada-co d-co-capture (if whole 1 0) (if once 1 0)) (if whole 1 2))
        (ada-mov 1 d-result)
        (ada-ld d-clo d-st d-st-args)
        (adq-call-clo 1 after)))))

;;; ------------------------------------------------------------ `prim1`, `prim2`, `prim2imm`

;; A flat array's index (`y`): `REGk`, or the constant in X17.
(define adq-index (subr da-assembles (int int) int)
  (lambda (i op)
    (if (= op rop-prim2) (adp-o i 1) (begin (ada-imm d-x17 (adp-ob i 1)) d-x17))))

;; A primitive that never collects, on `RESULT` and `REGk` or a constant:
;; in line, where its fast path can; else a call-out with no collection,
;; the registers kept around it.
(define adq-prim12 (subr da-assembles (int int) unit)
  (lambda (i op)
    (let* ((pn (adp-o i 0)) (pname (d-prim-name pn)))
      (cond ((not (d-never-collects? pn))
             (adp-decline
              (adq-cat4 "`" (d-op-name op) "` of `" (adq-cat pname "`, which may collect"))))
            ;; What an `nclosure` made: here, the closure itself.
            ((string=? pname "%fx26-adapted") #u)
            ;; An element only `f64` operations use: its bits.
            ((and (string=? pname "%fx26-flatarray-ref") (adq-raw-ref?))
             (let* ((y (adq-index i op)) (slow (ada-label)) (done (ada-label)))
               (begin
                 (adf-flat-element d-result y slow)
                 (ada-e (arm-ldr-x8 d-result d-x15 d-x14))
                 (ada-b done)
                 (ada-bind slow)
                 (adq-pure-call pn 2 (ada-args2 d-result y))
                 (adr-unbox-f64 d-result)
                 (ada-bind done))))
            (else
             (begin
               ;; An element returned: an `f64`'s bits returned raw, where
               ;; the caller takes them so; any other, as below.
               (if (and (string=? pname "%fx26-flatarray-ref")
                        (< (get adp-si) (adp-ns))
                        (= (adp-op (adp-start (get adp-si))) rop-return))
                   (let* ((y (adq-index i op)) (generic (ada-label)))
                     (begin
                       (adf-flat-element d-result y generic)
                       (ada-e (arm-cmp-imm d-x16 (* 8 d-flat-f64)))
                       (ada-bc ada-c-ne generic)
                       (ada-e (arm-ldr-x8 d-result d-x15 d-x14))
                       (adr-raw-return)
                       (ada-bind generic)))
                   #u)
               (adq-prim12-rest i op pn pname)))))))

(define adq-prim12-rest (subr da-assembles (int int int string) unit)
  (lambda (i op pn pname)
    (let ((imm (and (= op rop-prim2imm) (adp-ofix? i 1))) (v (adp-o i 1)) (rop (nr-raw-op pname)))
      (cond
        ;; A blobref's read of a scalar the layout of which is the constant.
        ((and (string=? pname "%fx26-suffix-ref-get") imm)
         (let* ((raw (adq-raw-ref?)) (slow (ada-label)) (done (ada-label)))
           (begin
             (adf-suffix-get v raw slow)
             (ada-b done)
             (ada-bind slow)
             (ada-imm d-x17 (adp-ob i 1))
             (adq-pure-call pn 2 (ada-args2 d-result d-x17))
             (if raw (adr-unbox-f64 d-result) #u)
             (ada-bind done))))
        ;; A blobref stepped, a flat sum's numeric tag, a blobref made, its
        ;; room tested, or its length: in line.
        ((and imm (adq-suffix-imm? pname v)) (adq-suffix-imm i pn pname v))
        ((= (extract rop 1) 2) (adq-f64 i op pn (extract rop 3)))
        ((= (extract rop 1) 1) (adq-int i op (extract rop 2) (extract rop 3)))
        (else (adq-general i op pn pname))))))

;; Which of `%suffix-ref+`, `%fx26-flat-tag`, `%suffix-ref`,
;; `%fx26-suffix-fits` and `%fx26-suffix-ref-length` of the constant `v`
;; is done in line.
(define adq-suffix-imm? (subr da-reads (string int) bool)
  (lambda (pname v)
    (or (and (string=? pname "%suffix-ref+") (>= v 0) (< v 16777216))
        (string=? pname "%fx26-flat-tag")
        (and (string=? pname "%suffix-ref") (>= v 0) (< v 67108864))
        (and (string=? pname "%fx26-suffix-fits") (>= v 0) (< v 16777216))
        (and (string=? pname "%fx26-suffix-ref-length")
             (> (bitwise-and v (- (arithmetic-shift 1 d-array-operand-size-bits) 1)) 0)))))
(define adq-suffix-imm (subr da-assembles (int int string int) unit)
  (lambda (i pn pname v)
    (let* ((slow (ada-label)) (done (ada-label)))
      (begin
        (cond ((string=? pname "%suffix-ref+") (adf-suffix-step v slow))
              ((string=? pname "%fx26-flat-tag") (adf-flat-tag v slow))
              ((string=? pname "%fx26-suffix-fits") (adf-suffix-fits v slow))
              ((string=? pname "%fx26-suffix-ref-length") (adf-suffix-length v slow))
              (else (adf-blobref-at v slow)))
        (ada-b done)
        (ada-bind slow)
        (ada-imm d-x17 (adp-ob i 1))
        (adq-pure-call pn 2 (ada-args2 d-result d-x17))
        (ada-bind done)))))

;; An `f64` operation the machine does.
(define adq-f64 (subr da-assembles (int int int string) unit)
  (lambda (i op pn what)
    (cond ((string=? what "from-int") (adr-f64-of-int pn))
          ((string=? what "->int") (adr-int-of-f64 pn))
          (else (adr-f64-fast what (if (= op rop-prim2) (adp-o i 1) d-result))))))

;; An `i64` or `u64` operation: its operands raw where it takes them so, a
;; constant made so here. A shift's count is an `int`, a bignum maybe: its
;; low bits, as a fixnum's are, in a copy.
(define adq-count-of (subr da-assembles () unit)
  (lambda () (begin (adr-unbox-reg d-x17) (ada-e (arm-lsl-imm d-x17 d-x17 3)))))
(define adq-int (subr da-assembles (int int bool string) unit)
  (lambda (i op signed what)
    (let* ((count (or (string=? what "-shl") (string=? what "-shr")))
           (y (cond ((and (= op rop-prim2) count)
                     (begin (ada-mov d-x17 (adp-o i 1)) (adq-count-of) d-x17))
                    ((= op rop-prim2) (adp-o i 1))
                    ((= op rop-prim2imm)
                     (begin
                       (cond ((and (adp-ofix? i 1) (not count)) (ada-imm d-x17 (adp-o i 1)))
                             ((adp-oimm? i 1) (ada-imm d-x17 (adp-ob i 1)))
                             (else
                              (begin (ada-ldr-field d-x17 (adp-field (adp-const-of (adp-oid i 1))))
                                     (if count (adq-count-of) (adr-unbox-reg d-x17)))))
                       d-x17))
                    (else d-x17))))
      (let ((c (adr-compare signed what))
            (j (adp-branch-on (- (get adp-si) 1))))
        (cond ((string=? what "->int") (adr-box-reg d-result signed))
              ;; A test that only a branch reads, as `op2`'s.
              ((and (>= c 0) (>= j 0))
               (begin
                 (ada-e (arm-cmp d-result y))
                 (ada-bind (adp-label j))
                 (let ((l (adp-edge (get adp-si) (adp-branch-to j))))
                   (ada-bc (if (= (adp-op j) rop-brancht) c (ada-not c)) l))
                 (set adp-si (+ (get adp-si) 1))))
              (else (adr-raw-fast signed what y)))))))

;; Any other: its fast path in line, else, and when that fails, the call-out.
(define adq-general (subr da-assembles (int int int string) unit)
  (lambda (i op pn pname)
    (let* ((y (cond ((= op rop-prim2) (adp-o i 1))
                    ((= op rop-prim2imm) (begin (adq-constant d-x17 i 1) d-x17))
                    (else d-x17)))
           (slow (ada-label))
           (done (ada-label))
           (fast-path (adq-pure-fast pname y slow)))
      (begin
        ;; A fast path that never fails has no slow one.
        (if (or (not fast-path) (ada-used? slow))
            (begin
              (if fast-path (ada-b done) #u)
              (ada-bind slow)
              (if (= op rop-prim1)
                  (adq-pure-call pn 1 (ada-args1 d-result))
                  (adq-pure-call pn 2 (ada-args2 d-result y))))
            #u)
        (ada-bind done)))))

;;; ------------------------------------------------------------ `prim3imm`

;; Of three, `RESULT`, a constant and `REGk`, one that never collects: a
;; blobref's element, write or variant in line, where its fast path can;
;; else the primitive, a raw `f64` boxed for it in a copy.
(define adq-prim3 (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((pn (adp-o i 0)) (pname (d-prim-name pn)) (k (adp-o i 2)))
      (if (not (d-never-collects? pn))
          (adp-decline (adq-cat4 "`prim3imm` of `" pname "`, " "which may collect"))
          (let* ((z k)
                 (raw (and (nr-is-f64-set? (get adp-cells) i)
                           (= (nr-rep (adp-in (- (get adp-si) 1)) k) nr-f64)))
                 (slow (ada-label))
                 (done (ada-label))
                 (c (adp-o i 1)))
            (begin
              (cond ((not (adp-ofix? i 1)) #u)
                    ((string=? pname "%fx26-blobref-index") (adf-blobref-index c z slow))
                    ((string=? pname "%fx26-suffix-ref-set!") (adf-suffix-store c z raw slow))
                    ((string=? pname "%fx26-flat-variant!") (adf-flat-variant c z slow))
                    (else #u))
              (if (ada-used? slow) (ada-b done) #u)
              (ada-bind slow)
              (let ((z (if raw (begin (ada-mov d-x12 z) (adr-box-f64 d-x12) d-x12) z)))
                (begin
                  (adq-constant d-x17 i 1)
                  (adq-pure-call pn 3 (ada-args3 d-result d-x17 z))))
              (ada-bind done)))))))

;;; ------------------------------------------------------------ call-outs

;; What a `prim`, `cellular` or `lambda` calls out to, as a call-out's code
;; (`fx::callout_code`) and its arity; -1 where it cannot be compiled (and
;; why noted). A `lambda`'s code field noted in `adq-code-field`.
(define adq-code-field (ref int @k) (new -1))
(define adq-what (subr da-assembles (int int) (productof (1 int) (2 int)))
  (lambda (i op)
    (let ((k0 (adp-o i 0)) (n (adp-o i 1)) (none (product (1 -1) (2 0))))
      (cond
        ((= op rop-lambda)
         (if (= (array-ref (get adp-kind) i) -1)
             (begin (adq-error-at i) none)
             (begin (set adq-code-field (adp-field (adp-code-of (array-ref (get adp-a) i))))
                    (product (1 (ada-co d-co-closure n 0)) (2 n)))))
        ((and (= op rop-cellular) (= k0 routine-cons) (= n 2))
         (product (1 (ada-co d-co-cons 0 0)) (2 2)))
        ((and (= op rop-cellular) (string=? (d-routine-name k0) "rest") (= n 0))
         (product (1 (ada-co d-co-rest 0 0)) (2 0)))
        ((and (= op rop-cellular) (string=? (d-routine-name k0) "field@") (= n 2))
         (product (1 (ada-co d-co-field-ref 0 0)) (2 2)))
        ((= op rop-prim)
         (let ((name (d-prim-name k0)))
           (cond ((or (string=? name "%region-closure") (string=? name "%region-nclosure"))
                  (product (1 (ada-co d-co-region-closure n 0)) (2 n)))
                 ((string=? name "%stay-cellular")
                  (begin (adp-decline "it calls `stay-cellular`") none))
                 ((and (>= (d-prim-min k0) 0) (>= n (d-prim-min k0))
                       (or (< (d-prim-max k0) 0) (<= n (d-prim-max k0))))
                  (product (1 (ada-co d-co-prim k0 n)) (2 n)))
                 ((string=? name "?")
                  (begin (adp-decline (string-append "primitive " (int->string k0))) none))
                 (else (begin (adp-decline (adq-cat4 "the primitive `" name "`" "")) none)))))
        (else (begin (adp-decline (adq-cat4 "the routine `" (d-routine-name k0) "`" "")) none))))))
;; The procedure's error at cell `i`, as Rust found it.
(define adq-error-at (subr da-assembles (int) unit)
  (lambda (i)
    (letrec ((nth (subr da-reads (da-strings int) string)
               (lambda (l k) (if (= k 0) (car l) (nth (cdr l) (- k 1))))))
      (ada-fail (nth (get adp-errors) (array-ref (get adp-a) i))))))

;; A call-out: to Rust, on Rust's stack, which may collect; everything
;; live is in the frame by then, and the arguments go through the state.
;; What can be is done in line first.
(define adq-callouts (subr da-assembles (int int) unit)
  (lambda (i op)
    (begin
      (set adq-code-field -1)
      (let ((w (adq-what i op)))
        (if (< (extract w 1) 0)
            #u
            (let* ((c (extract w 1))
                   ;; A leaf may make a closure: its slow path makes a frame
                   ;; of its own around the call-out.
                   (leaf-closure (and (< (get adp-frame) 0) (= (bitwise-and c 31) d-co-closure))))
              (if (and (< (get adp-frame) 0) (not leaf-closure))
                  (adp-decline "a call-out outside a frame")
                  (adq-callouts-made i c (extract w 2) leaf-closure))))))))

;; Whether call-out `c` is a primitive's named `want` of `n` arguments.
(define adq-prim-is? (subr da-reads (int string int) bool)
  (lambda (c want n)
    (and (= (bitwise-and c 31) d-co-prim)
         (= (quotient c (* 32 4096)) n)
         (string=? (d-prim-name (bitwise-and (quotient c 32) 4095)) want))))
(define adq-prim-name-of (subr da-reads (int) string)
  (lambda (c)
    (if (= (bitwise-and c 31) d-co-prim) (d-prim-name (bitwise-and (quotient c 32) 4095)) "")))

(define adq-callouts-made (subr da-assembles (int int int bool) unit)
  (lambda (i c arity leaf-closure)
    (let* ((done (ada-label))
           (slow (ada-label))
           (raw-store (= (nr-rep (adp-in (- (get adp-si) 1)) 3) nr-f64))
           (kind (bitwise-and c 31))
           (n (bitwise-and (quotient c 32) 4095))
           (pname (adq-prim-name-of c)))
      (begin
        (adq-inline c kind pname arity raw-store slow done)
        (ada-bind slow)
        (if (and raw-store (adq-prim-is? c "%fx26-flatarray-set!" 3)) (adr-box-f64 3) #u)
        ;; A closure the free space had no room for: the machine's common
        ;; routine makes it.
        (if (and (= kind d-co-closure) (>= (get adq-code-field) 0))
            (begin
              ;; The return address kept, and a frame for the collector to
              ;; walk, with nothing in it.
              (if leaf-closure (ada-push-frame d-link d-stub-frame) #u)
              (ada-ldr-field d-x17 (get adq-code-field))
              (ada-e (arm-movz d-x9 n 0))
              (ada-ld d-x16 d-st d-st-closure)
              (ada-e (arm-blr d-x16))
              (if leaf-closure (ada-pop-frame d-stub-frame) #u))
            (adq-callout c arity))
        (ada-bind done)))))

;; What is done in line before the call-out, to `done`, or on to `slow`.
(define adq-inline (subr da-assembles (int int string int bool int int) unit)
  (lambda (c kind pname arity raw-store slow done)
    (begin
      (if (adq-prim-is? c "%region-cons" 3) (adq-region-cons slow done) #u)
      ;; Boxes and arrays of at most `ARRAY_INLINE` fields, in the heap or
      ;; in a region's chunk: `new`, `make-array`, `rnew`, `rmake-array`.
      (if (adq-prim-is? c "%make-box" 1)
          (begin (adq-heap-slot) (ada-e (arm-add-imm d-x16 d-x14 3)) (adq-room slow)
                 (adq-box-at 1 done))
          #u)
      (if (adq-prim-is? c "%make-bloblet-filled" 3)
          (begin (ada-e (arm-cmp-imm 1 0)) (ada-bc ada-c-ne slow) (adq-array-words slow)
                 (adq-heap-slot) (adq-array-fill) (adq-room slow) (adq-array-at done))
          #u)
      (if (adq-prim-is? c "%region-new" 2)
          (begin (adq-region-slot slow) (ada-e (arm-add-imm d-x16 d-x14 3)) (adq-room slow)
                 (adq-box-at 2 done))
          #u)
      (if (adq-prim-is? c "%region-make-array" 3)
          (begin (adq-array-words slow) (adq-region-slot slow) (adq-array-fill) (adq-room slow)
                 (adq-array-at done))
          #u)
      (if (adq-prim-is? c "%fx26-flatarray-set!" 3) (adf-flat-set slow done raw-store) #u)
      (if (adq-prim-is? c "%fx26-bytevector-u8-set!" 3) (adf-bytes-set slow done) #u)
      (if (adq-prim-is? c "%fx26-suffix-ref-set!" 3) (adf-suffix-set slow done) #u)
      (if (adq-prim-is? c "%fx26-suffix-ref-index" 3)
          (begin (adf-suffix-index slow) (ada-b done))
          #u)
      (if (adq-prim-is? c "string=?" 2) (begin (adq-string-eq 1 2) (ada-b done)) #u)
      ;; `int`'s bit operations of fixnums.
      (if (or (string=? pname "%fx26-bitwise-and") (string=? pname "%fx26-bitwise-ior")
              (string=? pname "%fx26-bitwise-xor") (string=? pname "%fx26-bitwise-not"))
          (adq-bitwise pname arity slow done)
          #u)
      ;; A mutable bloblet of no suffix (`%make-bloblet`).
      (if (and (string=? pname "%make-bloblet") (>= arity 1) (<= arity d-regs))
          (begin
            (ada-e (arm-cmp-imm 1 0))
            (ada-bc ada-c-ne slow)
            (adq-bump (+ 1 arity) slow)
            (ada-sto d-x16 d-x13 0)
            (ada-imm d-x15 (ada-header d-kind-bloblet arity 0))
            (ada-sto d-x15 d-x11 0)
            (adq-fields-from 2 arity arity)
            (adq-bloblet-done arity done))
          #u)
      ;; A sum or product (`%make-frozen`).
      (if (and (string=? pname "%make-frozen") (>= arity 2) (<= arity d-regs))
          (adq-frozen arity slow done)
          #u)
      (if (= kind d-co-cons)
          (begin
            (adq-bump 2 slow)
            (ada-e (arm-stp 1 2 d-x11 0))
            (ada-sto d-x16 d-x13 0)
            (ada-e (arm-add-imm d-result d-x11 d-tag-pair))
            (ada-b done))
          #u)
      ;; Field `x2` (8k) of the bloblet in `x1`, 2 ≤ k ≤ F.
      (if (= kind d-co-field-ref)
          (begin
            (adq-field-in-range slow)
            (ada-e (arm-sub d-x11 1 2))
            (ada-e (arm-ldur d-result d-x11 -4))
            (ada-b done))
          #u)
      (if (adq-prim-is? c "%bloblet-set!" 3) (adq-bloblet-set slow done) #u)
      ;; A native closure over REG1…REGn from the free space.
      (if (and (= kind d-co-closure) (>= (get adq-code-field) 0) (<= arity 8))
          (adq-closure arity slow done)
          #u))))

;; `rcons`, in the region's current chunk when its handle (in `x1`) has a
;; slot in the heap's table and the chunk has room: its fill bumped by two
;; words.
(define adq-region-cons (subr da-assembles (int int) unit)
  (lambda (slow done)
    (begin
      (adq-region-slot slow)
      (ada-e (arm-add-imm d-x16 d-x14 2))
      (ada-e (arm-cmp d-x16 d-x15))
      (ada-bc ada-c-hi slow)
      (ada-ld d-x9 d-st d-st-words)
      (ada-e (arm-add-lsl d-x11 d-x9 d-x14 3))
      (ada-e (arm-stp 2 3 d-x11 0))
      (ada-sto d-x16 d-x13 0)
      (ada-e (arm-add-imm d-result d-x11 d-tag-pair))
      (ada-b done))))
;; The region in `x1`'s slot in the heap's table (at X13, its fill in X14,
;; its end in X15), when it has one: else `slow`.
(define adq-region-slot (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (ada-e (arm-tst-low 1 3))
      (ada-bc ada-c-ne slow)
      (ada-e (arm-cmp-imm 1 (* 8 d-region-slots)))
      (ada-bc ada-c-hs slow)
      (ada-ld d-x13 d-st d-st-region-table)
      (ada-e (arm-add-lsl d-x13 d-x13 1 1))
      (ada-e (arm-ldp d-x14 d-x15 d-x13 0)))))
;; The heap's free space: its top's place at X13, its fill in X14, the
;; collection's threshold in X15.
(define adq-heap-slot (subr da-assembles () unit)
  (lambda ()
    (begin (ada-ld d-x13 d-st d-st-top) (ada-ld d-x14 d-x13 0)
           (ada-ld d-x15 d-st d-st-alloc-limit))))
;; Room to the fill in X16, short of X15: at X11, the fill bumped; else
;; `slow`. Uses X9.
(define adq-room (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (ada-e (arm-cmp d-x16 d-x15))
      (ada-bc ada-c-hi slow)
      (ada-ld d-x9 d-st d-st-words)
      (ada-e (arm-add-lsl d-x11 d-x9 d-x14 3))
      (ada-sto d-x16 d-x13 0))))
;; `n` words from the heap's free space, short of the collection's
;; threshold: at X11, the fill to be in X16 (stored by the caller); else
;; `slow`.
(define adq-bump (subr da-assembles (int int) unit)
  (lambda (n slow)
    (begin
      (adq-heap-slot)
      (ada-e (arm-add-imm d-x16 d-x14 n))
      (ada-e (arm-cmp d-x16 d-x15))
      (ada-bc ada-c-hi slow)
      (ada-ld d-x9 d-st d-st-words)
      (ada-e (arm-add-lsl d-x11 d-x9 d-x14 3)))))
;; A box of `v` at X11, its room had: header, field, trailer.
(define adq-box-at (subr da-assembles (int int) unit)
  (lambda (v done)
    (begin
      (ada-imm d-x15 (ada-header d-kind-box 2 0))
      (ada-e (arm-stp d-x15 v d-x11 0))
      (ada-imm d-x15 (ada-trailer 2))
      (ada-sto d-x15 d-x11 16)
      (ada-e (arm-add-imm d-result d-x11 (+ 24 d-tag-bloblet)))
      (ada-b done))))
;; `8n` in `x2` a length to make in line: else `slow`.
(define adq-array-words (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (ada-e (arm-tst-low 2 3))
      (ada-bc ada-c-ne slow)
      (ada-e (arm-cmp-imm 2 (* 8 d-array-inline)))
      (ada-bc ada-c-hi slow))))
;; Its room: `n + 2` words, the fill in X16.
(define adq-array-fill (subr da-assembles () unit)
  (lambda ()
    (begin (ada-e (arm-lsr-imm d-x16 2 3)) (ada-e (arm-add d-x16 d-x16 d-x14))
           (ada-e (arm-add-imm d-x16 d-x16 2)))))
;; An array of `8n` (in `x2`) at X11, its room had, each field `x3`: a
;; bloblet of `n + 1` fields, the trailer one of them. Uses X9, X15, X17.
(define adq-array-at (subr da-assembles (int) unit)
  (lambda (done)
    (let* ((fill (ada-label)) (filled (ada-label)))
      (begin
        (ada-e (arm-lsl-imm d-x15 2 (- d-h-fields-lo 3)))
        (ada-imm d-x17 (ada-header d-kind-bloblet 1 0))
        (ada-e (arm-add d-x15 d-x15 d-x17))
        (ada-sto d-x15 d-x11 0)
        (ada-e (arm-add d-x17 d-x11 2))
        (ada-e (arm-add-imm d-x15 2 (+ 8 d-tag-trailer)))
        (ada-sto d-x15 d-x17 8)
        (ada-mov d-x9 2)
        (ada-bind fill)
        (ada-e (arm-cmp-imm d-x9 0))
        (ada-bc ada-c-eq filled)
        (ada-e (arm-add d-x17 d-x11 d-x9))
        (ada-sto 3 d-x17 0)
        (ada-e (arm-sub-imm d-x9 d-x9 8))
        (ada-b fill)
        (ada-bind filled)
        (ada-e (arm-add d-x17 d-x11 2))
        (ada-e (arm-add-imm d-result d-x17 (+ 16 d-tag-bloblet)))
        (ada-b done)))))

;; Fields `x2`…`xn` of the bloblet of `total` fields at X11.
(define adq-fields-from (subr da-assembles (int int int) unit)
  (lambda (j n total)
    (if (> j n)
        #u
        (begin (ada-sto j d-x11 (* 8 (- (+ 1 total) j))) (adq-fields-from (+ j 1) n total)))))
;; Its trailer, and `RESULT` the bloblet.
(define adq-bloblet-done (subr da-assembles (int int) unit)
  (lambda (total done)
    (begin
      (ada-imm d-x15 (ada-trailer total))
      (ada-sto d-x15 d-x11 (* 8 total))
      (ada-e (arm-add-imm d-result d-x11 (+ (* 8 (+ 1 total)) d-tag-bloblet)))
      (ada-b done))))

;; `int`'s bit operations of fixnums: of two, `and`, `ior` and `xor`; `not`
;; of one, its tag's bits cleared. A bignum calls out.
(define adq-bitwise (subr da-assembles (string int int int) unit)
  (lambda (name n slow done)
    (begin
      (if (= n 2)
          (begin (ada-e (arm-orr d-x13 1 2)) (ada-e (arm-tst-low d-x13 3)))
          (ada-e (arm-tst-low 1 3)))
      (ada-bc ada-c-ne slow)
      (cond ((string=? name "%fx26-bitwise-and") (ada-e (arm-and d-result 1 2)))
            ((string=? name "%fx26-bitwise-ior") (ada-e (arm-orr d-result 1 2)))
            ((string=? name "%fx26-bitwise-xor") (ada-e (arm-eor d-result 1 2)))
            (else (begin (ada-e (arm-sub d-result d-xzr 1))
                         (ada-e (arm-sub-imm d-result d-result 8)))))
      (ada-b done))))

;; A sum or product (`%make-frozen`, `x1` its kind) of `total` fields: its
;; header, frozen fields and suffix; its fields from `x2`…; its trailer.
(define adq-frozen-header (subr pure (int int) int)
  (lambda (kind total)
    (+ (ada-header kind total 0)
       (+ (arithmetic-shift 1 d-h-fields-frozen-lo) (arithmetic-shift 1 d-h-suffix-frozen-lo)))))
(define adq-frozen (subr da-assembles (int int int) unit)
  (lambda (total slow done)
    (let* ((sum (ada-label)) (kinded (ada-label)))
      (begin
        (ada-imm d-x15 (ada-fixnum d-kind-sum))
        (ada-e (arm-cmp 1 d-x15))
        (ada-bc ada-c-eq sum)
        (ada-imm d-x15 (ada-fixnum d-kind-product))
        (ada-e (arm-cmp 1 d-x15))
        (ada-bc ada-c-ne slow)
        (ada-imm d-x17 (adq-frozen-header d-kind-product total))
        (ada-b kinded)
        (ada-bind sum)
        (ada-imm d-x17 (adq-frozen-header d-kind-sum total))
        (ada-bind kinded)
        (adq-bump (+ 1 total) slow)
        (ada-sto d-x16 d-x13 0)
        (ada-sto d-x17 d-x11 0)
        (adq-fields-from 2 total total)
        (adq-bloblet-done total done)))))

;; Field `x2` (8k) of the bloblet in `x1` in range, 2 ≤ k ≤ F, its
;; trailer's distance (8F) in X16; else `slow`.
(define adq-field-in-range (subr da-assembles (int) unit)
  (lambda (slow)
    (begin
      (ada-e (arm-ldur d-x16 1 (ada-field-off 1)))
      (ada-e (arm-and-low d-x13 d-x16 3))
      (ada-e (arm-cmp-imm d-x13 d-tag-trailer))
      (ada-bc ada-c-ne slow)
      (ada-e (arm-cmp-imm 2 16))
      (ada-bc ada-c-lt slow)
      (ada-e (arm-sub-imm d-x16 d-x16 d-tag-trailer))
      (ada-e (arm-cmp 2 d-x16))
      (ada-bc ada-c-gt slow))))
;; `%bloblet-set!`: `x3` into field `x2` (8k) of the bloblet in `x1`, its
;; fields not frozen.
(define adq-bloblet-set (subr da-assembles (int int) unit)
  (lambda (slow done)
    (begin
      (adq-field-in-range slow)
      ;; The header: F + 1 words before the suffix.
      (ada-e (arm-sub d-x11 1 d-x16))
      (ada-e (arm-ldur d-x13 d-x11 -12))
      (ada-e (arm-ubfx d-x13 d-x13 d-h-fields-frozen-lo 1))
      (ada-e (arm-cmp-imm d-x13 0))
      (ada-bc ada-c-ne slow)
      (ada-e (arm-sub d-x11 1 2))
      (ada-e (arm-stur 3 d-x11 -4))
      (ada-card-mark d-x11 -4 d-x13 d-x16)
      (ada-imm d-result d-unspecified)
      (ada-b done))))

;; A native closure over REG1…REGn from the free space: its header; its
;; free values, the code, and the trailer, fields counted back from where
;; it points.
(define adq-closure (subr da-assembles (int int int) unit)
  (lambda (n slow done)
    (let ((total (+ n 2)))
      (letrec ((frees (subr da-assembles (int) unit)
                 (lambda (k)
                   (if (= k n)
                       #u
                       (begin (ada-sto (+ 1 k) d-x11 (* 8 (- n k))) (frees (+ k 1)))))))
        (begin
          (adq-bump (+ total 1) slow)
          (ada-imm d-x17 (ada-header d-kind-native-closure total 0))
          (ada-sto d-x17 d-x11 0)
          (frees 0)
          (ada-ldr-field d-x17 (get adq-code-field))
          (ada-sto d-x17 d-x11 (* 8 (+ n 1)))
          (ada-imm d-x17 (ada-trailer total))
          (ada-sto d-x17 d-x11 (* 8 total))
          (ada-sto d-x16 d-x13 0)
          (ada-e (arm-add-imm d-result d-x11 (+ (* 8 (+ total 1)) d-tag-bloblet)))
          (ada-b done))))))
))))
