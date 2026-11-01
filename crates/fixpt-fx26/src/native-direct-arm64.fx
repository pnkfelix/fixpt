;;; The native convention's procedures compiled to arm64, in FX-26:
;;; `fixpt-native/src/direct.rs`'s `procedure`, step for step and
;;; instruction for instruction, over the encoder written in FX-26
;;; (`arm64.fx`), the assembler (`native-direct-arm64-asm.fx`), the analysis
;;; of representations (`native-reps.fx`), the pieces of raw values
;;; (`native-direct-arm64-raw.fx`), and the procedure's state and
;;; instructions (`-proc.fx`, `-ops.fx`, `-prims.fx`). The Rust compiler is
;;; this one's oracle: for every procedure, the same bytes, the same fields
;;; of its code bloblet and the same call-outs (`tests/native_x64.rs`, on
;;; arm64). x86_64's (`native-direct-x64.fx`).
;;;
;;; Rust keeps the driver (`direct/fx.rs`): it finds the procedures a
;;; closure reaches, binds their globals, and asks this compiler for each
;;; one's code with what `procedure` would have asked it (`prepare_x64`,
;;; which `procedure` asks alike: `native-compile-arm64-proc`); it places
;;; the code. This file is the loop over the instructions, what is placed
;;; after them, and that entry. Its steps have the Rust names, with `adx-`
;;; before them.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to its pieces.

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
           (proc (select arm-direct-types native-direct-arm64-proc-sig))
           (ops (select arm-direct-types native-direct-arm64-ops-sig))
           (prims (select arm-direct-types native-direct-arm64-prims-sig)))
    (module
(hide (include direct-types) (include arm-direct-types))
(hide (include arm) (include dl) (include layout) (include asm) (include reps) (include raw)
      (include proc) (include ops) (include prims))

(define adx-fld (subr pure (int) int) (lambda (k) (ada-field-off k)))

;; `mask` with bit `r`.
(define adx-with (subr pure (int int) int)
  (lambda (mask r) (bitwise-ior mask (arithmetic-shift 1 r))))
;; Each register `r` of `mask`, from 0, `f` of it.
(define adx-each-reg (subr da-assembles (int da-on-reg) unit)
  (lambda (mask f)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r) (if (> r 8) #u (begin (if (adp-bit? mask r) (f r) #u) (go (+ r 1)))))))
      (go 0))))
;; Each unboxing (`8r + rep`) of `us`, and each test of `cs`.
(define adx-unboxes (subr da-assembles (da-bytes) unit)
  (lambda (us)
    (if (null? us)
        #u
        (begin (adr-unbox-to (quotient (car us) 8) (modulo (car us) 8)) (adx-unboxes (cdr us))))))
(define adx-checks (subr da-assembles (da-bytes int) unit)
  (lambda (cs general)
    (if (null? cs) #u (begin (ada-check-fixnum (car cs) general) (adx-checks (cdr cs) general)))))

;;; ------------------------------------------------------------ instructions

;; Whether routine `r` is control (`cellular` of a prompt, a mark, an
;; abort, a capture or marks).
(define adx-control? (subr pure (int) bool)
  (lambda (r)
    (or (= r routine-prompt) (= r routine-withmark) (= r routine-withmark-tail)
        (= r routine-abort) (= r routine-callcc) (= r routine-callcomp) (= r routine-ncallcc)
        (= r routine-ncallcomp) (= r routine-callone) (= r routine-ncallone)
        (= r routine-firstmark) (= r routine-currentmarks) (= r routine-marksof))))

;; The instruction at cell `i`, `op`.
(define adx-instruction (subr da-assembles (int int) unit)
  (lambda (i op)
    (cond
      ((= op rop-args) #u)
      ((= op rop-vargs) (ado-vargs i))
      ((= op rop-const) (ado-const i))
      ((= op rop-global) (ado-global i))
      ((= op rop-global-guard) (ado-global-guard i))
      ((= op rop-setglbl) (ado-setglbl i))
      ((= op rop-lexical) (ado-lexical i))
      ((= op rop-reg) (ado-reg i))
      ((= op rop-setreg) (ado-setreg i))
      ((= op rop-movereg) (ado-movereg i))
      ((= op rop-save) (ado-save i))
      ((= op rop-pop) (ado-pop i))
      ((= op rop-stack) (ado-stack i))
      ((= op rop-setstk) (ado-setstk i))
      ((= op rop-load) (ado-load i))
      ((= op rop-store) (ado-store i))
      ((= op rop-op1) (ado-op1 i))
      ((or (= op rop-op2) (= op rop-op2imm)) (ado-op2 i op))
      ((= op rop-field) (ado-field i))
      ((= op rop-setfield) (ado-setfield i))
      ((and (= op rop-cellular) (adx-control? (adp-o i 0))) (adq-control i))
      ((or (= op rop-prim1) (= op rop-prim2) (= op rop-prim2imm)) (adq-prim12 i op))
      ((= op rop-prim3imm) (adq-prim3 i))
      ((or (= op rop-prim) (= op rop-cellular) (= op rop-lambda)) (adq-callouts i op))
      ((or (= op rop-invoke) (= op rop-tailinvoke)) (ado-invoke i op))
      ((= op rop-invokeself) (ado-invokeself i))
      ((= op rop-return) (ado-return i))
      ((or (= op rop-branch) (= op rop-branchf) (= op rop-brancht)) (ado-branch i op))
      (else (adp-decline (string-append "`" (string-append (d-op-name op) "`")))))))

;; Whether `op` is a call-out or call, before which the frame's map is
;; stored.
(define adx-may-collect? (subr pure (int) bool)
  (lambda (op)
    (or (= op rop-prim) (= op rop-cellular) (= op rop-lambda) (= op rop-invokeself)
        (= op rop-invoke))))

;; The instruction at index `si`: the registers the one before leaves as
;; values that are raw here unboxed, falling in; in the fixnum version,
;; those it leaves unknown that are known here tested; its conversions;
;; what registers hold of the frame; the frame's map, before what may
;; collect; and its code.
(define adx-step (subr da-assembles () unit)
  (lambda ()
    (let* ((si (get adp-si)) (i (adp-start si)) (op (adp-op i)) (at (ada-here)))
      (begin
        (if (and (> si 0)
                 (let ((before (adp-op (adp-start (- si 1)))))
                   (not (or (= before rop-branch) (= before rop-return)
                            (= before rop-tailinvoke)))))
            (begin
              (adx-unboxes (nr-unboxes (adp-out (- si 1)) (adp-in si)))
              (if (get adp-fast)
                  (adx-checks
                   (nr-checks (adp-out (- si 1)) (adp-in si) (array-ref (get adp-live) si))
                   (adp-label-g i))
                  #u))
            #u)
        (set adp-si (+ si 1))
        (ada-bind (adp-label i))
        (let ((stepped (nr-step (get adp-cells) i (array-ref (get adp-raw-refs) si) (get adp-fast)
                                (get adp-raw) (get adp-params) (array-ref (get adp-callees) si)
                                (adp-in si))))
          ;; `RESULT`, where a `reg` just before left it in its register
          ;; (`src`), is tested there.
          (adr-convert (extract stepped 1) (adp-label-g i) (get adp-src)))
        (if (array-ref (get adp-target) i) (set adp-map-stored? #f) #u)
        (ado-held-step i op at)
        ;; Before what may collect, in a frame: the slots live after it,
        ;; the code bloblet's, and the closure's if the code reads it.
        (if (and (>= (get adp-frame) 0) (array-ref (get adp-framed) i) (adx-may-collect? op))
            (let ((map (adp-map-word (array-ref (get adp-live-out) si))))
              (if (and (get adp-map-stored?) (= map (get adp-map-stored)))
                  #u
                  (begin (ada-imm d-x16 (ada-fixnum map))
                         (ada-sto d-x16 d-frame 16)
                         (set adp-map-stored? #t)
                         (set adp-map-stored map))))
            #u)
        (adx-instruction i op)))))

;; A version of the procedure: the fixnum one (`fast`) or the general one.
(define adx-version (subr da-assembles (bool) unit)
  (lambda (fast)
    (let ((io (nr-reps-of (get adp-cells) (get adp-starts) fast (get adp-raw) (get adp-params)
                          (get adp-callees))))
      (letrec ((loop (subr da-assembles () unit)
                 (lambda ()
                   (if (or (>= (get adp-si) (adp-ns)) (not (ada-ok?)))
                       #u
                       (begin (adx-step) (loop))))))
        (begin
          (set adp-fast fast)
          (set adp-reps-in (extract io 1))
          (set adp-reps-out (extract io 2))
          (set adp-src d-result)
          (set adp-pending -1)
          (set adp-bound-cell -1)
          (set adp-map-stored? #f)
          (ado-held-version fast)
          (set adp-si 0)
          (loop)
          (if (ada-ok?) (ada-bind (adp-label (get adp-n))) #u))))))

;;; ------------------------------------------------------------ after the code

;; A poll's way out at a time slice's end, as `emit_poll`: out of fuel if
;; the reserve is spent; else a frame of its own, mapped as a procedure's,
;; holding what is live, the call-out that gives the next slice, the
;; scheduler's `preempt` if it would have another task run, and back: by
;; its return if the procedure has a frame, else by a branch.
(define adx-poll (subr da-assembles (dp-poll) unit)
  (lambda (p)
    (let* ((out (extract p 1)) (back (extract p 2)) (values (extract p 3)) (raws (extract p 4))
           (clo (extract p 5)) (mapped (extract p 6))
           (mask (bitwise-ior (bitwise-ior (arithmetic-shift 1 10) values) (if clo 512 0))))
      (begin
        (ada-bind out)
        (ada-ld d-x16 d-st d-st-reserve)
        (ada-e (arm-cmp-imm d-x16 0))
        (ada-trap d-out-of-fuel ada-c-eq)
        (if mapped
            (begin
              (ada-imm d-x16 (ada-fixnum (extract p 7)))
              (ada-sto d-x16 d-frame 16)
              (ada-adr d-x17 back)
              (ada-push-frame d-x17 d-poll-frame))
            (ada-push-frame d-link d-poll-frame))
        (ada-imm d-x16 (ada-fixnum (bitwise-ior (arithmetic-shift d-poll-fields d-map-bits) mask)))
        (ada-sto d-x16 d-frame 16)
        (adx-each-reg values (lambda (r) (ada-sto r d-frame (+ 24 (* 8 r)))))
        (if clo (ada-sto d-clo d-frame (+ 24 72)) #u)
        (ada-ldr-field d-x16 1)
        (ada-sto d-x16 d-frame (+ 24 80))
        (adx-each-reg raws (lambda (r) (ada-sto r d-frame (+ d-poll-raw0 (* 8 r)))))
        (ada-sto d-x9 d-frame (+ d-poll-raw0 72))
        (ada-call-out d-poll)
        (ada-ld d-fuel d-st d-st-fuel)
        (ada-ld d-clo d-st d-st-aux)
        (let ((resume (ada-label)))
          (begin
            (ada-e (arm-cmp-imm d-clo 0))
            (ada-bc ada-c-eq resume)
            (ada-e (arm-ldur d-x16 d-clo (adx-fld d-closure-word)))
            (ada-e (arm-add d-x16 d-x16 d-delta))
            (ada-e (arm-movz d-x9 0 0))
            (ada-e (arm-blr d-x16))
            (ada-call-out d-poll-done)
            (ada-bind resume)))
        (adx-each-reg values (lambda (r) (ada-ld r d-frame (+ 24 (* 8 r)))))
        (if clo (ada-ld d-clo d-frame (+ 24 72)) #u)
        (adx-each-reg raws (lambda (r) (ada-ld r d-frame (+ d-poll-raw0 (* 8 r)))))
        (ada-ld d-x9 d-frame (+ d-poll-raw0 72))
        (ada-pop-frame d-poll-frame)
        (if mapped (ada-e arm-ret) (ada-b back))))))

;; What is placed after the code, each in the order it was noted: the
;; `int` operations' slow paths; the ways in that unbox or test (going
;; over to the general version where one is not a fixnum); then, past the
;; procedure's own code, the calls through cells whose global was
;; written, the calls of what is not native code, an abort's resumption,
;; the overflows, the polls' ways out, and the traps. The procedure's own
;; code's length, in instructions.
(define adx-after (subr da-assembles () int)
  (lambda ()
    (begin
      (letrec ((slows (subr da-assembles (adp-int-slow-list) unit)
                 (lambda (l) (if (null? l) #u (begin (adr-int-slow (car l)) (slows (cdr l))))))
               (edges (subr da-assembles (adp-edge-list) unit)
                 (lambda (l)
                   (if (null? l)
                       #u
                       (let ((e (car l)))
                         (begin (ada-bind (extract e 1))
                                (adx-unboxes (extract e 2))
                                (adx-checks (extract e 3) (extract e 5))
                                (ada-b (extract e 4))
                                (edges (cdr l))))))))
        (begin (slows (the adp-int-slow-list (reverse (get adp-int-slows))))
               (edges (the adp-edge-list (reverse (get adp-edges))))))
      (let ((own (ada-here)))
        (begin
          (adx-cell-slows (the adp-cell-slow-list (reverse (get adp-cell-slows))))
          (adx-foreign (the adp-foreign-list (reverse (get adp-foreign))))
          (if (get adp-uses-resume) (begin (ada-bind (get adp-resume-at)) (ada-resume)) #u)
          (adx-overflows (the adp-overflow-list (reverse (get adp-overflows)))
                         (if (get adp-captures) (get adp-info-captures) (get adp-info)))
          (adx-polls (the adp-poll-list (reverse (get adp-polls))))
          (ada-place-stubs)
          own)))))

;; Not the procedure known: what the cell holds takes values, and its
;; code runs.
(define adx-cell-slows (subr da-assembles (adp-cell-slow-list) unit)
  (lambda (l)
    (if (null? l)
        #u
        (let ((c (car l)))
          (begin
            (ada-bind (extract c 1))
            (adx-each-reg (extract c 3) adr-box-f64)
            (ada-e (arm-ldur d-x16 d-clo (adx-fld d-closure-word)))
            (ada-b (extract c 2))
            (adx-cell-slows (cdr l)))))))
;; Each call of what is not native code: to the machine's common routine
;; (`common_foreign`), with the arguments' count; a tail call goes there
;; to return from it to this procedure's caller.
(define adx-foreign (subr da-assembles (adp-foreign-list) unit)
  (lambda (l)
    (if (null? l)
        #u
        (let ((f (car l)))
          (begin
            (ada-bind (extract f 1))
            (ada-e (arm-movz d-x9 (extract f 3) 0))
            (ada-ld d-x16 d-st d-st-foreign)
            (if (extract f 4)
                (ada-e (arm-br d-x16))
                (begin (ada-e (arm-blr d-x16)) (ada-b (extract f 2))))
            (adx-foreign (cdr l)))))))
;; The arguments it keeps are values: those raw boxed around it. Through
;; the link, which the frame holds already: X9 may be a variadic
;; procedure's count.
(define adx-overflows (subr da-assembles (adp-overflow-list int) unit)
  (lambda (l info)
    (if (null? l)
        #u
        (let ((o (car l)))
          (begin
            (ada-bind (extract o 1))
            (adx-each-reg (extract o 3) adr-box-f64)
            (ada-ldr-field d-x16 1)
            (ada-imm d-x17 info)
            (ada-ld d-link d-st d-st-overflow)
            (ada-e (arm-blr d-link))
            (adx-each-reg (extract o 3) adr-unbox-f64)
            (ada-b (extract o 2))
            (adx-overflows (cdr l) info))))))
(define adx-polls (subr da-assembles (adp-poll-list) unit)
  (lambda (l) (if (null? l) #u (begin (adx-poll (car l)) (adx-polls (cdr l))))))

;;; ------------------------------------------------------------ the procedure

;; Its entry: the raw parameters unboxed, then, with a frame or a call, a
;; poll keeping the arguments live (all, for a variadic procedure, whose
;; count is in X9, which the poll keeps too), raw or not.
(define adx-entry (subr da-assembles (int) unit)
  (lambda (entry)
    (let ((checked (ada-label)))
      (letrec ((unbox (subr da-assembles (int) unit)
                 (lambda (r)
                   (if (> r 8)
                       #u
                       (begin (if (nr-raw-param? (get adp-params) r) (adr-unbox-f64 r) #u)
                              (unbox (+ r 1)))))))
        (begin
          (ada-bind entry)
          (unbox 1)
          (set adp-entry-checked checked)
          (ada-bind checked)
          (if (or (get adp-calls) (>= (get adp-frame) 0))
              (let* ((first (adp-start 0))
                     (n (if (= (adp-op first) rop-args) (min (adp-o first 0) 8) 8))
                     (out (ada-label))
                     (back (ada-label)))
                (letrec ((masks (subr da-reads (int int int) (productof (1 int) (2 int)))
                           (lambda (r raws values)
                             (cond ((> r n) (product (1 raws) (2 values)))
                                   ((nr-raw-param? (get adp-params) r)
                                    (masks (+ r 1) (adx-with raws r) values))
                                   (else (masks (+ r 1) raws (adx-with values r)))))))
                  (let ((m (masks 1 0 0)))
                    (begin
                      (ada-e (arm-subs-imm d-fuel d-fuel 1))
                      (ada-bc ada-c-lo out)
                      (ada-bind back)
                      (set adp-polls
                           (cons (product (1 out) (2 back) (3 (extract m 2)) (4 (extract m 1))
                                          (5 (get adp-captures)) (6 #f) (7 0))
                                 (get adp-polls)))))))
              #u))))))

;; `n` labels, as an array.
(define adx-labels (subr da-assembles (int) da-ints)
  (lambda (n)
    (let ((a (the da-ints (make-array n 0))))
      (letrec ((fill (subr da-assembles (int) unit)
                 (lambda (k) (if (= k n) #u (begin (array-set! a k (ada-label)) (fill (+ k 1)))))))
        (begin (fill 0) a)))))

;; Where label `l` is, in bytes, or -1 if it was never placed.
(define adx-offset (subr da-reads (int) int)
  (lambda (l) (let ((w (ada-label-at l))) (if (< w 0) -1 (* 4 w)))))
;; Where each instruction starts in the code, both versions' (`Proc::starts`):
;; each offset and the instruction's cell, flat, from instruction `si` down.
(define adx-starts (subr da-assembles (int da-bytes) da-bytes)
  (lambda (si acc)
    (if (< si 0)
        acc
        (let* ((i (adp-start si))
               (g (adx-offset (array-ref (get adp-labels-g) i)))
               (f (adx-offset (array-ref (get adp-labels-f) i)))
               (with-f (if (>= f 0) (the da-bytes (cons f (cons i acc))) acc)))
          (adx-starts (- si 1) (if (>= g 0) (the da-bytes (cons g (cons i with-f))) with-f))))))

;; Each load of a call-out's number given its field (`Asm::callout_fields`).
(define adx-callout-fields (subr da-assembles (da-pairs) unit)
  (lambda (ls)
    (if (null? ls)
        #u
        (let ((k (adp-field (adp-callout-of (extract (car ls) 2)))))
          (begin (ada-callout-field (extract (car ls) 1) k) (adx-callout-fields (cdr ls)))))))

;; A procedure's code, as `procedure` makes it, of what Rust gave of it
;; (`FxRequest`: its name, its lists in order, and the messages its
;; failures noted at instructions name): its bytes, how many are its own,
;; its code bloblet's fields (as `direct/fx.rs`'s `field_of` reads them),
;; the call-outs it numbered, why it cannot be compiled ("" if it can;
;; the call-outs numbered until then are the Rust compiler's too), and
;; where each instruction starts (`adx-starts`).
(define native-compile-arm64-proc
  (subr da-assembles (string (listof da-bytes @k) da-strings) dx-made)
  (lambda (name lists errors)
    (begin
      (adp-begin name lists errors)
      (adp-analyse)
      (if (ada-ok?)
          (let ((entry (ada-label)))
            (begin
              (set adp-labels-g (adx-labels (+ (get adp-n) 1)))
              (set adp-resume-at (ada-label))
              (adx-entry entry)
              (set adp-labels-f (adx-labels (+ (get adp-n) 1)))
              (if (get adp-has-int) (adx-version #t) #u)
              (if (ada-ok?) (adx-version #f) #u)))
          #u)
      (if (ada-ok?)
          (let* ((own (adx-after))
                 (placed (adx-callout-fields (ada-callout-loads-made)))
                 (code (ada-finish)))
            (product (1 code) (2 (* 4 own)) (3 (the da-bytes (reverse (get adp-fields))))
                     (4 (ada-callouts)) (5 (ada-err))
                     (6 (adx-starts (- (adp-ns) 1) (the da-bytes nil)))))
          (product (1 (the da-bytes nil)) (2 0) (3 (the da-bytes nil)) (4 (ada-callouts))
                   (5 (ada-err)) (6 (the da-bytes nil)))))))
)))
