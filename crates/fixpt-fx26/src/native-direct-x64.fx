;;; The native convention's procedures compiled to x86_64, in FX-26:
;;; `fixpt-native/src/direct/x64.rs`'s `procedure_x64`, step for step and
;;; instruction for instruction, over the encoder written in FX-26
;;; (`x86_64.fx`), the assembler (`native-direct-x64-asm.fx`), the analysis
;;; of representations (`native-reps.fx`), the pieces of raw values and of
;;; the heap (`native-direct-x64-raw.fx`, `-flat.fx`), and the procedure's
;;; state and instructions (`-proc.fx`, `-ops.fx`, `-prims.fx`). The Rust
;;; compiler is this one's oracle: for every procedure, the same bytes, the
;;; same fields of its code bloblet and the same call-outs
;;; (`tests/native_x64.rs`).
;;;
;;; Rust keeps the driver (`direct/fx.rs`): it finds the procedures a
;;; closure reaches, binds their globals, and asks this compiler for each
;;; one's code with what `procedure_x64` would have asked it
;;; (`native-compile-x64-proc`); it places the code. This file is the loop
;;; over the instructions, what is placed after them, and that entry. Its
;;; steps have the Rust names, with `dx-` before them.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to its pieces.

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
           (proc (select direct-types native-direct-x64-proc-sig))
           (ops (select direct-types native-direct-x64-ops-sig))
           (prims (select direct-types native-direct-x64-prims-sig)))
    (module
(hide (include direct-types))
(hide (include x86) (include dl) (include layout) (include asm) (include reps) (include raw)
      (include proc) (include ops) (include prims))

(define dx-fld (subr pure (int) int) (lambda (k) (da-field-off k)))

;; `mask` with bit `r`.
(define dx-with (subr pure (int int) int)
  (lambda (mask r) (bitwise-ior mask (arithmetic-shift 1 r))))
;; Each register `r` of `mask`, from 0, `f` of it.
(define dx-each-reg (subr da-assembles (int da-on-reg) unit)
  (lambda (mask f)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r) (if (> r 8) #u (begin (if (dp-bit? mask r) (f r) #u) (go (+ r 1)))))))
      (go 0))))
;; Each unboxing (`8r + rep`) of `us`, and each test of `cs`.
(define dx-unboxes (subr da-assembles (da-bytes) unit)
  (lambda (us)
    (if (null? us)
        #u
        (begin (dr-unbox-to (quotient (car us) 8) (modulo (car us) 8)) (dx-unboxes (cdr us))))))
(define dx-checks (subr da-assembles (da-bytes int) unit)
  (lambda (cs general)
    (if (null? cs) #u (begin (da-check-fixnum (car cs) general) (dx-checks (cdr cs) general)))))

;;; ------------------------------------------------------------ instructions

;; Whether routine `r` is control (`cellular` of a prompt, a mark, an
;; abort, a capture or marks).
(define dx-control? (subr pure (int) bool)
  (lambda (r)
    (or (= r routine-prompt) (= r routine-withmark) (= r routine-withmark-tail)
        (= r routine-abort) (= r routine-callcc) (= r routine-callcomp) (= r routine-ncallcc)
        (= r routine-ncallcomp) (= r routine-callone) (= r routine-ncallone)
        (= r routine-firstmark) (= r routine-currentmarks) (= r routine-marksof))))

;; A field's displacement: any field's, in 32 bits.
(define dx-field-off (subr da-assembles (int) int) (lambda (k) (dx-fld k)))

;; The instruction at cell `i`, `op`.
(define dx-instruction (subr da-assembles (int int) unit)
  (lambda (i op)
    (cond
      ((= op rop-args) #u)
      ;; Entered with any number of arguments, their count in X9: it and
      ;; the registers into the state, for `rest` to list.
      ((= op rop-vargs) (begin (da-sto d-st d-st-nargs d-x9) (da-regs-to-args 8)))
      ((= op rop-const) (do-const i))
      ((= op rop-global) (do-global i))
      ((= op rop-global-guard) (do-global-guard i))
      ((= op rop-setglbl) (do-setglbl i))
      ((= op rop-lexical) (do-lexical i))
      ((= op rop-reg) (do-reg i))
      ((= op rop-setreg) (do-setreg i))
      ((= op rop-movereg) (do-movereg i))
      ((= op rop-save) (do-save i))
      ((= op rop-pop) (da-pop-frame-ret (get dp-size)))
      ((= op rop-stack) (do-stack i))
      ((= op rop-setstk) (do-setstk i))
      ((= op rop-load) (do-load i))
      ((= op rop-store) (do-store i))
      ((= op rop-op1) (dx-op1 i))
      ((or (= op rop-op2) (= op rop-op2imm)) (do-op2 i op))
      ((= op rop-field)
       (let ((off (dx-field-off (dp-o i 0)))) (if (da-ok?) (da-ld d-result d-result off) #u)))
      ((= op rop-setfield)
       (let ((off (dx-field-off (dp-o i 0))))
         (if (da-ok?)
             (begin (da-store-reg d-result off (dp-o i 1) d-x11)
                    (da-card-mark d-result off d-x16 d-x17))
             #u)))
      ((and (= op rop-cellular) (dx-control? (dp-o i 0))) (dq-control i))
      ((or (= op rop-prim1) (= op rop-prim2) (= op rop-prim2imm)) (dq-prim12 i op))
      ((= op rop-prim3imm) (dq-prim3 i))
      ((or (= op rop-prim) (= op rop-cellular) (= op rop-lambda)) (dq-callouts i op))
      ((or (= op rop-invoke) (= op rop-tailinvoke)) (do-invoke i op))
      ((= op rop-invokeself) (do-invokeself i))
      ((= op rop-return)
       (if (= (nr-rep (dp-in (- (get dp-si) 1)) 0) nr-f64) (dr-raw-return) (da-e (x86-ret))))
      ((or (= op rop-branch) (= op rop-branchf) (= op rop-brancht)) (do-branch i op))
      (else (dp-decline (string-append "`" (string-append (d-op-name op) "`")))))))

;; A list may be `nil`: `car` of it traps.
(define dx-op1 (subr da-assembles (int) unit)
  (lambda (i)
    (let ((r (dp-o i 0)))
      (if (or (= r routine-pair-car) (= r routine-pair-cdr))
          (begin
            (da-mov d-x16 d-result)
            (da-e (x86-alu-imm da-and d-x16 7))
            (da-e (x86-alu-imm da-cmp d-x16 d-tag-pair))
            (da-trap d-not-a-pair da-c-ne)
            (da-ld d-result d-result (if (= r routine-pair-car) -1 7)))
          (dp-decline (string-append "op1 " (d-routine-name r)))))))

;; Whether `op` is a call-out or call, before which the frame's map is
;; stored.
(define dx-may-collect? (subr pure (int) bool)
  (lambda (op)
    (or (= op rop-prim) (= op rop-cellular) (= op rop-lambda) (= op rop-invokeself)
        (= op rop-invoke))))

;; The instruction at index `si`: the registers the one before leaves as
;; values that are raw here unboxed, falling in; in the fixnum version,
;; those it leaves unknown that are known here tested; its conversions;
;; the frame's map, before what may collect; and its code.
(define dx-step (subr da-assembles () unit)
  (lambda ()
    (let* ((si (get dp-si)) (i (dp-start si)) (op (dp-op i)) (at (da-here)))
      (begin
        (if (and (> si 0)
                 (let ((before (dp-op (dp-start (- si 1)))))
                   (not (or (= before rop-branch) (= before rop-return)
                            (= before rop-tailinvoke)))))
            (begin
              (dx-unboxes (nr-unboxes (dp-out (- si 1)) (dp-in si)))
              (if (get dp-fast)
                  (dx-checks (nr-checks (dp-out (- si 1)) (dp-in si) (array-ref (get dp-live) si))
                             (dp-label-g i))
                  #u))
            #u)
        (set dp-si (+ si 1))
        (da-bind (dp-label i))
        (let ((stepped (nr-step (get dp-cells) i (array-ref (get dp-raw-refs) si) (get dp-fast)
                                (get dp-raw) (get dp-params) (array-ref (get dp-callees) si)
                                (dp-in si))))
          ;; `RESULT`, where a `reg` just before left it in its register
          ;; (`src`), is tested there.
          (dr-convert (extract stepped 1) (dp-label-g i) (get dp-src)))
        (if (array-ref (get dp-target) i) (set dp-map-stored? #f) #u)
        (do-held-step i op at)
        (if (and (>= (get dp-frame) 0) (array-ref (get dp-framed) i) (dx-may-collect? op))
            (let ((map (dp-map-word (array-ref (get dp-live-out) si))))
              (if (and (get dp-map-stored?) (= map (get dp-map-stored)))
                  #u
                  (begin (da-imm d-x16 (* 8 map))
                         (da-sto d-frame 16 d-x16)
                         (set dp-map-stored? #t)
                         (set dp-map-stored map))))
            #u)
        (dx-instruction i op)))))

;; A version of the procedure: the fixnum one (`fast`) or the general one.
(define dx-version (subr da-assembles (bool) unit)
  (lambda (fast)
    (let ((io (nr-reps-of (get dp-cells) (get dp-starts) fast (get dp-raw) (get dp-params)
                          (get dp-callees))))
      (letrec ((loop (subr da-assembles () unit)
                 (lambda ()
                   (if (or (>= (get dp-si) (dp-ns)) (not (da-ok?))) #u (begin (dx-step) (loop))))))
        (begin
          (set dp-fast fast)
          (set dp-reps-in (extract io 1))
          (set dp-reps-out (extract io 2))
          (set dp-src d-result)
          (set dp-pending -1)
          (set dp-bound-cell -1)
          (set dp-map-stored? #f)
          (do-held-version fast)
          (set dp-si 0)
          (loop)
          (if (da-ok?) (da-bind (dp-label (get dp-n))) #u))))))

;;; ------------------------------------------------------------ after the code

;; A poll's way out at a time slice's end, as `emit_poll`: out of fuel if
;; the reserve is spent; else a frame of its own, mapped as a procedure's,
;; holding what is live, the call-out that gives the next slice, the
;; scheduler's `preempt` if it would have another task run, and back.
(define dx-poll (subr da-assembles (dp-poll) unit)
  (lambda (p)
    (let* ((out (extract p 1)) (back (extract p 2)) (values (extract p 3)) (raws (extract p 4))
           (clo (extract p 5)) (mapped (extract p 6)) (spent (da-label))
           (mask (bitwise-ior (bitwise-ior (arithmetic-shift 1 10) values) (if clo 512 0))))
      (begin
        (da-bind out)
        (da-e (x86-alu-mi da-cmp d-st d-st-reserve 0))
        (da-stub spent d-out-of-fuel)
        (da-jcc da-c-e spent)
        (if mapped
            (begin
              (da-imm d-x16 (* 8 (extract p 7)))
              (da-sto d-frame 16 d-x16)
              (da-lea-l d-x17 back)
              (da-push-frame d-x17 d-poll-frame))
            (da-push-frame-ret d-poll-frame))
        (da-imm d-x16 (* 8 (bitwise-ior (arithmetic-shift d-poll-fields d-map-bits) mask)))
        (da-sto d-frame 16 d-x16)
        (dx-each-reg values (lambda (r) (da-store-reg d-frame (+ 24 (* 8 r)) r d-x16)))
        (if clo (da-sto d-frame (+ 24 72) d-clo) #u)
        (da-field d-x16 1)
        (da-sto d-frame (+ 24 80) d-x16)
        (dx-each-reg raws (lambda (r) (da-store-reg d-frame (+ d-poll-raw0 (* 8 r)) r d-x16)))
        (da-sto d-frame (+ d-poll-raw0 72) d-x9)
        (da-call-out d-poll)
        (da-preempt)
        (dx-each-reg values (lambda (r) (da-load-reg r d-frame (+ 24 (* 8 r)) d-x16)))
        (if clo (da-ld d-clo d-frame (+ 24 72)) #u)
        (dx-each-reg raws (lambda (r) (da-load-reg r d-frame (+ d-poll-raw0 (* 8 r)) d-x16)))
        (da-ld d-x9 d-frame (+ d-poll-raw0 72))
        (if mapped
            (begin (da-pop-frame d-poll-frame) (da-e (x86-jmp-r d-x11)))
            (begin (da-pop-frame-ret d-poll-frame) (da-jmp back)))))))

;; What is placed after the code, each in the order it was noted: the
;; `int` operations' slow paths; the ways in that unbox or test; then,
;; past the procedure's own code, the calls through cells whose global
;; was written, the calls of what is not native code, an abort's
;; resumption, the overflows, the polls' ways out, and the traps. The
;; procedure's own code's length.
(define dx-after (subr da-assembles () int)
  (lambda ()
    (begin
      (letrec ((slows (subr da-assembles (dp-int-slow-list) unit)
                 (lambda (l) (if (null? l) #u (begin (dr-int-slow (car l)) (slows (cdr l))))))
               (edges (subr da-assembles (dp-edge-list) unit)
                 (lambda (l)
                   (if (null? l)
                       #u
                       (let ((e (car l)))
                         (begin (da-bind (extract e 1))
                                (dx-unboxes (extract e 2))
                                (dx-checks (extract e 3) (extract e 5))
                                (da-jmp (extract e 4))
                                (edges (cdr l))))))))
        (begin (slows (the dp-int-slow-list (reverse (get dp-int-slows))))
               (edges (the dp-edge-list (reverse (get dp-edges))))))
      (let ((own (da-here)))
        (begin
          (dx-cell-slows (the dp-cell-slow-list (reverse (get dp-cell-slows))))
          (dx-foreign (the dp-foreign-list (reverse (get dp-foreign))))
          (if (get dp-uses-resume) (begin (da-bind (get dp-resume-at)) (da-resume)) #u)
          (dx-overflows (the dp-overflow-list (reverse (get dp-overflows)))
                        (if (get dp-captures) (get dp-info-captures) (get dp-info)))
          (dx-polls (the dp-poll-list (reverse (get dp-polls))))
          (da-place-stubs)
          own)))))

;; Not the procedure known: what the cell holds takes values, and its
;; code runs.
(define dx-cell-slows (subr da-assembles (dp-cell-slow-list) unit)
  (lambda (l)
    (if (null? l)
        #u
        (let ((c (car l)))
          (begin
            (da-bind (extract c 1))
            (dx-each-reg (extract c 3) (lambda (r) (da-in-place r dr-box-f64)))
            (da-ld d-x16 d-clo (dx-fld d-closure-word))
            (da-jmp (extract c 2))
            (dx-cell-slows (cdr l)))))))
(define dx-foreign (subr da-assembles (dp-foreign-list) unit)
  (lambda (l)
    (if (null? l)
        #u
        (let ((f (car l)))
          (begin
            (da-bind (extract f 1))
            (da-imm d-x9 (extract f 3))
            (if (extract f 4)
                (da-e (x86-jmp-m d-st -1 1 d-st-foreign))
                (begin (da-e (x86-call-m d-st d-st-foreign)) (da-jmp (extract f 2))))
            (dx-foreign (cdr l)))))))
;; The arguments it keeps are values: those raw boxed around it.
(define dx-overflows (subr da-assembles (dp-overflow-list int) unit)
  (lambda (l info)
    (if (null? l)
        #u
        (let ((o (car l)))
          (begin
            (da-bind (extract o 1))
            (dx-each-reg (extract o 3) (lambda (r) (da-in-place r dr-box-f64)))
            (da-field d-x16 1)
            (da-imm d-x17 info)
            (da-e (x86-call-m d-st d-st-overflow))
            (dx-each-reg (extract o 3) (lambda (r) (da-in-place r dr-unbox-f64)))
            (da-jmp (extract o 2))
            (dx-overflows (cdr l) info))))))
(define dx-polls (subr da-assembles (dp-poll-list) unit)
  (lambda (l) (if (null? l) #u (begin (dx-poll (car l)) (dx-polls (cdr l))))))

;;; ------------------------------------------------------------ the procedure

;; Its entry: the raw parameters unboxed, then, with a frame or a call, a
;; poll keeping the arguments live (all, for a variadic procedure, whose
;; count is in X9, which the poll keeps too), raw or not.
(define dx-entry (subr da-assembles () unit)
  (lambda ()
    (let ((entry (da-label)) (checked (da-label)))
      (begin
        (da-bind entry)
        (dr-raw-entry (get dp-params))
        (set dp-entry-checked checked)
        (da-bind checked)
        (if (or (get dp-calls) (>= (get dp-frame) 0))
            (let* ((first (dp-start 0))
                   (n (if (= (dp-op first) rop-args) (min (dp-o first 0) 8) 8))
                   (out (da-label))
                   (back (da-label)))
              (letrec ((masks (subr da-reads (int int int) (productof (1 int) (2 int)))
                         (lambda (r raws values)
                           (cond ((> r n) (product (1 raws) (2 values)))
                                 ((nr-raw-param? (get dp-params) r)
                                  (masks (+ r 1) (dx-with raws r) values))
                                 (else (masks (+ r 1) raws (dx-with values r)))))))
                (let ((m (masks 1 0 0)))
                  (begin
                    (da-e (x86-alu-mi da-sub d-st d-st-fuel 1))
                    (da-jcc da-c-b out)
                    (da-bind back)
                    (set dp-polls
                         (cons (product (1 out) (2 back) (3 (extract m 2)) (4 (extract m 1))
                                        (5 (get dp-captures)) (6 #f) (7 0))
                               (get dp-polls)))))))
            #u)))))

;; `n` labels, as an array.
(define dx-labels (subr da-assembles (int) da-ints)
  (lambda (n)
    (let ((a (the da-ints (make-array n 0))))
      (letrec ((fill (subr da-assembles (int) unit)
                 (lambda (k) (if (= k n) #u (begin (array-set! a k (da-label)) (fill (+ k 1)))))))
        (begin (fill 0) a)))))

;; Where each instruction starts in the code, both versions' (`Proc::starts`):
;; each offset and the instruction's cell, flat, from instruction `si` down.
(define dx-starts (subr da-assembles (int da-bytes) da-bytes)
  (lambda (si acc)
    (if (< si 0)
        acc
        (let* ((i (dp-start si))
               (g (da-label-offset (array-ref (get dp-labels-g) i)))
               (f (da-label-offset (array-ref (get dp-labels-f) i)))
               (with-f (if (>= f 0) (the da-bytes (cons f (cons i acc))) acc)))
          (dx-starts (- si 1) (if (>= g 0) (the da-bytes (cons g (cons i with-f))) with-f))))))

;; Each load of a call-out's number given its field (`Asm::callout_fields`).
(define dx-callout-fields (subr da-assembles (da-pairs) unit)
  (lambda (ls)
    (if (null? ls)
        #u
        (let ((k (dp-field (dp-callout-of (extract (car ls) 2)))))
          (begin (da-callout-field (extract (car ls) 1) k) (dx-callout-fields (cdr ls)))))))

;; A procedure's code, as `procedure_x64` makes it, of what Rust gave of it
;; (`FxRequest`: its name, its lists in order, and the messages its
;; failures noted at instructions name): its bytes, how many are its own,
;; its code bloblet's fields (as `direct/fx.rs`'s `field_of` reads them),
;; the call-outs it numbered, why it cannot be compiled ("" if it can;
;; the call-outs numbered until then are the Rust compiler's too), and
;; where each instruction starts (`dx-starts`).
(define native-compile-x64-proc (subr da-assembles (string (listof da-bytes @k) da-strings) dx-made)
  (lambda (name lists errors)
    (begin
      (dp-begin name lists errors)
      (dp-analyse)
      (if (da-ok?)
          (begin
            (set dp-labels-g (dx-labels (+ (get dp-n) 1)))
            (set dp-resume-at (da-label))
            (dx-entry)
            (set dp-labels-f (dx-labels (+ (get dp-n) 1)))
            (if (get dp-has-int) (dx-version #t) #u)
            (if (da-ok?) (dx-version #f) #u))
          #u)
      (if (da-ok?)
          (let* ((own (dx-after))
                 (placed (dx-callout-fields (da-callout-loads-made)))
                 (code (da-finish)))
            (product (1 code) (2 own) (3 (the da-bytes (reverse (get dp-fields))))
                     (4 (da-callouts)) (5 (da-err))
                     (6 (dx-starts (- (dp-ns) 1) (the da-bytes nil)))))
          (product (1 (the da-bytes nil)) (2 0) (3 (the da-bytes nil)) (4 (da-callouts))
                   (5 (da-err)) (6 (the da-bytes nil)))))))
)))
