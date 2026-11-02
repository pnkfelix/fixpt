;;; Register code compiled to arm64 machine code, in FX-26: the arm64
;;; machine's `assemble_register_word` and `assemble_adapter`
;;; (`fixpt-native/src/cellular/regcode.rs`), step for step and instruction
;;; for instruction, over `native.fx`'s assembler and the encoder written
;;; in FX-26 (`arm64.fx`), as `native-x64-regs.fx` is for x86_64. The Rust
;;; compiler is this one's oracle: for every register word, the same
;;; instructions and the same resume points (`tests/native.rs`).
;;;
;;; Its steps have the names the Rust ones have, with `ar-` before them
;;; (`ar-push-regs` is `push_regs`), so that a change to one is made to the
;;; other by reading them side by side. Where Rust returns an error, this
;;; one notes the first (`ar-fail`) and stops. Its fast paths and what it
;;; does inline are `native-arm64-regs-ops.fx`'s.
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
           (asm (select regs-types native-arm64-asm-sig))
           (ops (select regs-types native-arm64-regs-ops-sig)))
    (module
(hide (include regs-types))
(hide (include arm64) (include layout) (include native-layout) (include regs-layout) (include asm)
      (include ops))

;; Compiling a register word: its field count, its frame's size once
;; `save` has made it (-1 before: a leaf, `Asm::link`), the time slice
;; register code takes in line, and the first error ("" for none).
(define ar-fields (ref int @k) (new 0))
(define ar-link (ref int @k) (new -1))
(define ar-slice (ref int @k) (new 0))
(define ar-err (ref string @k) (new ""))
;; Each cell's label; its resume point (-1 for none); and whether a
;; backward branch arrives there.
(define ar-labels (ref ar-ints @k) (new (make-array 1 0)))
(define ar-resume (ref ar-ints @k) (new (make-array 1 0)))
(define ar-heads (ref ar-bools @k) (new (make-array 1 #f)))

;; Register code's next slices taken in line (`refills`): each stub, and
;; where it goes back to; its polls that may leave the machine (`polls`);
;; their resume points (`resume_at`): each field, and its code's label; and
;; what each loop's poll keeps (`liveness`), by cell.
(define ar-refills (ref ar-pairs @k) (new nil))
(define ar-polls (ref ar-poll-list @k) (new nil))
(define ar-resume-at (ref ar-pairs @k) (new nil))
(define ar-live (ref ar-ints @k) (new (make-array 1 0)))

(define ar-fail (subr (maxeff (read @globals) (read @k) (write @k)) (string) unit)
  (lambda (m) (if (string=? (get ar-err) "") (set ar-err m) #u)))

;;; ------------------------------------------------------------ helpers

;; `x30` is the link again, from the frame, or a leaf's from the state
;; (`relink`).
(define ar-relink (subr (maxeff ar-assembles spin) () unit)
  (lambda ()
    (if (>= (get ar-link) 0)
        (ar-slot a-lr (get ar-link) #f)
        (n-e (arm-ldr a-lr n-st a-st-leaf-link)))))
;; Back from somewhere that may have collected: the value on the data
;; stack into `RESULT`, and `IP` made again (`resumed`).
(define ar-resumed (subr (maxeff ar-assembles spin) () unit)
  (lambda ()
    (begin (n-e (arm-ldr-post a-result n-dsp 8)) (ar-pool (get ar-fields)) (ar-relink))))

;; A call-out to routine `n` with the ip at field `f` (`r_callout`).
(define ar-callout (subr (maxeff ar-assembles spin) (int int) unit)
  (lambda (n f)
    (begin
      (ar-ip-at f)
      (n-save)
      (n-e (arm-mov 0 n-st))
      (n-e (arm-movz 1 n 0))
      (n-e (arm-ldr n-x16 n-st n-st-callout))
      (n-e (arm-blr n-x16))
      (n-cbnz 0 (get n-exit-common))
      (n-load)
      (if (n-control? n) (n-enter-cur n-x13) #u))))

;; A return entry, marked as register code's `blr` pushes it: its `8k`
;; negated (`push_return_marked`).
(define ar-push-return-marked (subr (maxeff ar-assembles spin) () unit)
  (lambda ()
    (begin
      (n-e (arm-add n-x13 n-base n-cur))
      (n-e (arm-sub-imm n-x13 n-x13 4))
      (n-e (arm-sub n-x13 n-ip n-x13))
      (n-fp-encode n-x14)
      (n-e (arm-stp-pre n-x14 n-clo n-rsp -16))
      (n-e (arm-stp-pre n-cur n-x13 n-rsp -16)))))
;; The return entry on top made plain, if a `blr` marked it
;; (`unmark_return`).
(define ar-unmark-return (subr (maxeff ar-assembles spin) () unit)
  (lambda ()
    (let ((plain (n-label)))
      (begin
        (n-e (arm-ldr n-x13 n-rsp 8))
        (n-e (arm-cmp-imm n-x13 0))
        (n-b-cond ar-ge plain)
        (n-e (arm-sub n-x13 a-xzr n-x13))
        (n-e (arm-str n-x13 n-rsp 8))
        (n-bind plain)))))
;; Pop a return entry and return to it the stack's way, a marked one too
;; (`pop_return_of(true)`).
(define ar-pop-return-marked (subr (maxeff ar-assembles spin) () unit)
  (lambda ()
    (let ((again (n-label)) (plain (n-label)))
      (begin
        (n-bind again)
        (n-e (arm-ldr n-x13 n-rsp 0))
        (n-pass-mark n-prompt-mark again)
        (n-pass-mark n-mark-mark again)
        (n-e (arm-ldp-post n-cur n-x13 n-rsp 16))
        (n-e (arm-cmp-imm n-x13 0))
        (n-b-cond ar-ge plain)
        (n-e (arm-sub n-x13 a-xzr n-x13))
        (n-bind plain)
        (n-e (arm-ldp-post n-x14 n-clo n-rsp 16))
        (n-value n-x15 n-false)
        (n-e (arm-cmp n-cur n-x15))
        (n-b-cond ar-eq (get n-exit-common))
        (n-e (arm-add n-ip n-base n-cur))
        (n-e (arm-sub-imm n-ip n-ip 4))
        (n-e (arm-sub n-ip n-ip n-x13))
        (n-fp-decode n-x14)
        (n-enter-cur n-x13)))))

;;; ------------------------------------------------------------ polls

;; A poll, at a cell boundary, in register code (`fuel`): the next slice
;; taken in line, from a stub (`ar-place-refills`).
(define ar-fuel (subr (maxeff ar-assembles spin) () unit)
  (lambda ()
    (let ((refill (n-label)) (back (n-label)))
      (begin
        (n-e (arm-subs-imm n-fuel n-fuel 1))
        (n-b-cond ar-eq refill)
        (n-bind back)
        (set ar-refills (cons (product (1 refill) (2 back)) (get ar-refills)))))))
;; The next slices' stubs: out of fuel if the reserve is spent
;; (`flush_stubs`).
(define ar-place-refills (subr (maxeff ar-assembles spin) (ar-pairs) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let ((out (n-label)))
          (begin
            (n-bind (extract (car rs) 1))
            (n-e (arm-ldr n-x13 n-st a-st-reserve))
            (n-cbz n-x13 out)
            (n-value n-x14 (get ar-slice))
            (n-e (arm-cmp n-x13 n-x14))
            (n-e (arm-csel n-x14 n-x13 n-x14 ar-lo))
            (n-e (arm-sub n-x13 n-x13 n-x14))
            (n-e (arm-str n-x13 n-st a-st-reserve))
            (n-e (arm-mov n-fuel n-x14))
            (n-b (extract (car rs) 2))
            (n-bind out)
            (n-e (arm-movz n-x13 n-trap-out-of-fuel 0))
            (n-e (arm-movz n-x14 0 0))
            (n-b (get n-trap-common))
            (ar-place-refills (cdr rs)))))))

;; A poll that may leave the machine (`poll_regs`), keeping the registers
;; `live` says (bit 0 `RESULT`, bit `k` `REGk`), back at the resume point
;; field `f` names.
(define ar-poll-regs (subr (maxeff ar-assembles spin) (int int) unit)
  (lambda (live f)
    (let ((out (n-label)) (back (n-label)) (again (n-label)))
      (begin
        (n-e (arm-subs-imm n-fuel n-fuel 1))
        (n-b-cond ar-eq out)
        (n-bind back)
        (set ar-resume-at (cons (product (1 f) (2 again)) (get ar-resume-at)))
        (set ar-polls (cons (product (1 out) (2 back) (3 again) (4 live) (5 f) (6 (get ar-fields))
                                     (7 (get ar-link)))
                            (get ar-polls)))))))
(define ar-live? (subr pure (int int) bool)
  (lambda (live k) (not (= (bitwise-and live (arithmetic-shift 1 k)) 0))))
;; `REGk`'s register, `RESULT` for 0.
(define ar-kept (subr pure (int) int) (lambda (k) (if (= k 0) a-result (ar-reg k))))
;; The registers `live` says, from `k` up, onto the data stack; and back
;; off it, from `k` down.
(define ar-push-live (subr (maxeff ar-assembles spin) (int int) unit)
  (lambda (live k)
    (if (> k a-regs)
        #u
        (begin
          (if (ar-live? live k) (n-e (arm-str-pre (ar-kept k) n-dsp -8)) #u)
          (ar-push-live live (+ k 1))))))
(define ar-pop-live (subr (maxeff ar-assembles spin) (int int) unit)
  (lambda (live k)
    (if (< k 0)
        #u
        (begin
          (if (ar-live? live k) (n-e (arm-ldr-post (ar-kept k) n-dsp 8)) #u)
          (ar-pop-live live (- k 1))))))
;; The polls' code out of line (`flush_polls`).
(define ar-place-polls (subr (maxeff ar-assembles spin) (ar-poll-list) unit)
  (lambda (ps)
    (if (null? ps)
        #u
        (let* ((p (car ps)) (live (extract p 4)) (leaf (extract p 7)))
          (begin
            (n-bind (extract p 1))
            (ar-push-live live 0)
            (if (< leaf 0) (n-e (arm-str-pre a-lr n-dsp -8)) #u)
            (ar-ip-at (extract p 5))
            (n-e (arm-movz n-x13 n-trap-out-of-fuel 0))
            (n-e (arm-movz n-x14 2 0))
            (n-b (get n-trap-common))
            ;; Back, by the resume table, the machine's registers loaded.
            (n-bind (extract p 3))
            (ar-pool (extract p 6))
            (if (< leaf 0) (n-e (arm-ldr-post a-lr n-dsp 8)) #u)
            (ar-pop-live live a-regs)
            (if (>= leaf 0)
                (let ((link (get ar-link)))
                  (begin (set ar-link leaf) (ar-relink) (set ar-link link)))
                #u)
            (n-b (extract p 2))
            (ar-place-polls (cdr ps)))))))
;; Each poll's resume point, from its label.
(define ar-place-resume-at (subr (maxeff ar-assembles spin) (ar-pairs) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (begin
          (array-set! (get ar-resume) (- (extract (car rs) 1) n-word-cell0)
                      (n-label-at (extract (car rs) 2)))
          (ar-place-resume-at (cdr rs))))))

;; Which registers each instruction may read before writing, as it begins,
;; as a mask (`liveness`): bit 0 `RESULT`, bit `k` `REGk`. What may collect
;; is taken to write REG1…REG8 all. Each instruction's uses, defs, and
;; successors (-1 for none), by cell; the instructions, last first.
(define ar-l-uses (ref ar-ints @k) (new (make-array 1 0)))
(define ar-l-defs (ref ar-ints @k) (new (make-array 1 0)))
(define ar-l-fall (ref ar-ints @k) (new (make-array 1 0)))
(define ar-l-jump (ref ar-ints @k) (new (make-array 1 0)))
(define ar-l-starts (ref ar-out @k) (new nil))
(define ar-upto (subr pure (int) int)
  (lambda (n) (- (arithmetic-shift 1 (+ (min n a-regs) 1)) 2)))
(define ar-bit (subr pure (int) int)
  (lambda (k) (if (or (= k 0) (> k a-regs)) 0 (arithmetic-shift 1 k))))
(define ar-l-note (subr (maxeff ar-assembles spin) (int int int int int) unit)
  (lambda (i uses defs fall jump)
    (begin
      (array-set! (get ar-l-uses) i uses)
      (array-set! (get ar-l-defs) i defs)
      (array-set! (get ar-l-fall) i fall)
      (array-set! (get ar-l-jump) i jump)
      (set ar-l-starts (cons i (get ar-l-starts))))))
;; Field `j` of the instruction at cell `i`'s operands, and its value as a
;; fixnum; the instruction at cell `i`.
(define ar-f (subr pure (int int) int) (lambda (i j) (+ n-word-cell0 (+ i (+ 1 j)))))
(define ar-k (subr pure (tword int int) int) (lambda (rw i j) (tword-int rw (ar-f i j))))
(define ar-op (subr pure (tword int) int) (lambda (rw i) (tword-int rw (+ n-word-cell0 i))))
(define ar-l-info (subr (maxeff ar-assembles spin) (tword int int) unit)
  (lambda (rw i n)
    (if (>= i n)
        #u
        (let* ((op (ar-op rw i))
               (next (+ i (+ 1 (a-operands op))))
               (all 510)
               (fall (if (or (= op rop-return) (= op rop-tailinvoke) (= op rop-branch)) -1 next))
               (jump (cond ((or (= op rop-branch) (= op rop-branchf) (= op rop-brancht))
                            (+ i (+ 2 (ar-k rw i 0))))
                           ((= op rop-global-guard) (+ i (+ 4 (ar-k rw i 2))))
                           (else -1))))
          (begin
            (cond
              ((= op rop-args) (ar-l-note i 0 (ar-upto (ar-k rw i 0)) fall jump))
              ((= op rop-vargs) (ar-l-note i 0 all fall jump))
              ((or (= op rop-const) (= op rop-global) (= op rop-lexical) (= op rop-stack))
               (ar-l-note i 0 1 fall jump))
              ((or (= op rop-setglbl) (= op rop-setstk) (= op rop-branchf) (= op rop-brancht)
                   (= op rop-return))
               (ar-l-note i 1 0 fall jump))
              ((= op rop-reg) (ar-l-note i (ar-bit (ar-k rw i 0)) 1 fall jump))
              ((= op rop-setreg) (ar-l-note i 1 (ar-bit (ar-k rw i 0)) fall jump))
              ((= op rop-movereg)
               (ar-l-note i (ar-bit (ar-k rw i 0)) (ar-bit (ar-k rw i 1)) fall jump))
              ((= op rop-load) (ar-l-note i 0 (ar-bit (ar-k rw i 0)) fall jump))
              ((= op rop-store) (ar-l-note i (ar-bit (ar-k rw i 0)) 0 fall jump))
              ((or (= op rop-op1) (= op rop-op2imm) (= op rop-field) (= op rop-prim1)
                   (= op rop-prim2imm))
               (ar-l-note i 1 1 fall jump))
              ((or (= op rop-op2) (= op rop-prim2) (= op rop-setfield))
               (ar-l-note i (bitwise-ior 1 (ar-bit (ar-k rw i 1))) (if (= op rop-setfield) 0 1)
                          fall jump))
              ((= op rop-prim3imm) (ar-l-note i (bitwise-ior 1 (ar-bit (ar-k rw i 2))) 1 fall jump))
              ((or (= op rop-prim) (= op rop-lambda) (= op rop-cellular))
               (ar-l-note i (ar-upto (ar-k rw i 1)) (bitwise-ior 1 all) fall jump))
              ((or (= op rop-invoke) (= op rop-invokeself))
               (ar-l-note i (bitwise-ior (ar-upto (ar-k rw i 0)) (if (= op rop-invoke) 1 0))
                          (bitwise-ior 1 all) fall jump))
              ((= op rop-tailinvoke)
               (ar-l-note i (bitwise-ior 1 (ar-upto (ar-k rw i 0))) 0 fall jump))
              (else (ar-l-note i 0 0 fall jump)))
            (ar-l-info rw next n))))))
(define ar-l-at (subr (maxeff (read @globals) (read @k)) (int) int)
  (lambda (s) (if (< s 0) 0 (array-ref (get ar-live) s))))
;; One pass, the instructions last first: whether any changed.
(define ar-l-pass (subr (maxeff ar-assembles spin) (ar-out bool) bool)
  (lambda (is changed)
    (if (null? is)
        changed
        (let* ((i (car is))
               (inn (bitwise-ior (array-ref (get ar-l-uses) i)
                                 (bitwise-and (bitwise-ior (ar-l-at (array-ref (get ar-l-fall) i))
                                                           (ar-l-at (array-ref (get ar-l-jump) i)))
                                              (bitwise-not (array-ref (get ar-l-defs) i))))))
          (if (= inn (array-ref (get ar-live) i))
              (ar-l-pass (cdr is) changed)
              (begin (array-set! (get ar-live) i inn) (ar-l-pass (cdr is) #t)))))))
(define ar-l-settle (subr (maxeff ar-assembles spin) () unit)
  (lambda () (if (ar-l-pass (get ar-l-starts) #f) (ar-l-settle) #u)))
(define ar-liveness (subr (maxeff ar-assembles spin) (tword int) unit)
  (lambda (rw n)
    (begin
      (set ar-live (the ar-ints (make-array (+ n 1) 0)))
      (set ar-l-uses (the ar-ints (make-array (+ n 1) 0)))
      (set ar-l-defs (the ar-ints (make-array (+ n 1) 0)))
      (set ar-l-fall (the ar-ints (make-array (+ n 1) -1)))
      (set ar-l-jump (the ar-ints (make-array (+ n 1) -1)))
      (set ar-l-starts nil)
      (ar-l-info rw 0 n)
      (ar-l-settle))))
;; Whether the word has a loop: a backward `branch`, which only such a
;; word's polls need `ar-live` for.
(define ar-looped? (subr (maxeff (read @globals) (read @k) spin) (tword int int) bool)
  (lambda (rw i n)
    (if (>= i n)
        #f
        (let ((op (ar-op rw i)))
          (if (and (= op rop-branch) (< (ar-k rw i 0) -1))
              #t
              (ar-looped? rw (+ i (+ 1 (a-operands op))) n))))))

;;; ------------------------------------------------------------ instructions

(define ar-save (subr (maxeff ar-assembles spin) (int) unit)
  (lambda (m)
    (letrec ((fill (subr (maxeff ar-assembles spin) (int) unit)
               (lambda (s)
                 (if (> s m) #u (begin (n-e (arm-str n-x15 n-dsp (* 8 s))) (fill (+ s 1)))))))
      (begin
        (set ar-link m)
        (ar-sub-const n-dsp n-dsp (* 8 (+ m 1)))
        (n-value n-x15 n-false)
        (fill 1)
        (n-e (arm-str a-lr n-dsp 0))
        (ar-add-const n-fp n-dsp (* 8 m))
        (n-ds-limit)))))

(define ar-op2 (subr (maxeff ar-assembles spin) (tword int int) unit)
  (lambda (rw i op)
    (let* ((other (if (= op rop-op2)
                      (ar-reg (ar-k rw i 1))
                      (begin (ar-constant n-x13 rw (ar-f i 1) (get ar-fields)) n-x13)))
           (r (ar-k rw i 0))
           (slow-prim (cond ((= r routine-int-add) "%fx26-add")
                            ((= r routine-int-sub) "%fx26-sub")
                            ((= r routine-int-less) "%fx26-int-less")
                            ((= r routine-int-eq) "%fx26-int-eq")
                            (else "")))
           (slow (n-label))
           (done (n-label)))
      (begin
        (if (string=? slow-prim "")
            #u
            (begin
              (n-e (arm-orr n-x15 a-result other))
              (n-e (arm-tst-low n-x15 3))
              (n-b-cond ar-ne slow)))
        (cond ((or (= r routine-int-add) (= r routine-int-sub))
               (begin
                 (n-e (if (= r routine-int-add)
                          (arm-adds n-x15 a-result other)
                          (arm-subs n-x15 a-result other)))
                 (n-b-cond ar-vs slow)
                 (n-e (arm-mov a-result n-x15))))
              ((or (= r routine-int-less) (= r routine-eq) (= r routine-int-eq))
               (begin
                 (n-e (arm-cmp a-result other))
                 (n-value n-x16 n-true)
                 (n-value n-x15 n-false)
                 (n-e (arm-csel a-result n-x16 n-x15 (if (= r routine-int-less) ar-lt ar-eq)))))
              (else (ar-fail "op2 of that routine in register code")))
        (if (string=? slow-prim "")
            #u
            (begin
              (n-b done)
              (n-bind slow)
              (ar-pure-call (a-prim-number slow-prim) other)
              (n-bind done)))))))

(define ar-prims (subr (maxeff ar-assembles spin) (tword int int) unit)
  (lambda (rw i op)
    (let ((p (ar-k rw i 0)))
      (if (not (a-never-collects? p))
          (ar-fail "a primitive that may collect")
          (let* ((y (cond ((= op rop-prim2) (ar-reg (ar-k rw i 1)))
                          ((= op rop-prim2imm)
                           (begin (ar-constant n-x13 rw (ar-f i 1) (get ar-fields)) n-x13))
                          (else n-x13)))
                 (slow (n-label))
                 (done (n-label))
                 (pname (a-prim-name p)))
            (if (if (= op rop-prim1) (ar-shape-test a-result pname slow) (ar-int-fast pname y slow))
                (begin (n-b done) (n-bind slow) (ar-pure-call p y) (n-bind done))
                (ar-pure-call p y)))))))

;; `prim`, `lambda` and `cellular`: inline what can be, else the call-out.
(define ar-callouts (subr (maxeff ar-assembles spin) (tword int int int) unit)
  (lambda (rw i op next)
    (let* ((k0 (ar-k rw i 0))
           (count (ar-k rw i 1))
           ;; The routine a `lambda`'s closure is made by, `closure` or
           ;; `nclosure`, which only the call-out does.
           (routine-n (cond ((= op rop-prim) routine-prim)
                            ((= op rop-lambda) (ar-k rw i 2))
                            (else k0)))
           (at (if (= op rop-cellular) (+ n-word-cell0 next) (ar-f i 0)))
           (slow (n-label))
           (done (n-label))
           (what (if (and (= op rop-lambda) (not (= routine-n routine-closure)))
                     ""
                     (ar-inline-name op k0 count))))
      (begin
        (if (and (not (string=? what "")) (<= count a-regs))
            (begin (ar-inline-op what count (ar-f i 0) (get ar-fields) slow) (n-b done))
            #u)
        (n-bind slow)
        ;; A leaf's link, kept while it calls out (`relink`).
        (if (< (get ar-link) 0) (n-e (arm-str a-lr n-st a-st-leaf-link)) #u)
        (ar-push-regs count)
        (ar-callout routine-n at)
        (array-set! (get ar-resume) next (n-here))
        (ar-resumed)
        (n-bind done)))))

;; The instruction after a `blr` or `bl` 8-aligned (words are).
(define ar-align-return (subr (maxeff ar-assembles spin) () unit)
  (lambda () (if (= (modulo (n-here) 2) 0) (n-e arm-nop) #u)))

(define ar-invoke (subr (maxeff ar-assembles spin) (tword int int int) unit)
  (lambda (rw i op next)
    (let ((tail (= op rop-tailinvoke)) (count (ar-k rw i 0))
          (cellular (n-label)) (native (n-label)) (back (n-label))
          (typed (= (ar-k rw i 1) rconv-cellular)))
      (begin
        ;; The callee, its word, and the word's twin; or, its code in the
        ;; code area, a native closure, which the Rust machine calls. A
        ;; callee typed `cellular`: not looked at.
        (n-e (arm-mov n-w a-result))
        (n-e (arm-mov n-x11 n-w))
        (n-e (arm-ldur a-x12 n-x11 (n-field-off n-closure-word)))
        (if typed
            #u
            (begin
              (n-e (arm-ldr n-x15 n-st n-st-code-lo))
              (n-e (arm-cmp a-x12 n-x15))
              (n-b-cond ar-hs native)))
        (n-e (arm-mov n-x11 a-x12))
        (n-e (arm-ldur n-x10 n-x11 (n-field-off word-twin)))
        (n-value n-x15 n-false)
        (n-e (arm-cmp n-x10 n-x15))
        (n-b-cond ar-eq cellular)
        (n-e (arm-mov n-x11 n-x10))
        ;; Its code, if compiled: its entry, a code bloblet.
        (n-e (arm-ldur n-x15 n-x11 (n-field-off n-word-entry)))
        (n-e (arm-tst-low n-x15 3))
        (n-b-cond ar-eq cellular)
        ;; Register code: the arguments stay where they are; a call pushes
        ;; a return entry marked as one `blr` made.
        (if tail #u (begin (ar-ip-at (+ n-word-cell0 next)) (ar-push-return-marked)))
        (n-e (arm-ldr n-x16 n-st n-st-code-delta))
        (n-e (arm-add n-x16 n-x15 n-x16))
        (n-e (arm-mov n-clo n-w))
        (n-e (arm-mov n-cur n-x10))
        (if tail
            (n-e (arm-br n-x16))
            (begin (ar-align-return) (n-e (arm-blr n-x16)) (n-b back)))
        ;; A native closure: the arguments and it on the data stack, and
        ;; the call's routine, returning the stack's way.
        (n-bind native)
        (if typed
            #u
            (begin
              (if (< (get ar-link) 0) (n-e (arm-str a-lr n-st a-st-leaf-link)) #u)
              (if tail (ar-unmark-return) #u)
              (ar-push-regs count)
              (n-e (arm-str-pre n-w n-dsp -8))
              (ar-callout (if tail routine-tailcall routine-call) (ar-f i 0))))
        ;; Stack code: the arguments as its frame.
        (n-bind cellular)
        (ar-fuel)
        (ar-push-regs count)
        (n-ds-limit)
        (n-rs-limit)
        (if tail (ar-unmark-return) (begin (ar-ip-at (+ n-word-cell0 next)) (n-push-return)))
        (if (= count 0)
            (n-e (arm-sub-imm n-fp n-dsp 8))
            (n-e (arm-add-imm n-fp n-dsp (* 8 (- count 1)))))
        (n-e (arm-mov n-clo n-w))
        (n-e (arm-mov n-cur a-x12))
        (ar-ip-at n-word-cell0)
        (n-e (arm-movz n-x13 (* 8 n-word-cell0) 0))
        (n-enter-cur n-x13)
        (if tail
            #u
            (begin
              ;; The native closure's call-out returns to the cell after
              ;; the count: the same point.
              (array-set! (get ar-resume) next (n-here))
              (array-set! (get ar-resume) (- next 1) (n-here))
              (n-e (arm-ldr-post a-result n-dsp 8))
              (n-bind back)
              (ar-pool (get ar-fields))
              (ar-relink)))))))

;; Cell `i`'s instruction, `op`, whose next is at `next`; `entry` is the
;; register entry.
(define ar-instruction (subr (maxeff ar-assembles spin) (tword int int int int) unit)
  (lambda (rw i op next entry)
    (let ((fields (get ar-fields)))
      (cond
        ((= op rop-args) #u)
        ((= op rop-const) (ar-constant a-result rw (ar-f i 0) fields))
        ((or (= op rop-global) (= op rop-setglbl))
         (begin
           (ar-cell n-x16 (ar-f i 0) fields)
           (n-e (arm-mov n-x11 n-x16))
           (if (= op rop-global)
               (n-e (arm-ldur a-result n-x11 (n-field-off 2)))
               (begin
                 (n-e (arm-stur a-result n-x11 (n-field-off 2)))
                 ;; One more write, for the guards (`global-guard`).
                 (n-bump-writes)
                 (n-card-mark n-x11 (n-field-off 2))))))
        ((= op rop-reg) (n-e (arm-mov a-result (ar-reg (ar-k rw i 0)))))
        ((= op rop-setreg) (n-e (arm-mov (ar-reg (ar-k rw i 0)) a-result)))
        ((= op rop-movereg) (n-e (arm-mov (ar-reg (ar-k rw i 1)) (ar-reg (ar-k rw i 0)))))
        ((= op rop-lexical)
         (begin
           (n-e (arm-mov n-x11 n-clo))
           (ar-field-of a-result n-x11 (+ n-closure-free0 (ar-k rw i 0)))))
        ((= op rop-save) (ar-save (ar-k rw i 0)))
        ((= op rop-pop) (ar-add-const n-dsp n-dsp (* 8 (+ (ar-k rw i 0) 1))))
        ((= op rop-stack) (ar-slot a-result (ar-k rw i 0) #f))
        ((= op rop-setstk) (ar-slot a-result (ar-k rw i 0) #t))
        ((= op rop-load) (ar-slot (ar-reg (ar-k rw i 0)) (ar-k rw i 1) #f))
        ((= op rop-store) (ar-slot (ar-reg (ar-k rw i 0)) (ar-k rw i 1) #t))
        ((= op rop-op1)
         (let ((r (ar-k rw i 0)))
           (if (or (= r routine-pair-car) (= r routine-pair-cdr))
               (begin
                 ;; A list may be `nil`: `car` of it traps.
                 (n-e (arm-and-low n-x13 a-result 3))
                 (n-e (arm-cmp-imm n-x13 n-tag-pair))
                 (n-trap-if ar-ne n-trap-type r)
                 (n-e (arm-ldur a-result a-result (if (= r routine-pair-car) -1 7))))
               (ar-fail "op1 of that routine in register code"))))
        ((or (= op rop-op2) (= op rop-op2imm)) (ar-op2 rw i op))
        ((or (= op rop-prim1) (= op rop-prim2) (= op rop-prim2imm)) (ar-prims rw i op))
        ((= op rop-prim3imm)
         (let ((p (ar-k rw i 0)))
           (if (not (a-never-collects? p))
               (ar-fail "a primitive that may collect")
               (begin
                 (ar-constant n-x13 rw (ar-f i 1) fields)
                 (ar-pure-call3 p n-x13 (ar-reg (ar-k rw i 2)))))))
        ((= op rop-field) (ar-field-of a-result a-result (ar-k rw i 0)))
        ((= op rop-setfield)
         (let ((off (n-field-off (ar-k rw i 0))) (v (ar-reg (ar-k rw i 1))))
           (begin
             (n-e (arm-mov n-x11 a-result))
             (if (>= off -256)
                 (begin (n-e (arm-stur v n-x11 off)) (n-card-mark n-x11 off))
                 (begin
                   (ar-sub-const n-x16 n-x11 (- 0 off))
                   (n-e (arm-str v n-x16 0))
                   (n-card-mark n-x16 0))))))
        ((or (= op rop-prim) (= op rop-lambda) (= op rop-cellular)) (ar-callouts rw i op next))
        ((or (= op rop-invoke) (= op rop-tailinvoke)) (ar-invoke rw i op next))
        ;; A call of the procedure itself: a `bl` to this word's own entry.
        ((= op rop-invokeself)
         (let ((back (n-label)))
           (begin
             (ar-ip-at (+ n-word-cell0 next))
             (ar-push-return-marked)
             (ar-align-return)
             (n-bl entry)
             (n-b back)
             (array-set! (get ar-resume) next (n-here))
             (n-e (arm-ldr-post a-result n-dsp 8))
             (n-bind back)
             (ar-pool fields)
             (ar-relink))))
        ;; To an entry a `blr` pushed: the caller's registers from it, and
        ;; back to the link, by `br`. To any other, the stack's way.
        ((= op rop-return)
         (let ((stack (n-label)))
           (begin
             (n-e (arm-ldr n-x13 n-rsp 8))
             (n-e (arm-cmp-imm n-x13 0))
             (n-b-cond ar-ge stack)
             (n-e (arm-ldp-post n-cur n-x13 n-rsp 16))
             (n-e (arm-ldp-post n-x14 n-clo n-rsp 16))
             (n-fp-decode n-x14)
             (n-e (arm-br a-lr))
             (n-bind stack)
             (n-e (arm-str-pre a-result n-dsp -8))
             (ar-pop-return-marked))))
        ((or (= op rop-branch) (= op rop-branchf) (= op rop-brancht))
         (let ((to (+ i (+ 2 (ar-k rw i 0)))))
           (if (= op rop-branch)
               (begin
                 ;; A loop's poll keeps what the loop's head reads.
                 (if (<= to i) (ar-poll-regs (array-ref (get ar-live) to) (ar-f i 0)) #u)
                 (n-b (array-ref (get ar-labels) to)))
               (begin
                 (n-value n-x16 n-false)
                 (n-e (arm-cmp a-result n-x16))
                 (n-b-cond (if (= op rop-branchf) ar-eq ar-ne) (array-ref (get ar-labels) to))))))
        ;; How many times the global has been written, against how many when
        ;; this code was compiled.
        ((= op rop-global-guard)
         (let ((to (+ i (+ 4 (ar-k rw i 2)))))
           (begin
             (ar-cell n-x16 (ar-f i 0) fields)
             (n-e (arm-ldur n-x11 n-x16 (n-field-off global-writes)))
             (n-value n-x16 (ar-bits rw (ar-f i 1)))
             (n-e (arm-cmp n-x11 n-x16))
             (n-b-cond ar-ne (array-ref (get ar-labels) to)))))
        (else (ar-fail "an instruction register code has no code for"))))))

;; No-ops up to a multiple of 8 instructions: a loop's head, 32-aligned
;; (words are).
(define ar-align (subr (maxeff ar-assembles spin) () unit)
  (lambda () (if (= (modulo (n-here) 8) 0) #u (begin (n-e arm-nop) (ar-align)))))

(define ar-cells (subr (maxeff ar-assembles spin) (tword int int int) unit)
  (lambda (rw i n entry)
    (if (or (>= i n) (not (string=? (get ar-err) "")))
        #u
        (let* ((op (ar-op rw i)) (next (+ i (+ 1 (a-operands op)))))
          (begin
            (if (array-ref (get ar-heads) i) (ar-align) #u)
            (n-bind (array-ref (get ar-labels) i))
            (ar-instruction rw i op next entry)
            (ar-cells rw next n entry))))))

;; Where a backward branch goes: a loop's head.
(define ar-mark-heads (subr (maxeff ar-assembles spin) (tword int int) unit)
  (lambda (rw j n)
    (if (>= j n)
        #u
        (let* ((op (ar-op rw j)) (k (a-operands op)))
          (begin
            (if (or (= op rop-branch) (= op rop-branchf) (= op rop-brancht) (= op rop-global-guard))
                (let ((to (+ (+ j (+ 1 k)) (tword-int rw (+ n-word-cell0 (+ j k))))))
                  (if (<= to j) (array-set! (get ar-heads) to #t) #u))
                #u)
            (ar-mark-heads rw (+ j (+ 1 k)) n))))))

(define ar-fill-labels (subr (maxeff ar-assembles spin) (ar-ints int) unit)
  (lambda (a i)
    (if (= i (array-length a))
        #u
        (begin (array-set! a i (n-label)) (ar-fill-labels a (+ i 1))))))
(define ar-array-list (subr ar-lists (ar-ints int ar-out) ar-out)
  (lambda (a i acc) (if (< i 0) acc (ar-array-list a (- i 1) (cons (array-ref a i) acc)))))

;; A register word's machine code, as `assemble_register_word_as` makes
;; it, every conditional branch long if `long?`.
(define ar-assemble (subr (maxeff ar-assembles spin) (tword bool) ar-regs-assembled)
  (lambda (rw long?)
    (let ((n (- (+ (tword-fields rw) 1) n-word-cell0)))
      (begin
        (n-reset)
        (set n-long long?)
        (set ar-err "")
        (set ar-link -1)
        (set ar-fields (tword-fields rw))
        (set ar-labels (the ar-ints (make-array (+ n 1) 0)))
        (ar-fill-labels (get ar-labels) 0)
        (set ar-resume (the ar-ints (make-array n -1)))
        (set ar-heads (the ar-bools (make-array (+ n 1) #f)))
        (set ar-refills nil)
        (set ar-polls nil)
        (set ar-resume-at nil)
        (let ((far-exit (get n-exit-common)) (near-exit (n-label)))
          (begin
            (set n-exit-common near-exit)
            (if (ar-looped? rw 0 n) (ar-liveness rw n) #u)
            ;; The register entry. Its poll keeps the arguments, unless they
            ;; are counted (`vargs`).
            (let ((entry (n-label)))
              (begin
                (n-bind entry)
                (if (= (ar-op rw 0) rop-args)
                    (ar-poll-regs (ar-upto (ar-k rw 0 0)) (+ n-word-cell0 1))
                    (ar-fuel))
                (n-rs-limit)
                (ar-pool (get ar-fields))
                (ar-mark-heads rw 0 n)
                (ar-cells rw 0 n entry)))
            (if (not (string=? (get ar-err) ""))
                (product (1 (the ar-out nil)) (2 (the ar-out nil)) (3 (get ar-err)))
                (begin
                  (n-bind (array-ref (get ar-labels) n))
                  ;; Out of the way of the code that runs: the polls' ways out
                  ;; and back, the next slices' stubs and the traps, and a
                  ;; jump to the machine's exit; then the machine's common
                  ;; trap and exit, through the state.
                  (ar-place-polls (the ar-poll-list (reverse (get ar-polls))))
                  (ar-place-refills (the ar-pairs (reverse (get ar-refills))))
                  (n-flush-stubs)
                  (n-bind near-exit)
                  (n-b far-exit)
                  (set n-exit-common far-exit)
                  (n-bind (get n-trap-common))
                  (n-e (arm-ldr n-x16 n-st n-st-trap))
                  (n-e (arm-br n-x16))
                  (n-bind far-exit)
                  (n-e (arm-ldr n-x16 n-st n-st-exit))
                  (n-e (arm-br n-x16))
                  (if (and (not long?) (not (n-branches-fit?)))
                      (ar-assemble rw #t)
                      (begin
                        (ar-place-resume-at (get ar-resume-at))
                        (let ((code (n-finish)))
                          (product (1 code) (2 (ar-array-list (get ar-resume) (- n 1) nil))
                                   (3 "")))))))))))))

;; A register word's machine code, as `assemble_register_word` makes it:
;; its instructions, where each cell's resume point is, and why not, if
;; not. `far-trap` and `far-exit` are no longer needed (the code reaches
;; the machine's through the state); `slice` is the time slice its next
;; slices are, which Rust's code has as a constant
;; (`fixpt_runtime::sched::slice`).
(define native-assemble-arm64-regs
  (subr (maxeff ar-assembles spin) (tword int int int) ar-regs-assembled)
  (lambda (rw far-trap far-exit slice)
    (begin (set ar-slice slice) (ar-assemble rw #f))))

;; The entry a stack-code caller takes into a word with register code
;; (`assemble_adapter`): the `n` arguments from its frame into registers,
;; the frame dropped, and on to the register word's code, its entry, a
;; link of 0.
(define ar-adapter-args (subr (maxeff ar-assembles spin) (int int) unit)
  (lambda (i n)
    (if (= i n)
        #u
        (begin (n-e (arm-ldur (ar-reg (+ i 1)) n-fp (- 0 (* 8 i)))) (ar-adapter-args (+ i 1) n)))))
(define native-adapter-arm64 (subr (maxeff ar-assembles spin) (int) ar-out)
  (lambda (n)
    (begin
      (n-reset)
      (ar-adapter-args 0 n)
      (n-e (arm-add-imm n-dsp n-fp 8))
      (n-e (arm-mov n-x11 n-cur))
      (n-e (arm-ldur n-cur n-x11 (n-field-off word-twin)))
      (n-e (arm-ldur n-x16 n-cur (n-field-off n-word-entry)))
      (n-e (arm-ldr n-x10 n-st n-st-code-delta))
      (n-e (arm-add n-x16 n-x16 n-x10))
      ;; No `blr` made this call: the link the callee keeps is a fixnum, 0.
      (n-e (arm-mov a-lr a-xzr))
      (n-e (arm-br n-x16))
      (n-finish))))
)))
