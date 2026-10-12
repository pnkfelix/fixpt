;;; Register code compiled to x86_64 machine code, in FX-26: the x86_64
;;; machine's `assemble_register_word` and `assemble_adapter`
;;; (`fixpt-native/src/cellular/x64/regcode.rs`), step for step and
;;; instruction for instruction, over `native-x64.fx`'s assembler and the
;;; encoder written in FX-26 (`x86_64.fx`). The Rust compiler is this one's
;;; oracle: for every register word, the same bytes and the same resume
;;; points (`tests/native_x64.rs`).
;;;
;;; Its steps have the names the Rust ones have, with `rg-` before them
;;; (`rg-push-regs` is `push_regs`), so that a change to one is made to the
;;; other by reading them side by side. Where Rust returns an error, this
;;; one notes the first (`rg-fail`) and stops. Its fast paths and what it
;;; does inline are `native-x64-regs-ops.fx`'s.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoders, the layouts and
;;; `native-x64.fx`'s assembler.

(let* ((native-x64-types (load-module "fx26:native-x64-types.fx"))
       (x86-64-types (load-module "fx26:x86_64-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx")))
  (lambda ((x86 (select x86-64-types x86-64-sig))
           (layout (select layout-types layout-sig))
           (native-layout (select native-x64-types native-x64-layout-sig))
           (regs-layout (select native-x64-types native-x64-regs-layout-sig))
           (asm (select native-x64-types native-x64-asm-sig))
           (ops (select native-x64-types native-x64-regs-ops-sig)))
    (module
(hide (include native-x64-types))
(hide (include x86) (include layout) (include native-layout) (include regs-layout) (include asm)
      (include ops))

;; Compiling a register word: its frame's size once `save` has made it
;; (-1 before), whether the link is on the machine stack here, whether the
;; code before falls through to here, and the first error ("" for none).
(define rg-link (ref int @k) (new -1))
(define rg-pushed (ref bool @k) (new #f))
(define rg-falls (ref bool @k) (new #t))
(define rg-err (ref string @k) (new ""))
;; Each cell's label; its resume point (-1 for none); whether the link is
;; on the stack where a branch arrives (1, 0, or -1 where none has yet);
;; and whether a backward branch arrives there.
(define rg-labels (ref x-ints @k) (new (make-array 1 0)))
(define rg-resume (ref x-ints @k) (new (make-array 1 0)))
(define rg-pushed-at (ref x-ints @k) (new (make-array 1 0)))
(define rg-heads (ref x-bools @k) (new (make-array 1 #f)))

(define rg-fail (subr (maxeff (read @globals) (read @k) (write @k)) (string) unit)
  (lambda (m) (if (string=? (get rg-err) "") (set rg-err m) #u)))

;;; ------------------------------------------------------------ helpers

(define rg-length (subr (maxeff (read @globals) (read @k) spin) (x-out) int)
  (lambda (bs) (if (null? bs) 0 (+ 1 (rg-length (cdr bs))))))
;; `REGk` := frame slot `n`, or the other way with `store?`.
(define rg-slot-reg (subr (maxeff x-assembles spin) (int int bool) unit)
  (lambda (k n store?)
    (let ((r (rg-in-reg k)) (d (- 0 (* 8 n))))
      (cond ((and (>= r 0) (not store?)) (x-load r n-fp d))
            ((>= r 0) (x-store n-fp d r))
            ((not store?) (begin (x-load n-x16 n-fp d) (x-store n-st (rg-reg-off k) n-x16)))
            (else (begin (x-load n-x16 n-st (rg-reg-off k)) (x-store n-fp d n-x16)))))))
;; `IP` := the address of the running word's field `f`.
(define rg-ip-at (subr (maxeff x-assembles spin) (int) unit)
  (lambda (f) (x-lea n-ip n-cur (x-field f))))
;; No-ops so that an instruction of `len` bytes, placed next, ends
;; 8-aligned: a `call`'s return point, which a frame keeps as a link.
(define rg-align-return (subr (maxeff x-assembles spin) (int) unit)
  (lambda (len)
    (let ((end (+ (x-here) len)))
      (x-e (x86-nops (- (* 8 (quotient (+ end 7) 8)) end))))))
;; No-ops up to a multiple of `n` bytes.
(define rg-align (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (let ((h (x-here)))
      (x-e (x86-nops (- (* n (quotient (+ h (- n 1)) n)) h))))))
;; Push `REG1`…`REGn`, `REG1` deepest; past `REGS`, the rest are a list in
;; the last register.
(define rg-push-from (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (k n)
    (if (> k n) #u (begin (x-push-ds (rg-get k n-x16)) (rg-push-from (+ k 1) n)))))
(define rg-push-list (subr (maxeff x-assembles spin) (int) unit)
  (lambda (left)
    (if (= left 0)
        #u
        (begin (x-load n-x13 n-x14 -1) (x-push-ds n-x13) (x-load n-x14 n-x14 7)
               (rg-push-list (- left 1))))))
(define rg-push-regs (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (if (<= n r-regs)
        (rg-push-from 1 n)
        (begin
          (rg-push-from 1 (- r-regs 1))
          (let ((r (rg-get r-regs n-x14)))
            (if (= r n-x14) #u (x-mov n-x14 r)))
          (rg-push-list (+ (- n r-regs) 1))))))

;; A call-out to routine `n` with the ip at field `f`.
(define rg-callout (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (n f)
    (begin
      (rg-ip-at f)
      (x-save)
      (x-mov r-rdi n-st)
      (x-e (x86-mov-imm r-rsi n))
      (x-e (x86-call-m n-st n-st-callout))
      (x-e (x86-test r-result r-result))
      (x-jcc x-c-ne (get x-exit-common))
      (x-load-state)
      (if (n-control? n) (x-enter-cur n-x13) #u))))

;; `RESULT` := primitive `p` of `RESULT`, `y` and, unless it is -1, `z`,
;; called in Rust (`pure_call`) with no safepoint; its failure a trap.
(define rg-push-saved (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin (x-e (x86-push r-rdi)) (x-e (x86-push r-rsi)) (x-e (x86-push r-r8))
           (x-e (x86-push n-clo)) (x-e (x86-push n-table)))))
(define rg-pop-saved (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin (x-e (x86-pop n-table)) (x-e (x86-pop n-clo)) (x-e (x86-pop r-r8))
           (x-e (x86-pop r-rsi)) (x-e (x86-pop r-rdi)))))
(define rg-pure-call3 (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (p y z)
    (begin
      (if (= y n-x16) #u (x-mov n-x16 y))
      (if (and (>= z 0) (not (= z r-t))) (x-mov r-t z) #u)
      (rg-push-saved)
      ;; With the link in the frame, the stack is as the machine's entry
      ;; left it, 16-aligned, and five pushes take it off by 8.
      (if (get rg-pushed) #u (x-alu-imm x-sub r-sp 8))
      (x-mov r-rdx r-result)
      (x-mov r-rcx n-x16)
      (if (>= z 0) (x-mov r-r8 r-t) #u)
      (x-mov r-rdi n-st)
      (x-e (x86-mov-imm r-rsi p))
      (x-e (x86-call-m n-st r-st-pure))
      (if (get rg-pushed) #u (x-alu-imm x-add r-sp 8))
      (rg-pop-saved)
      (x-e (x86-test r-rdx r-rdx))
      (x-trap-if x-c-ne r-trap-prim 0))))
(define rg-pure-call (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (p y) (rg-pure-call3 p y -1)))

;;; ------------------------------------------------------------ fast paths

;; A return entry for where this word is, marked as register code's `call`
;; pushes it: its `8k` negated.
(define rg-push-return-marked (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-mov n-x13 n-ip)
      (x-lea n-x14 n-cur -4)
      (x-alu x-sub n-x13 n-x14)
      (x-fp-encode n-x14)
      (x-alu-imm x-sub n-rsp 32)
      (x-store n-rsp 0 n-cur)
      (x-store n-rsp 8 n-x13)
      (x-store n-rsp 16 n-x14)
      (x-store n-rsp 24 n-clo))))
;; The return entry on top made plain, if a `call` marked it.
(define rg-unmark-return (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (let ((plain (x-label)))
      (begin
        (x-load n-x13 n-rsp 8)
        (x-e (x86-test n-x13 n-x13))
        (x-jcc rg-c-ge plain)
        (x-e (x86-neg n-x13))
        (x-store n-rsp 8 n-x13)
        (x-bind plain)))))
;; Pop a return entry and return to it the stack's way, a marked one too
;; (`pop_return_of(true)`).
(define rg-pop-return-marked (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (let ((again (x-label)) (plain (x-label)))
      (begin
        (x-bind again)
        (x-load n-x13 n-rsp 0)
        (x-pass-mark n-prompt-mark again)
        (x-pass-mark n-mark-mark again)
        (x-load n-cur n-rsp 0)
        (x-load n-x13 n-rsp 8)
        (x-e (x86-test n-x13 n-x13))
        (x-jcc rg-c-ge plain)
        (x-e (x86-neg n-x13))
        (x-bind plain)
        (x-load n-x14 n-rsp 16)
        (x-load n-clo n-rsp 24)
        (x-alu-imm x-add n-rsp 32)
        (x-cmp-value n-cur n-false)
        (x-jcc x-c-e (get x-exit-common))
        (x-lea n-ip n-cur -4)
        (x-alu x-sub n-ip n-x13)
        (x-fp-decode n-x14)
        (x-enter-cur n-x13)))))

;;; ------------------------------------------------------------ instructions

;; Field `j` of the instruction at cell `i`'s operands, and its value as a
;; fixnum.
(define rg-f (subr pure (int int) int) (lambda (i j) (+ n-word-cell0 (+ i (+ 1 j)))))
(define rg-k (subr pure (tword int int) int) (lambda (rw i j) (tword-int rw (rg-f i j))))
(define rg-op (subr pure (tword int) int) (lambda (rw i) (tword-int rw (+ n-word-cell0 i))))

;; A branch to cell `to` with the link where it is now.
(define rg-branch-to (subr (maxeff x-assembles spin) (int) unit)
  (lambda (to)
    (let ((p (if (get rg-pushed) 1 0)) (was (array-ref (get rg-pushed-at) to)))
      (if (and (>= was 0) (not (= was p)))
          (rg-fail "a branch disagrees on where the link is")
          (array-set! (get rg-pushed-at) to p)))))

(define rg-save (subr (maxeff x-assembles spin) (int) unit)
  (lambda (m)
    (letrec ((fill (subr (maxeff x-assembles spin) (int) unit)
               (lambda (s) (if (> s m) #u (begin (x-store n-dsp (* 8 s) r-rcx) (fill (+ s 1)))))))
      (if (not (get rg-pushed))
          (rg-fail "`save` with the link in a frame")
          (begin
            (set rg-link m)
            (x-alu-imm x-sub n-dsp (* 8 (+ m 1)))
            (x-load r-rcx n-st n-st-fal)
            (fill 1)
            (x-e (x86-pop-m n-dsp 0))
            (set rg-pushed #f)
            (x-lea n-fp n-dsp (* 8 m))
            (x-ds-limit))))))

(define rg-op2 (subr (maxeff x-assembles spin) (tword int int) unit)
  (lambda (rw i op)
    (let* ((other (if (= op rop-op2)
                      (rg-get (rg-k rw i 1) r-t)
                      (begin (rg-constant r-t rw (rg-f i 1)) r-t)))
           (r (rg-k rw i 0))
           (slow-prim (cond ((= r routine-int-add) "%fx26-add")
                            ((= r routine-int-sub) "%fx26-sub")
                            ((= r routine-int-less) "%fx26-int-less")
                            ((= r routine-int-eq) "%fx26-int-eq")
                            (else "")))
           (slow (x-label))
           (done (x-label)))
      (begin
        (if (string=? slow-prim "")
            #u
            (begin
              (x-mov r-rcx r-result)
              (x-alu x-or r-rcx other)
              (x-e (x86-test-imm r-rcx 7))
              (x-jcc x-c-ne slow)))
        (cond ((or (= r routine-int-add) (= r routine-int-sub))
               (begin
                 (x-mov r-rcx r-result)
                 (x-alu (if (= r routine-int-add) x-add x-sub) r-rcx other)
                 (x-jcc x-c-o slow)
                 (x-mov r-result r-rcx)))
              ((or (= r routine-int-less) (= r routine-eq) (= r routine-int-eq))
               (begin
                 (x-alu x-cmp r-result other)
                 (x-boolean r-result (if (= r routine-int-less) x-c-l x-c-e))))
              (else (rg-fail "op2 of that routine in register code")))
        (if (string=? slow-prim "")
            #u
            (begin
              (x-jmp done)
              (x-bind slow)
              (rg-pure-call (r-prim-number slow-prim) other)
              (x-bind done)))))))

(define rg-prims (subr (maxeff x-assembles spin) (tword int int) unit)
  (lambda (rw i op)
    (let ((p (rg-k rw i 0)))
      (if (not (r-never-collects? p))
          (rg-fail "a primitive that may collect")
          (let* ((y (cond ((= op rop-prim2) (rg-get (rg-k rw i 1) r-t))
                          ((= op rop-prim2imm) (begin (rg-constant r-t rw (rg-f i 1)) r-t))
                          (else r-t)))
                 (slow (x-label))
                 (done (x-label))
                 (pname (r-prim-name p)))
            (if (if (= op rop-prim1) (rg-shape-test r-result pname slow) (rg-int-fast pname y slow))
                (begin (x-jmp done) (x-bind slow) (rg-pure-call p y) (x-bind done))
                (rg-pure-call p y)))))))

;; `prim`, `lambda` and `cellular`: inline what can be, else the call-out.
(define rg-callouts (subr (maxeff x-assembles spin) (tword int int int) unit)
  (lambda (rw i op next)
    (let* ((k0 (rg-k rw i 0))
           (count (rg-k rw i 1))
           (routine-n (cond ((= op rop-prim) routine-prim)
                            ((= op rop-lambda) routine-closure)
                            (else k0)))
           (at (if (= op rop-cellular) (+ n-word-cell0 next) (rg-f i 0)))
           (slow (x-label))
           (done (x-label))
           (what (rg-inline-name op k0 count))
           (leaf (get rg-pushed)))
      (begin
        (if (and (not (string=? what "")) (<= count r-regs))
            (begin (rg-inline-op what count (rg-f i 0) slow) (x-jmp done))
            #u)
        (x-bind slow)
        ;; A leaf's link, kept in the state while it calls out.
        (if leaf (x-e (x86-pop-m n-st r-st-leaf-link)) #u)
        (rg-push-regs count)
        (rg-callout routine-n at)
        (array-set! (get rg-resume) next (x-here))
        (x-pop-ds r-result)
        (if leaf (x-e (x86-push-m n-st r-st-leaf-link)) #u)
        (x-bind done)))))

(define rg-invoke (subr (maxeff x-assembles spin) (tword int int int) unit)
  (lambda (rw i op next)
    (let ((tail (= op rop-tailinvoke)) (count (rg-k rw i 0)))
      (if (not (eq? tail (get rg-pushed)))
          (rg-fail "an invoke with the link elsewhere")
          (let ((cellular (x-label)) (back (x-label)))
            (begin
              (if tail #u (begin (rg-ip-at (+ n-word-cell0 next)) (rg-push-return-marked)))
              ;; The callee, its word (in `T`), and the word's twin.
              (x-load r-t r-result (x-field n-closure-word))
              (x-load r-rdx r-t (x-field word-twin))
              (x-cmp-value r-rdx n-false)
              (x-jcc x-c-e cellular)
              (x-load n-x16 r-rdx (x-field n-word-entry))
              (x-e (x86-test n-x16 n-x16))
              (x-jcc x-c-e cellular)
              (x-mov n-clo r-result)
              (x-mov n-cur r-rdx)
              (if tail
                  (x-e (x86-jmp-m n-table n-x16 1 0))
                  (let ((call (x86-call-m-ix n-table n-x16 1 0)))
                    (begin (rg-align-return (rg-length call)) (x-e call) (x-jmp back))))
              ;; Stack code: the arguments as its frame.
              (x-bind cellular)
              (if tail #u (x-e (x86-neg-m n-rsp 8)))
              (x-fuel)
              (rg-push-regs count)
              (x-ds-limit)
              (x-rs-limit)
              (if tail (begin (rg-unmark-return) (x-alu-imm x-add r-sp 8)) #u)
              (if (= count 0) (x-lea n-fp n-dsp -8) (x-lea n-fp n-dsp (* 8 (- count 1))))
              (x-mov n-clo r-result)
              (x-mov n-cur r-t)
              (rg-ip-at n-word-cell0)
              (x-e (x86-mov-imm r-rcx (* 8 n-word-cell0)))
              (x-enter-cur r-rcx)
              (if tail
                  (set rg-falls #f)
                  (begin
                    (array-set! (get rg-resume) next (x-here))
                    (x-pop-ds r-result)
                    (x-bind back)))))))))

;; Cell `i`'s instruction, `op`, whose next is at `next`; `entry` is the
;; register entry.
(define rg-instruction (subr (maxeff x-assembles spin) (tword int int int int) unit)
  (lambda (rw i op next entry)
    (cond
      ((= op rop-args) #u)
      ((= op rop-const) (rg-constant r-result rw (rg-f i 0)))
      ((= op rop-global) (begin (rg-cell n-x16 (rg-f i 0)) (x-load r-result n-x16 (x-field 2))))
      ((= op rop-setglbl)
       (begin
         (rg-cell n-x16 (rg-f i 0))
         (x-store n-x16 (x-field 2) r-result)
         (x-e (x86-alu-mi x-add n-x16 (x-field global-writes) 8))
         (rg-card-mark n-x16 (x-field 2) r-rcx r-rdx)))
      ((= op rop-reg)
       (let ((r (rg-get (rg-k rw i 0) r-result))) (if (= r r-result) #u (x-mov r-result r))))
      ((= op rop-setreg) (rg-put (rg-k rw i 0) r-result))
      ((= op rop-movereg) (rg-put (rg-k rw i 1) (rg-get (rg-k rw i 0) n-x16)))
      ((= op rop-lexical) (x-load r-result n-clo (x-field (+ n-closure-free0 (rg-k rw i 0)))))
      ((= op rop-save) (rg-save (rg-k rw i 0)))
      ((= op rop-pop)
       (if (get rg-pushed)
           (rg-fail "`pop` with the link on the stack")
           (begin
             (x-e (x86-push-m n-dsp 0))
             (set rg-pushed #t)
             (x-alu-imm x-add n-dsp (* 8 (+ (rg-k rw i 0) 1))))))
      ((= op rop-stack) (x-load r-result n-fp (- 0 (* 8 (rg-k rw i 0)))))
      ((= op rop-setstk) (x-store n-fp (- 0 (* 8 (rg-k rw i 0))) r-result))
      ((= op rop-load) (rg-slot-reg (rg-k rw i 0) (rg-k rw i 1) #f))
      ((= op rop-store) (rg-slot-reg (rg-k rw i 0) (rg-k rw i 1) #t))
      ((= op rop-op1)
       (let ((r (rg-k rw i 0)))
         (if (or (= r routine-pair-car) (= r routine-pair-cdr))
             (begin
               (x-mov r-rcx r-result)
               (x-alu-imm x-and r-rcx 7)
               (x-alu-imm x-cmp r-rcx n-tag-pair)
               (x-trap-if x-c-ne n-trap-type r)
               (x-load r-result r-result (if (= r routine-pair-car) -1 7)))
             (rg-fail "op1 of that routine in register code"))))
      ((or (= op rop-op2) (= op rop-op2imm)) (rg-op2 rw i op))
      ((or (= op rop-prim1) (= op rop-prim2) (= op rop-prim2imm)) (rg-prims rw i op))
      ((= op rop-prim3imm)
       (let ((p (rg-k rw i 0)))
         (if (not (r-never-collects? p))
             (rg-fail "a primitive that may collect")
             (begin
               (rg-constant n-x16 rw (rg-f i 1))
               (rg-pure-call3 p n-x16 (rg-get (rg-k rw i 2) r-t))))))
      ((= op rop-field) (x-load r-result r-result (x-field (rg-k rw i 0))))
      ((= op rop-setfield)
       (let ((v (rg-get (rg-k rw i 1) r-t)) (disp (x-field (rg-k rw i 0))))
         (begin (x-store r-result disp v) (rg-card-mark r-result disp r-rcx r-rdx))))
      ((or (= op rop-prim) (= op rop-lambda) (= op rop-cellular)) (rg-callouts rw i op next))
      ((or (= op rop-invoke) (= op rop-tailinvoke)) (rg-invoke rw i op next))
      ;; A call of the procedure itself: a `call` of this word's own entry.
      ((= op rop-invokeself)
       (if (get rg-pushed)
           (rg-fail "`invokeself` with the link on the stack")
           (let ((back (x-label)))
             (begin
               (rg-ip-at (+ n-word-cell0 next))
               (rg-push-return-marked)
               (rg-align-return 5)
               (x-to entry (x86-call 0))
               (x-jmp back)
               (array-set! (get rg-resume) next (x-here))
               (x-pop-ds r-result)
               (x-bind back)))))
      ;; To an entry a `call` pushed: back by `ret`. To any other, the
      ;; stack's way, the link dropped.
      ((= op rop-return)
       (if (not (get rg-pushed))
           (rg-fail "`return` with the link in a frame")
           (let ((stack (x-label)))
             (begin
               (x-e (x86-alu-mi x-cmp n-rsp 8 0))
               (x-jcc rg-c-ge stack)
               (x-load n-cur n-rsp 0)
               (x-load r-rdx n-rsp 16)
               (x-load n-clo n-rsp 24)
               (x-alu-imm x-add n-rsp 32)
               (x-fp-decode r-rdx)
               (x-e (x86-ret))
               (x-bind stack)
               (x-push-ds r-result)
               (x-alu-imm x-add r-sp 8)
               (rg-pop-return-marked)
               (set rg-falls #f)))))
      ((or (= op rop-branch) (= op rop-branchf) (= op rop-brancht))
       (let ((to (+ i (+ 2 (rg-k rw i 0)))))
         (begin
           (rg-branch-to to)
           (if (= op rop-branch)
               (begin
                 (if (<= to i) (x-fuel) #u)
                 (x-jmp (array-ref (get rg-labels) to))
                 (set rg-falls #f))
               (begin
                 (x-cmp-value r-result n-false)
                 (x-jcc (if (= op rop-branchf) x-c-e x-c-ne) (array-ref (get rg-labels) to)))))))
      ;; How many times the global has been written, against how many when
      ;; this code was compiled.
      ((= op rop-global-guard)
       (let ((to (+ i (+ 4 (rg-k rw i 2)))))
         (begin
           (rg-branch-to to)
           (rg-cell n-x16 (rg-f i 0))
           (x-load r-rcx n-x16 (x-field global-writes))
           (x-e (x86-mov-imm n-x16 (rg-bits rw (rg-f i 1))))
           (x-alu x-cmp r-rcx n-x16)
           (x-jcc x-c-ne (array-ref (get rg-labels) to)))))
      (else (rg-fail "an instruction register code has no code for")))))

;; Where the link is as cell `i` begins, as the branches to it say.
(define rg-arrive (subr (maxeff x-assembles spin) (int) unit)
  (lambda (i)
    (let ((p (array-ref (get rg-pushed-at) i)))
      (cond ((and (get rg-falls) (>= p 0) (not (eq? (= p 1) (get rg-pushed))))
             (rg-fail "the link is on the stack by one path, not by another"))
            ((and (not (get rg-falls)) (>= p 0)) (set rg-pushed (= p 1)))
            ((not (get rg-falls)) (set rg-pushed (< (get rg-link) 0)))
            (else #u)))))

(define rg-cells (subr (maxeff x-assembles spin) (tword int int int) unit)
  (lambda (rw i n entry)
    (if (or (>= i n) (not (string=? (get rg-err) "")))
        #u
        (let* ((op (rg-op rw i)) (next (+ i (+ 1 (r-operands op)))))
          (begin
            (rg-arrive i)
            (if (array-ref (get rg-heads) i) (rg-align 16) #u)
            (x-bind (array-ref (get rg-labels) i))
            (set rg-falls #t)
            (rg-instruction rw i op next entry)
            (rg-cells rw next n entry))))))

;; Where a backward branch goes: a loop's head, 16-aligned.
(define rg-mark-heads (subr (maxeff x-assembles spin) (tword int int) unit)
  (lambda (rw j n)
    (if (>= j n)
        #u
        (let* ((op (rg-op rw j)) (k (r-operands op)))
          (begin
            (if (or (= op rop-branch) (= op rop-branchf) (= op rop-brancht) (= op rop-global-guard))
                (let ((to (+ (+ j (+ 1 k)) (tword-int rw (+ n-word-cell0 (+ j k))))))
                  (if (<= to j) (array-set! (get rg-heads) to #t) #u))
                #u)
            (rg-mark-heads rw (+ j (+ 1 k)) n))))))

(define rg-fill-labels (subr (maxeff x-assembles spin) (x-ints int) unit)
  (lambda (a i)
    (if (= i (array-length a))
        #u
        (begin (array-set! a i (x-label)) (rg-fill-labels a (+ i 1))))))
(define rg-array-list (subr x-lists (x-ints int x-out) x-out)
  (lambda (a i acc) (if (< i 0) acc (rg-array-list a (- i 1) (cons (array-ref a i) acc)))))

;; A register word's machine code, as `assemble_register_word` makes it:
;; its bytes, where each cell's resume point is, and why not, if not.
(define native-assemble-x64-regs (subr (maxeff x-assembles spin) (tword) x-regs-assembled)
  (lambda (rw)
    (let ((n (- (+ (tword-fields rw) 1) n-word-cell0)))
      (begin
        (x-reset)
        (set rg-err "")
        (set rg-link -1)
        (set rg-labels (the x-ints (make-array (+ n 1) 0)))
        (rg-fill-labels (get rg-labels) 0)
        (set rg-resume (the x-ints (make-array n -1)))
        (set rg-pushed-at (the x-ints (make-array (+ n 1) -1)))
        (set rg-heads (the x-bools (make-array (+ n 1) #f)))
        ;; The register entry: called, the link on the machine stack.
        (let ((entry (x-label)))
          (begin
            (x-bind entry)
            (set rg-pushed #t)
            (x-fuel)
            (x-rs-limit)
            (rg-mark-heads rw 0 n)
            (set rg-falls #t)
            (rg-cells rw 0 n entry)))
        (if (not (string=? (get rg-err) ""))
            (product (1 (the x-out nil)) (2 (the x-out nil)) (3 (get rg-err)))
            (begin
              (x-bind (array-ref (get rg-labels) n))
              ;; Out of the way of the code that runs: the traps; then the
              ;; machine's common trap and exit, through the state.
              (x-flush-stubs)
              (x-bind (get x-trap-common))
              (x-e (x86-jmp-m n-st -1 1 n-st-trap))
              (x-bind (get x-exit-common))
              (x-e (x86-jmp-m n-st -1 1 n-st-exit))
              (let ((code (x-finish)))
                (product (1 code) (2 (rg-array-list (get rg-resume) (- n 1) nil)) (3 "")))))))))

;; The `n` arguments from a stack-code caller's frame into registers.
(define rg-adapter-args (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (i n)
    (if (= i n)
        #u
        (let ((r (rg-in-reg (+ i 1))) (d (- 0 (* 8 i))))
          (begin
            (if (>= r 0)
                (x-load r n-fp d)
                (begin (x-load n-x16 n-fp d) (x-store n-st (rg-reg-off (+ i 1)) n-x16)))
            (rg-adapter-args (+ i 1) n))))))

;; The entry a stack-code caller takes into a word with register code
;; (`assemble_adapter`): on to native slot `slot`, a link of 0 pushed.
(define native-adapter-x64 (subr (maxeff x-assembles spin) (int int) x-out)
  (lambda (n slot)
    (begin
      (x-reset)
      (rg-adapter-args 0 n)
      (x-lea n-dsp n-fp 8)
      (x-load n-cur n-cur (x-field word-twin))
      (x-e (x86-mov-imm n-x16 0))
      (x-e (x86-push n-x16))
      (x-e (x86-jmp-m n-table -1 1 (* 8 slot)))
      (x-finish))))
)))
