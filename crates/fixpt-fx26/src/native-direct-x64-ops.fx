;;; The instructions of the native convention's compiler to x86_64 written
;;; in FX-26 that are not primitives' or call-outs': `procedure_x64`'s arms
;;; for moves, frames, globals, `int` operations, calls and branches
;;; (`fixpt-native/src/direct/x64.rs`), step for step, each `do-` and the
;;; instruction's name, over the procedure's state (`native-direct-x64-
;;; proc.fx`). The primitives' and call-outs' are `native-direct-x64-
;;; prims.fx`'s; the loop over the instructions, `native-direct-x64.fx`'s.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder, the layouts, the
;;; assembler, the analysis and the procedure.

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
           (proc (select direct-types native-direct-x64-proc-sig)))
    (module
(hide (include direct-types))
(hide (include x86) (include dl) (include layout) (include asm) (include reps) (include raw)
      (include proc))

;;; ------------------------------------------------------------ helpers

;; `[r + field_off(k)]`'s displacement (`fld`).
(define do-fld (subr pure (int) int) (lambda (k) (da-field-off k)))
;; `mask` with bit `r`.
(define do-with (subr pure (int int) int)
  (lambda (mask r) (bitwise-ior mask (arithmetic-shift 1 r))))
;; `REGk`'s register, if it has one (`hw`), else -1.
(define do-hw (subr pure (int) int) (lambda (k) (da-in-reg k)))

;; Whether the instruction at `j` sets `RESULT` before it reads anything
;; (`sets_first`), or ignores it (`ignores`).
(define do-sets-first? (subr da-reads (int) bool)
  (lambda (j)
    (let ((op (dp-op j)))
      (or (= op rop-const) (= op rop-reg) (= op rop-stack) (= op rop-global) (= op rop-lexical)))))
(define do-ignores? (subr da-reads (int) bool)
  (lambda (j) (or (do-sets-first? j) (= (dp-op j) rop-invokeself))))
;; The instruction at index `si`'s op, or -1 past the last.
(define do-op-at-si (subr da-reads (int) int)
  (lambda (si) (if (< si (dp-ns)) (dp-op (dp-start si)) -1)))
;; Whether the instruction at `j` is an `op2` or `op2imm`.
(define do-op2? (subr da-reads (int) bool)
  (lambda (j) (or (= (dp-op j) rop-op2) (= (dp-op j) rop-op2imm))))

;; What the global or constant at `j` is for: the call just after it (a
;; tail call's frame popped between), by its cell, or -1 (`called`).
(define do-called (subr da-reads (int) int)
  (lambda (j)
    (letrec ((from (subr da-reads (int) int)
               (lambda (si)
                 (cond ((>= si (dp-ns)) -1)
                       ((= (dp-op (dp-start si)) rop-pop) (from (+ si 1)))
                       ((or (= (dp-op (dp-start si)) rop-invoke)
                            (= (dp-op (dp-start si)) rop-tailinvoke))
                        (dp-start si))
                       (else -1)))))
      (from (+ (dp-si-of j) 1)))))

;; The procedure's error at cell `i` (`FxRequest::errors`), as it was.
(define do-error-at (subr da-assembles (int) unit)
  (lambda (i)
    (letrec ((nth (subr da-reads (da-strings int) string)
               (lambda (l k) (if (= k 0) (car l) (nth (cdr l) (- k 1))))))
      (da-fail (nth (get dp-errors) (array-ref (get dp-a) i))))))

;;; ------------------------------------------------------------ constants

;; `const`: an immediate as it is; a cellular word's procedure, its code;
;; a cellular closure of no free values, called just after or as a native
;; closure of its code; any other constant from a field.
(define do-const (subr da-assembles (int) unit)
  (lambda (i)
    (let ((kind (array-ref (get dp-kind) i)) (q (array-ref (get dp-a) i)))
      (cond ((dp-oimm? i 0) (da-imm d-result (dp-ob i 0)))
            ((= kind -1) (do-error-at i))
            ((= kind 1) (da-field d-result (dp-field (dp-code-of q))))
            ((= kind 2)
             (if (>= (do-called i) 0)
                 (set dp-pending (dp-code-of q))
                 (da-field d-result (dp-field (dp-closure-of q 0)))))
            (else (da-field d-result (dp-field (dp-const-of (dp-oid i 0)))))))))

;; What the global at `i` is bound to (`global_value`), as a field.
(define do-global-value (subr da-reads (int) int)
  (lambda (i)
    (let ((kind (array-ref (get dp-kind) i)) (a (array-ref (get dp-a) i)))
      (cond ((= kind 1) (dp-code-of a))
            ((= kind 2) (dp-closure-of a (array-ref (get dp-b) i)))
            ((= kind 3) (dp-const-of a))
            (else (dp-cell-of (dp-oid i 0)))))))

;; A native closure of no free values of the procedure noted at `i`.
(define do-closure-at (subr da-reads (int) int)
  (lambda (i) (dp-closure-of (array-ref (get dp-a) i) 0)))
;; `global`: for a call just after, bound; else its cell read, and while
;; the cell has not been written since, what it was bound to.
(define do-global (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((cell (dp-oid i 0))
           (writes (array-ref (get dp-c) i))
           (kind (array-ref (get dp-kind) i))
           (g (do-global-value i)))
      (cond ((= kind -1) (do-error-at i))
            ((>= (do-called i) 0)
             (begin
               (if (= kind 0) #u (begin (set dp-bound-cell cell) (set dp-bound-writes writes)))
               (set dp-pending g)))
            (else
             (begin
               (da-field d-x9 (dp-field (dp-cell-of cell)))
               (da-ld d-result d-x9 (do-fld 2))
               (if (= kind 0)
                   #u
                   (let ((other (da-label)))
                     (begin
                       (da-ld d-x11 d-x9 (do-fld d-global-writes))
                       (da-imm d-x16 writes)
                       (da-e (x86-alu da-cmp d-x11 d-x16))
                       (da-jcc da-c-ne other)
                       (da-field d-result (dp-field (if (= kind 1) (do-closure-at i) g)))
                       (da-bind other))))))))))

(define do-global-guard (subr da-assembles (int) unit)
  (lambda (i)
    (let ((to (+ i (+ 4 (dp-o i 2)))))
      (begin
        (da-field d-x9 (dp-field (dp-cell-of (dp-oid i 0))))
        (da-ld d-x11 d-x9 (do-fld d-global-writes))
        (da-imm d-x16 (dp-ob i 1))
        (da-e (x86-alu da-cmp d-x11 d-x16))
        (da-jcc da-c-ne (dp-edge (- (get dp-si) 1) to))))))

(define do-setglbl (subr da-assembles (int) unit)
  (lambda (i)
    (begin
      (da-field d-x9 (dp-field (dp-cell-of (dp-oid i 0))))
      (da-sto d-x9 (do-fld 2) d-result)
      ;; One more write, for the guards (`global-guard`).
      (da-e (x86-alu-mi da-add d-x9 (do-fld d-global-writes) 8))
      (da-card-mark d-x9 (do-fld 2) d-x16 d-x17))))

(define do-lexical (subr da-assembles (int) unit)
  (lambda (i)
    (let ((from (if (and (>= (get dp-clo-slot) 0) (array-ref (get dp-framed) i))
                    (begin (da-ld d-x9 d-frame (get dp-clo-slot)) d-x9)
                    d-clo))
          (off (do-fld (+ d-closure-free0 (dp-o i 0)))))
      ;; Any distance: an x86 load's displacement is 32 bits (arm64's
      ;; `ldur`, 9, limits it there).
      (da-ld d-result from off))))

;;; ------------------------------------------------------------ registers and slots

;; Whether a representation is an `i64`'s or a `u64`'s.
(define do-raw-int? (subr pure (int) bool)
  (lambda (rep) (or (= rep nr-raw-signed) (= rep nr-raw-unsigned))))
;; `RESULT` := `REGk`, or where it is noted, for the `op2` just after.
(define do-reg (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((k (dp-o i 0))
           (j (dp-joinable (- (get dp-si) 1)))
           (r (do-hw k)))
      (if (and (>= j 0) (>= r 0) (do-op2? j)
               (not (do-raw-int? (nr-rep (dp-in (- (get dp-si) 1)) (min k 8)))))
          (set dp-src r)
          (let ((g (da-get k d-result)))
            (begin (if (= g d-result) #u (da-mov d-result g)) (do-hold! 0 (do-held k))))))))

(define do-setreg (subr da-assembles (int) unit)
  (lambda (i) (let ((k (dp-o i 0))) (begin (da-put k d-result) (do-hold! k (do-held 0))))))
(define do-movereg (subr da-assembles (int) unit)
  (lambda (i)
    (begin (da-put (dp-o i 1) (da-get (dp-o i 0) d-x16))
           (do-hold! (dp-o i 1) (do-held (dp-o i 0))))))

;; The frame made, the return address `call` pushed moved to its second;
;; past the stack cache's limit, the rest flushed into the heap.
(define do-save (subr da-assembles (int) unit)
  (lambda (i)
    (let ((size (get dp-size)) (over (da-label)) (back (da-label)) (rin (dp-in (- (get dp-si) 1))))
      (letrec ((raws (subr da-reads (int int) int)
                 (lambda (r acc)
                   (if (> r 8)
                       acc
                       (raws (+ r 1) (if (= (nr-rep rin r) nr-f64) (do-with acc r) acc)))))
               (zero-all (subr da-assembles (int) unit)
                 (lambda (off)
                   (if (>= off (- size 8))
                       #u
                       (begin (da-e (x86-store-imm d-frame -1 1 off 0)) (zero-all (+ off 8))))))
               (zero-live (subr da-assembles (int int) unit)
                 (lambda (k unwritten)
                   (if (or (= k (array-length (get dp-raw))) (>= k 64))
                       #u
                       (begin
                         (if (and (dp-bit? unwritten k) (not (array-ref (get dp-raw) k)))
                             (da-e (x86-store-imm d-frame -1 1 (array-ref (get dp-slot-off) k) 0))
                             #u)
                         (zero-live (+ k 1) unwritten))))))
        (begin
          (da-push-frame-ret size)
          (da-e (x86-alu-rm da-cmp d-sp d-st d-st-stack-limit))
          (da-jcc da-c-b over)
          (da-bind back)
          (set dp-overflows (cons (tup (1 over) (2 back) (3 (raws 1 0))) (get dp-overflows)))
          (set dp-map-stored? #f)
          (if (get dp-unmapped)
              (zero-all 24)
              (zero-live 0 (array-ref (get dp-live-out) (- (get dp-si) 1))))
          (da-field d-x9 1)
          (da-sto d-frame (get dp-self-slot) d-x9)
          (if (get dp-captures) (da-sto d-frame (get dp-clo-slot) d-clo) #u))))))

;; A slot's place in the frame.
(define do-slot (subr da-reads (int) int) (lambda (k) (array-ref (get dp-slot-off) k)))

;;; ------------------------------------------------------------ what registers hold

;; What `RESULT` or REGk holds of the frame (`held`): a slot, or -1; none
;; past REG3.
(define do-held (subr da-reads (int) int)
  (lambda (k) (if (<= k 3) (array-ref (get dp-held) k) -1)))
(define do-hold! (subr da-assembles (int int) unit)
  (lambda (k slot) (if (<= k 3) (array-set! (get dp-held) k slot) #u)))
(define do-forget-all! (subr da-assembles () unit)
  (lambda () (begin (do-hold! 0 -1) (do-hold! 1 -1) (do-hold! 2 -1) (do-hold! 3 -1))))
;; Slot `n`, written: held nowhere.
(define do-forget-slot! (subr da-assembles (int) unit)
  (lambda (n)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r)
                 (if (> r 3) #u (begin (if (= (do-held r) n) (do-hold! r -1) #u) (go (+ r 1)))))))
      (go 0))))
;; The first of `RESULT` and REG1…REG3 that holds slot `n`, or -1.
(define do-held-by (subr da-reads (int) int)
  (lambda (n)
    (letrec ((go (subr da-reads (int) int)
               (lambda (r) (cond ((> r 3) -1) ((= (do-held r) n) r) (else (go (+ r 1)))))))
      (go 0))))
;; A version begun: nothing held; in the general one, the labels the
;; fixnum version goes to.
(define do-held-version (subr da-assembles (bool) unit)
  (lambda (fast)
    (begin (do-forget-all!)
           (set dp-entered (if fast (the da-bools (make-array 1 #f)) (da-targets))))))
(define do-entered? (subr da-reads (int) bool)
  (lambda (l) (and (< l (array-length (get dp-entered))) (array-ref (get dp-entered) l))))
;; Before instruction `i`, `op`, its code from `at`: nothing held where
;; ways meet, where a way from the fixnum version comes in, or where its
;; conversions made registers over; then what it makes over forgotten.
(define do-held-step (subr da-assembles (int int int) unit)
  (lambda (i op at)
    (begin
      (if (or (array-ref (get dp-target) i) (not (= (da-here) at)) (do-entered? (dp-label-g i)))
          (do-forget-all!)
          #u)
      (cond ((or (or (or (= op rop-stack) (= op rop-setstk)) (or (= op rop-load) (= op rop-store)))
                 (or (or (= op rop-reg) (= op rop-setreg)) (or (= op rop-movereg) (= op rop-args)))
                 (or (or (= op rop-setglbl) (= op rop-setfield))
                     (or (= op rop-branchf) (or (= op rop-brancht) (= op rop-global-guard)))))
             #u)
            ((or (or (or (= op rop-const) (= op rop-global))
                     (or (= op rop-lexical) (= op rop-field)))
                 (or (or (= op rop-op1) (= op rop-prim1))
                     (or (= op rop-prim2) (or (= op rop-prim2imm) (= op rop-prim3imm)))))
             (do-hold! 0 -1))
            ((or (= op rop-op2) (= op rop-op2imm))
             (let ((j (dp-joinable (- (get dp-si) 1))))
               (begin (do-hold! 0 -1)
                      (if (and (>= j 0) (= (dp-op j) rop-setreg))
                          (do-hold! (dp-fix (+ j 1)) -1)
                          #u))))
            (else (do-forget-all!))))))

;; `stack`: `RESULT` := slot `n`, moved from a register that holds it.
(define do-stack (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((n (dp-o i 0)) (r (do-held-by n)))
      (begin
        (cond ((= r 0) #u)
              ((> r 0) (da-mov d-result (da-in-reg r)))
              (else (da-ld d-result d-frame (do-slot n))))
        (do-hold! 0 n)))))
(define do-setstk (subr da-assembles (int) unit)
  (lambda (i)
    (let ((n (dp-o i 0)))
      (begin (da-sto d-frame (do-slot n) d-result) (do-forget-slot! n) (do-hold! 0 n)))))
;; `load`: REGk := slot `n`, from a register that holds it.
(define do-load (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((k (dp-o i 0)) (n (dp-o i 1)) (f (do-held-by n)))
      (begin
        (cond ((and (>= f 0) (= (da-in-reg f) (da-in-reg k))) #u)
              ((>= f 0) (da-put k (da-in-reg f)))
              (else (da-load-reg k d-frame (do-slot n) d-x11)))
        (do-hold! k n)))))

;; `store`, and its slot read back at once: the register is still it.
(define do-store (subr da-assembles (int) unit)
  (lambda (i)
    (let ((k (dp-o i 0)) (slot (dp-o i 1)))
      (begin
        (da-store-reg d-frame (do-slot slot) k d-x11)
        (do-forget-slot! slot)
        (do-hold! k slot)
        (let ((j (dp-joinable (- (get dp-si) 1))))
          (if (and (>= j 0) (= (dp-op j) rop-stack) (dp-fix? (+ j 1)) (= (dp-fix (+ j 1)) slot))
              (begin
                (da-bind (dp-label j))
                (set dp-si (+ (get dp-si) 1))
                (let ((n (dp-joinable (- (get dp-si) 1))) (r (do-hw k)))
                  (if (and (>= n 0) (>= r 0) (do-op2? n))
                      (set dp-src r)
                      (let ((g (da-get k d-result)))
                        (begin (if (= g d-result) #u (da-mov d-result g)) (do-hold! 0 slot))))))
              #u))))))

;;; ------------------------------------------------------------ `int` operations

;; Whether `n` fits 32 bits, signed.
(define do-i32? (subr pure (int) bool) (lambda (n) (and (>= n -2147483648) (< n 2147483648))))
;; `op2` and `op2imm`: an `int` sum, difference or comparison, or `eq?`,
;; in line, its slow path (`IntSlow`) after the code.
(define do-op2 (subr da-assembles (int int) unit)
  (lambda (i op)
    (let* ((x (get dp-src))
           (imm? (and (= op rop-op2imm) (dp-oimm? i 1) (do-i32? (da-signed (dp-ob i 1)))))
           (small (if imm? (da-signed (dp-ob i 1)) 0))
           (other (begin
                    (set dp-src d-result)
                    (cond ((= op rop-op2) (da-get (dp-o i 1) d-x16))
                          ((not (dp-oimm? i 1))
                           (begin (da-field d-x16 (dp-field (dp-const-of (dp-oid i 1)))) d-x16))
                          (imm? d-x16)
                          (else (begin (da-imm d-x16 (dp-ob i 1)) d-x16)))))
           (r (dp-o i 0))
           (fast-int (and (get dp-fast) (nr-int-routine? r)))
           (add-sub (or (= r routine-int-add) (= r routine-int-sub))))
      (cond ((not (or add-sub (= r routine-int-less) (= r routine-int-eq) (= r routine-eq)))
             (dp-decline (string-append (d-op-name op) (string-append " " (d-routine-name r)))))
            (else (do-op2-made i op x imm? small other r fast-int add-sub))))))

;; The rest of `do-op2`, its operands placed.
(define do-op2-made
  (subr da-assembles (int int int bool int int int bool bool) unit)
  (lambda (i op x imm? small other r fast-int add-sub)
    (let* ((j (dp-joinable (- (get dp-si) 1)))
           (d (if (and add-sub (>= j 0) (= (dp-op j) rop-setreg) (>= (do-hw (dp-o j 0)) 0)
                       (>= (+ (get dp-si) 1) 0) (< (+ (get dp-si) 1) (dp-ns))
                       (do-ignores? (dp-start (+ (get dp-si) 1))))
                  (begin (da-bind (dp-label j)) (set dp-si (+ (get dp-si) 1)) (do-hw (dp-o j 0)))
                  d-result))
           (prim (cond (fast-int -1)
                       ((= r routine-int-add) d-prim-add)
                       ((= r routine-int-sub) d-prim-sub)
                       ((= r routine-int-less) d-prim-int-less)
                       ((and (= r routine-int-eq) (not (and (= op rop-op2imm) (dp-ofix? i 1))))
                        d-prim-int-eq)
                       (else -1)))
           (entry (da-label))
           (back (da-label))
           (dst (if (or (and (not imm?) (= d other)) (and fast-int (= d x))) d-x13 d)))
      (begin
        (if (>= prim 0)
            (begin
              (if (or imm? (= other x))
                  (da-e (x86-test-imm x 7))
                  (begin (da-mov d-x13 x)
                         (da-e (x86-alu da-or d-x13 other))
                         (da-e (x86-test-imm d-x13 7))))
              (da-jcc da-c-ne entry))
            #u)
        (cond (add-sub
               (begin
                 (if (= dst x) #u (da-mov dst x))
                 (let ((alu (if (= r routine-int-add) da-add da-sub)))
                   (if imm? (da-e (x86-alu-imm alu dst small)) (da-e (x86-alu alu dst other))))))
              (imm? (da-e (x86-alu-imm da-cmp x small)))
              (else (da-e (x86-alu da-cmp x other))))
        (do-op2-ends i x imm? small other r fast-int add-sub d dst prim entry back)))))

;; Where an `op2`'s value goes: an overflow's way, the flags to a branch
;; just after, or a boolean; its slow path noted.
(define do-op2-ends
  (subr da-assembles (int int bool int int int bool bool int int int int int) unit)
  (lambda (i x imm? small other r fast-int add-sub d dst prim entry back)
    (let ((cond (if (= r routine-int-less) da-c-l da-c-e))
          (slow (lambda ((ov int) (into int) (bl int) (bt bool))
                  (tup (1 entry) (2 ov) (3 back) (4 x) (5 (if imm? -1 other)) (6 small)
                           (7 into) (8 prim) (9 (= r routine-int-sub)) (10 bl) (11 bt)))))
      (letrec ((note (subr da-assembles (dr-int-slow) unit)
                 (lambda (s) (if (>= prim 0) (set dp-int-slows (cons s (get dp-int-slows))) #u))))
        (begin
          (cond ((and add-sub fast-int)
                 (begin (da-jcc da-c-o (dp-label-g i)) (if (= dst d) #u (da-mov d dst))
                        (note (slow -1 d -1 #f))))
                (add-sub
                 (let ((ov (da-label)))
                   (begin (da-jcc da-c-o ov)
                          (if (= dst d) #u (da-mov d dst))
                          (note (slow ov d -1 #f)))))
                (else (do-op2-test cond (lambda ((l int) (t bool)) (note (slow -1 d-result l t))))))
          (da-bind back))))))

;; A test that only a branch just after reads: the branch on the flags,
;; with no boolean made; else the boolean. `noted` notes the slow path,
;; with the branch's label (-1 for none) and whether it is taken when true.
(define do-op2-test (subr da-assembles (int (subr da-assembles (int bool) unit)) unit)
  (lambda (cond noted)
    (let ((j (dp-branch-on (- (get dp-si) 1))))
      (if (>= j 0)
          (let* ((to (dp-branch-to j))
                 (taken-if-true (= (dp-op j) rop-brancht))
                 (c (cond (taken-if-true cond) ((= cond da-c-e) da-c-ne) (else da-c-ge))))
            (begin
              (da-bind (dp-label j))
              (let ((l (dp-edge (get dp-si) to)))
                (begin (da-jcc c l) (noted l taken-if-true)))
              (set dp-si (+ (get dp-si) 1))))
          (begin (da-flag cond d-x9) (noted -1 #f))))))

;;; ------------------------------------------------------------ calls

;; Whether the value of the instruction being compiled is taken raw.
(define do-raw-ref? (subr da-reads () bool)
  (lambda () (array-ref (get dp-raw-refs) (- (get dp-si) 1))))
;; `invoke` and `tailinvoke`, as `procedure` makes them: `call` in place
;; of `blr`, `jmp` of `br`. A procedure known here that takes some
;; arguments raw: given them so, entered past its unboxing of them.
(define do-invoke (subr da-assembles (int int) unit)
  (lambda (i op)
    (let* ((tail (= op rop-tailinvoke))
           (callee (array-ref (get dp-callees) (- (get dp-si) 1)))
           (raws (bitwise-and (arithmetic-shift callee 1) 510))
           (skip (dr-raw-entry-skip callee))
           (stub (da-label))
           (after (da-label))
           (cv (dp-o i 1))
           (pending (get dp-pending))
           (note (lambda ()
                   (set dp-foreign
                        (cons (tup (1 stub) (2 after) (3 (dp-o i 0)) (4 tail))
                              (get dp-foreign))))))
      (begin
        (set dp-pending -1)
        (if (>= (get dp-bound-cell) 0)
            (let ((slow (da-label)) (join (da-label)))
              (begin
                (da-field d-x9 (dp-field (dp-cell-of (get dp-bound-cell))))
                (da-ld d-clo d-x9 (do-fld 2))
                (da-ld d-x11 d-x9 (do-fld d-global-writes))
                (da-imm d-x16 (get dp-bound-writes))
                (da-e (x86-alu da-cmp d-x11 d-x16))
                (da-jcc da-c-ne slow)
                (set dp-bound-cell -1)
                (do-bound-callee pending skip)
                (da-bind join)
                (set dp-cell-slows
                     (cons (tup (1 slow) (2 join) (3 raws)) (get dp-cell-slows)))))
            (do-callee pending cv skip stub note))
        ;; The count, for a variadic callee (`vargs`).
        (da-imm d-x9 (dp-o i 0))
        (da-e (x86-alu-rm da-add d-x16 d-st d-st-delta))
        (da-e (if tail (x86-jmp-r d-x16) (x86-call-r d-x16)))
        (da-bind after)
        (if (and (not tail) (do-raw-ref?)) (dr-take-raw-f64) #u)))))

;; Past the callee's unboxing of its raw parameters.
(define do-past-raw (subr da-assembles (int) unit)
  (lambda (skip) (if (> skip 0) (da-e (x86-alu-imm da-add d-x16 skip)) #u)))
;; The callee of a call bound by its global, while the global holds it.
(define do-bound-callee (subr da-assembles (int int) unit)
  (lambda (pending skip)
    (let ((tag (bitwise-and pending 7)))
      (cond ((= tag 1) (begin (da-field d-x16 (dp-field pending)) (do-past-raw skip)))
            ;; Another compile's native code, what the cell holds while the
            ;; guard holds.
            ((= tag 2) (begin (da-ld d-x16 d-clo (do-fld d-closure-word)) (do-past-raw skip)))
            (else (begin (da-field d-clo (dp-field pending))
                         (da-ld d-x16 d-clo (do-fld d-closure-word))))))))
;; Any other's: the procedure known, the cell's value, a closure or a
;; constant, or `RESULT`'s.
(define do-callee (subr da-assembles (int int int int (subr da-assembles () unit)) unit)
  (lambda (pending cv skip stub note)
    (let ((tag (bitwise-and pending 7))
          ;; Cellular, called out; native or fx, its code run, native code
          ;; or a stub that enters `foreign` (`docs/research/code-stubs.md`).
          (not-native
           (lambda ()
             (if (= cv rconv-cellular) (da-jmp stub) (da-ld d-x16 d-clo (do-fld d-closure-word))))))
      (cond ((< pending 0)
             (begin (da-mov d-clo d-result) (not-native) (if (= cv rconv-cellular) (note) #u)))
            ((= tag 1) (begin (da-field d-x16 (dp-field pending)) (do-past-raw skip)))
            ((= tag 3)
             (begin
               (da-field d-x9 (dp-field pending))
               (da-ld d-clo d-x9 (do-fld 2))
               (not-native)
               (if (= cv rconv-cellular) (note) #u)))
            (else (begin (da-field d-clo (dp-field pending))
                         (da-ld d-x16 d-clo (do-fld d-closure-word))))))))

(define do-invokeself (subr da-assembles (int) unit)
  (lambda (i)
    (begin
      (if (and (>= (get dp-clo-slot) 0) (get dp-captures))
          (da-ld d-clo d-frame (get dp-clo-slot))
          #u)
      (da-call-l (get dp-entry-checked))
      (if (do-raw-ref?) (dr-take-raw-f64) #u))))

;;; ------------------------------------------------------------ branches

;; The slots live after the instruction being compiled.
(define do-live-out (subr da-reads () int)
  (lambda () (array-ref (get dp-live-out) (- (get dp-si) 1))))

;; A branch; a loop's (back to its head) polled first, keeping what the
;; head reads, raw or not, with the frame's map for here.
(define do-branch (subr da-assembles (int int) unit)
  (lambda (i op)
    (let* ((to (+ i (+ 2 (dp-o i 0)))) (l (dp-edge (- (get dp-si) 1) to)))
      (cond ((= op rop-branchf) (begin (da-cmp-k d-result d-false) (da-jcc da-c-e l)))
            ((= op rop-brancht) (begin (da-cmp-k d-result d-false) (da-jcc da-c-ne l)))
            (else
             (begin (if (array-ref (get dp-back-to) to) (do-loop-poll i to) #u) (da-jmp l)))))))

(define do-loop-poll (subr da-assembles (int int) unit)
  (lambda (i to)
    (let* ((t (dp-si-of to))
           (rep (dp-in (- (get dp-si) 1)))
           (live (array-ref (get dp-live) t))
           (out (da-label))
           (back (da-label)))
      (letrec ((masks (subr da-reads (int int int) (tupof (1 int) (2 int)))
                 (lambda (r vals raws)
                   (if (> r 8)
                       (tup (1 vals) (2 raws))
                       (let ((kept (and (dp-bit? live r) (not (= (nr-rep rep r) nr-undefined))))
                             (raw? (nr-raw? (nr-rep rep r)))
                             (bit (arithmetic-shift 1 r)))
                         (masks (+ r 1)
                                (if (and kept (not raw?)) (bitwise-ior vals bit) vals)
                                (if (and kept raw?) (bitwise-ior raws bit) raws)))))))
        (let ((m (masks 0 0 0))
              (mapped (and (>= (get dp-frame) 0) (array-ref (get dp-framed) i))))
          (begin
            (da-e (x86-alu-mi da-sub d-st d-st-fuel 1))
            (da-jcc da-c-b out)
            (da-bind back)
            (set dp-polls
                 (cons (tup (1 out) (2 back) (3 (extract m 1)) (4 (extract m 2))
                                (5 (and (get dp-captures) (not (array-ref (get dp-framed) i))))
                                (6 mapped)
                                (7 (if mapped (dp-map-word (do-live-out)) 0)))
                       (get dp-polls)))
            (set dp-map-stored? #f)))))))
)))
