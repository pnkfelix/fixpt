;;; The instructions of the native convention's compiler to arm64 written
;;; in FX-26 that are not primitives' or call-outs': `procedure`'s arms for
;;; moves, frames, globals, `int` operations, fields, calls and branches
;;; (`fixpt-native/src/direct.rs`), step for step, each `ado-` and the
;;; instruction's name, over the procedure's state (`native-direct-arm64-
;;; proc.fx`). x86_64's (`native-direct-x64-ops.fx`). The primitives' and
;;; call-outs' are `native-direct-arm64-prims.fx`'s; the loop over the
;;; instructions, `native-direct-arm64.fx`'s.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder, the layouts, the
;;; assembler, the analysis, raw values and the procedure.

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
           (proc (select arm-direct-types native-direct-arm64-proc-sig)))
    (module
(hide (include direct-types) (include arm-direct-types))
(hide (include arm) (include dl) (include layout) (include asm) (include reps) (include raw)
      (include proc))

;;; ------------------------------------------------------------ helpers

;; Where field `k` of a bloblet is from its reference (`field_off`).
(define ado-fld (subr pure (int) int) (lambda (k) (ada-field-off k)))
;; `mask` with bit `r`.
(define ado-with (subr pure (int int) int)
  (lambda (mask r) (bitwise-ior mask (arithmetic-shift 1 r))))
;; How many bits of `mask` are set.
(define ado-count (subr spin (int) int)
  (lambda (mask) (if (= mask 0) 0 (+ (bitwise-and mask 1) (ado-count (arithmetic-shift mask -1))))))

;; Whether the instruction at `j` sets `RESULT` before it reads anything
;; (`sets_first`), or ignores it (`ignores`).
(define ado-sets-first? (subr da-reads (int) bool)
  (lambda (j)
    (let ((op (adp-op j)))
      (or (= op rop-const) (= op rop-reg) (= op rop-stack) (= op rop-global) (= op rop-lexical)))))
(define ado-ignores? (subr da-reads (int) bool)
  (lambda (j) (or (ado-sets-first? j) (= (adp-op j) rop-invokeself))))
;; Whether the instruction at `j` is an `op2` or `op2imm`.
(define ado-op2? (subr da-reads (int) bool)
  (lambda (j) (or (= (adp-op j) rop-op2) (= (adp-op j) rop-op2imm))))

;; What the global or constant at `j` is for: the call just after it (a
;; tail call's frame popped between), by its cell, or -1 (`called`).
(define ado-called (subr da-reads (int) int)
  (lambda (j)
    (letrec ((from (subr da-reads (int) int)
               (lambda (si)
                 (cond ((>= si (adp-ns)) -1)
                       ((= (adp-op (adp-start si)) rop-pop) (from (+ si 1)))
                       ((or (= (adp-op (adp-start si)) rop-invoke)
                            (= (adp-op (adp-start si)) rop-tailinvoke))
                        (adp-start si))
                       (else -1)))))
      (from (+ (adp-si-of j) 1)))))

;; The procedure's error at cell `i` (`FxRequest::errors`), as it was.
(define ado-error-at (subr da-assembles (int) unit)
  (lambda (i)
    (letrec ((nth (subr da-reads (da-strings int) string)
               (lambda (l k) (if (= k 0) (car l) (nth (cdr l) (- k 1))))))
      (ada-fail (nth (get adp-errors) (array-ref (get adp-a) i))))))

;; `t` := field `f` of the code bloblet (`ldr_field` of `self.field`).
(define ado-ldr-field (subr da-assembles (int int) unit)
  (lambda (t f) (ada-ldr-field t (adp-field f))))
;; The global's cell (`x9`) against its count of writes as compiled.
(define ado-writes-test (subr da-assembles (int) unit)
  (lambda (writes)
    (begin (ada-e (arm-ldur d-x11 d-x9 (ado-fld d-global-writes)))
           (ada-imm d-x16 writes)
           (ada-e (arm-cmp d-x11 d-x16)))))

;;; ------------------------------------------------------------ constants and globals

;; Entered with any number of arguments, their count in X9: it and the
;; registers into the state, for `rest` to list.
(define ado-vargs (subr da-assembles (int) unit)
  (lambda (i)
    (letrec ((args (subr da-assembles (int) unit)
               (lambda (j)
                 (if (= j 8)
                     #u
                     (begin (ada-sto (+ 1 j) d-st (+ d-st-args (* 8 j))) (args (+ j 1)))))))
      (begin (ada-sto d-x9 d-st d-st-nargs) (args 0)))))

;; `const`: an immediate as it is; a cellular word's procedure, its code;
;; a cellular closure of no free values, called just after or as a native
;; closure of its code; any other constant from a field.
(define ado-const (subr da-assembles (int) unit)
  (lambda (i)
    (let ((kind (array-ref (get adp-kind) i)) (q (array-ref (get adp-a) i)))
      (cond ((adp-oimm? i 0) (ada-imm d-result (adp-ob i 0)))
            ((= kind -1) (ado-error-at i))
            ((= kind 1) (ado-ldr-field d-result (adp-code-of q)))
            ((= kind 2)
             (if (>= (ado-called i) 0)
                 (set adp-pending (adp-code-of q))
                 (ado-ldr-field d-result (adp-closure-of q 0))))
            (else (ado-ldr-field d-result (adp-const-of (adp-oid i 0))))))))

;; What the global at `i` is bound to (`global_value`), as a field.
(define ado-global-value (subr da-reads (int) int)
  (lambda (i)
    (let ((kind (array-ref (get adp-kind) i)) (a (array-ref (get adp-a) i)))
      (cond ((= kind 1) (adp-code-of a))
            ((= kind 2) (adp-closure-of a (array-ref (get adp-b) i)))
            ((= kind 3) (adp-const-of a))
            (else (adp-cell-of (adp-oid i 0)))))))

;; `global`: for a call just after, bound; else its cell read, and while
;; the cell has not been written since, what it was bound to (a
;; procedure's code alone is no value: its closure, over nothing).
(define ado-global (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((cell (adp-oid i 0))
           (writes (array-ref (get adp-c) i))
           (kind (array-ref (get adp-kind) i))
           (g (ado-global-value i)))
      (cond ((= kind -1) (ado-error-at i))
            ((>= (ado-called i) 0)
             (begin
               (if (= kind 0) #u (begin (set adp-bound-cell cell) (set adp-bound-writes writes)))
               (set adp-pending g)))
            (else
             (begin
               (ado-ldr-field d-x9 (adp-cell-of cell))
               (ada-e (arm-ldur d-result d-x9 (ado-fld 2)))
               (if (= kind 0)
                   #u
                   (let ((other (ada-label)))
                     (begin
                       (ado-writes-test writes)
                       (ada-bc ada-c-ne other)
                       (ado-ldr-field
                        d-result
                        (if (= kind 1) (adp-closure-of (array-ref (get adp-a) i) 0) g))
                       (ada-bind other))))))))))

;; Always the test, as this code may outlive a later definition of the
;; global: how many times the cell has been written, against how many
;; when the code was compiled.
(define ado-global-guard (subr da-assembles (int) unit)
  (lambda (i)
    (let ((to (+ i (+ 4 (adp-o i 2)))))
      (begin
        (ado-ldr-field d-x9 (adp-cell-of (adp-oid i 0)))
        (ado-writes-test (adp-ob i 1))
        (ada-bc ada-c-ne (adp-edge (- (get adp-si) 1) to))))))

(define ado-setglbl (subr da-assembles (int) unit)
  (lambda (i)
    (begin
      (ado-ldr-field d-x9 (adp-cell-of (adp-oid i 0)))
      (ada-e (arm-stur d-result d-x9 (ado-fld 2)))
      ;; One more write, for the guards (`global-guard`).
      (ada-e (arm-ldur d-x16 d-x9 (ado-fld d-global-writes)))
      (ada-e (arm-add-imm d-x16 d-x16 (ada-fixnum 1)))
      (ada-e (arm-stur d-x16 d-x9 (ado-fld d-global-writes)))
      (ada-card-mark d-x9 (ado-fld 2) d-x16 d-x17))))

;; `RESULT` := a field `off` from `from`: past `ldur`'s reach through its
;; address in X16, by one `sub`, or past its reach by the offset.
(define ado-load-off (subr da-assembles (int int) unit)
  (lambda (from off)
    (cond ((>= off -256) (ada-e (arm-ldur d-result from off)))
          ((>= off -4095)
           (begin (ada-e (arm-sub-imm d-x16 from (- 0 off))) (ada-e (arm-ldur d-result d-x16 0))))
          (else (begin (ada-imm d-x16 off) (ada-e (arm-ldr-reg d-result from d-x16)))))))

;; Past `ldur`'s reach (32 values), through its address in X16, as
;; `field` does. No size limit, as on x86_64.
(define ado-lexical (subr da-assembles (int) unit)
  (lambda (i)
    (let ((from (if (and (>= (get adp-clo-slot) 0) (array-ref (get adp-framed) i))
                    (begin (ada-ld d-x9 d-frame (get adp-clo-slot)) d-x9)
                    d-clo)))
      (ado-load-off from (ado-fld (+ d-closure-free0 (adp-o i 0)))))))

;; A field past `ldur`'s reach (a module of more than 31 members, say)
;; through its address, in X16.
(define ado-field (subr da-assembles (int) unit)
  (lambda (i) (ado-load-off d-result (ado-fld (adp-o i 0)))))

(define ado-setfield (subr da-assembles (int) unit)
  (lambda (i)
    (let ((off (ado-fld (adp-o i 0))) (v (adp-o i 1)))
      (if (< off -4095)
          (begin (ada-imm d-x16 off)
                 (ada-e (arm-add d-x16 d-result d-x16))
                 (ada-e (arm-stur v d-x16 0))
                 (ada-card-mark d-x16 0 d-x16 d-x17))
          (begin
            (if (< off -256)
                (begin (ada-e (arm-sub-imm d-x16 d-result (- 0 off))) (ada-e (arm-stur v d-x16 0)))
                (ada-e (arm-stur v d-result off)))
            (ada-card-mark d-result off d-x16 d-x17))))))

;;; ------------------------------------------------------------ what registers hold

;; What `RESULT` or REGk holds of the frame (`held`): a slot, or -1; none
;; past REG8.
(define ado-held (subr da-reads (int) int)
  (lambda (k) (if (and (>= k 0) (<= k 8)) (array-ref (get adp-held) k) -1)))
(define ado-hold! (subr da-assembles (int int) unit)
  (lambda (k slot) (if (and (>= k 0) (<= k 8)) (array-set! (get adp-held) k slot) #u)))
(define ado-forget-all! (subr da-assembles () unit)
  (lambda ()
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r) (if (> r 8) #u (begin (ado-hold! r -1) (go (+ r 1)))))))
      (go 0))))
;; Slot `n`, written: held nowhere.
(define ado-forget-slot! (subr da-assembles (int) unit)
  (lambda (n)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r)
                 (if (> r 8) #u (begin (if (= (ado-held r) n) (ado-hold! r -1) #u) (go (+ r 1)))))))
      (go 0))))
;; The first of `RESULT` and REG1…REG8 that holds slot `n`, or -1.
(define ado-held-by (subr da-reads (int) int)
  (lambda (n)
    (letrec ((go (subr da-reads (int) int)
               (lambda (r) (cond ((> r 8) -1) ((= (ado-held r) n) r) (else (go (+ r 1)))))))
      (go 0))))
;; A version begun: nothing held; in the general one, the labels the
;; fixnum version goes to (`entered`).
(define ado-held-version (subr da-assembles (bool) unit)
  (lambda (fast)
    (begin (ado-forget-all!)
           (set adp-entered (if fast (the da-bools (make-array 1 #f)) (ada-targets))))))
(define ado-entered? (subr da-reads (int) bool)
  (lambda (l) (and (< l (array-length (get adp-entered))) (array-ref (get adp-entered) l))))
;; Before instruction `i`, `op`, its code from `at`: nothing held where
;; ways meet, where a way from the fixnum version comes in, or where its
;; conversions made registers over; then what it makes over forgotten.
(define ado-held-step (subr da-assembles (int int int) unit)
  (lambda (i op at)
    (begin
      (if (or (array-ref (get adp-target) i) (not (= (ada-here) at)) (ado-entered? (adp-label-g i)))
          (ado-forget-all!)
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
             (ado-hold! 0 -1))
            ((or (= op rop-op2) (= op rop-op2imm))
             (let ((j (adp-joinable (- (get adp-si) 1))))
               (begin (ado-hold! 0 -1)
                      (if (and (>= j 0) (= (adp-op j) rop-setreg))
                          (ado-hold! (adp-fix (+ j 1)) -1)
                          #u))))
            (else (ado-forget-all!))))))

;;; ------------------------------------------------------------ registers and slots

;; Whether a representation is an `i64`'s or a `u64`'s (`Rep::Raw`).
(define ado-raw-int? (subr pure (int) bool)
  (lambda (rep) (or (= rep nr-raw-signed) (= rep nr-raw-unsigned))))
;; `RESULT` := `REGk`, or where it is noted, for the `op2` just after.
(define ado-reg (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((k (adp-o i 0)) (j (adp-joinable (- (get adp-si) 1))))
      (if (and (>= j 0) (ado-op2? j)
               (not (ado-raw-int? (nr-rep (adp-in (- (get adp-si) 1)) (min k 8)))))
          (set adp-src k)
          (begin (ada-mov d-result k) (ado-hold! 0 (ado-held k)))))))

(define ado-setreg (subr da-assembles (int) unit)
  (lambda (i) (let ((k (adp-o i 0))) (begin (ada-mov k d-result) (ado-hold! k (ado-held 0))))))
(define ado-movereg (subr da-assembles (int) unit)
  (lambda (i)
    (begin (ada-mov (adp-o i 1) (adp-o i 0))
           (ado-hold! (adp-o i 1) (ado-held (adp-o i 0))))))

;; The frame made: the stack's limit checked (past it, the rest flushed
;; into the heap, `common_overflow`); this code bloblet in its slot; the
;; closure in its, if the code reads it. Its slots are not cleared but
;; those read before any write on some way, or all of a frame unmapped.
(define ado-save (subr da-assembles (int) unit)
  (lambda (i)
    (let ((size (get adp-size)) (rin (adp-in (- (get adp-si) 1))))
      (letrec ((raws (subr da-reads (int int) int)
                 (lambda (r acc)
                   (if (> r 8)
                       acc
                       (raws (+ r 1) (if (= (nr-rep rin r) nr-f64) (ado-with acc r) acc)))))
               (zero-all (subr da-assembles (int) unit)
                 (lambda (off)
                   (if (>= off (- size 8))
                       #u
                       (begin (ada-sto d-xzr d-frame off) (zero-all (+ off 8))))))
               (zero-live (subr da-assembles (int int) unit)
                 (lambda (k unwritten)
                   (if (or (= k (array-length (get adp-raw))) (>= k 64))
                       #u
                       (begin
                         (if (and (adp-bit? unwritten k) (not (array-ref (get adp-raw) k)))
                             (ada-sto d-xzr d-frame (array-ref (get adp-slot-off) k))
                             #u)
                         (zero-live (+ k 1) unwritten))))))
        (begin
          (ada-push-frame d-link size)
          (ada-e (arm-cmp-sp d-limit))
          (let ((over (ada-label)) (back (ada-label)))
            (begin
              (ada-bc ada-c-lo over)
              (ada-bind back)
              (set adp-overflows
                   (cons (product (1 over) (2 back) (3 (raws 1 0))) (get adp-overflows)))))
          (set adp-map-stored? #f)
          (if (get adp-unmapped)
              (zero-all 24)
              (zero-live 0 (array-ref (get adp-live-out) (- (get adp-si) 1))))
          (ada-ldr-field d-x9 1)
          (ada-sto d-x9 d-frame (get adp-self-slot))
          (if (get adp-captures) (ada-sto d-clo d-frame (get adp-clo-slot)) #u))))))

(define ado-pop (subr da-assembles (int) unit) (lambda (i) (ada-pop-frame (get adp-size))))

;; A slot's place in the frame.
(define ado-slot (subr da-reads (int) int) (lambda (k) (array-ref (get adp-slot-off) k)))

;; `stack`: `RESULT` := slot `n`, moved from a register that holds it.
(define ado-stack (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((n (adp-o i 0)) (r (ado-held-by n)))
      (begin
        (cond ((= r 0) #u)
              ((> r 0) (ada-mov d-result r))
              (else (ada-ld d-result d-frame (ado-slot n))))
        (ado-hold! 0 n)))))
(define ado-setstk (subr da-assembles (int) unit)
  (lambda (i)
    (let ((n (adp-o i 0)))
      (begin (ada-sto d-result d-frame (ado-slot n)) (ado-forget-slot! n) (ado-hold! 0 n)))))
;; `load`: REGk := slot `n`, from a register that holds it.
(define ado-load (subr da-assembles (int) unit)
  (lambda (i)
    (let* ((k (adp-o i 0)) (n (adp-o i 1)) (f (ado-held-by n)))
      (begin
        (cond ((= f k) #u)
              ((>= f 0) (ada-mov k f))
              (else (ada-ld k d-frame (ado-slot n))))
        (ado-hold! k n)))))

;; `store`, and its slot read back at once: the register is still it.
(define ado-store (subr da-assembles (int) unit)
  (lambda (i)
    (let ((k (adp-o i 0)) (slot (adp-o i 1)))
      (begin
        (ada-sto k d-frame (ado-slot slot))
        (ado-forget-slot! slot)
        (ado-hold! k slot)
        (let ((j (adp-joinable (- (get adp-si) 1))))
          (if (and (>= j 0) (= (adp-op j) rop-stack) (adp-fix? (+ j 1)) (= (adp-fix (+ j 1)) slot))
              (begin
                (ada-bind (adp-label j))
                (set adp-si (+ (get adp-si) 1))
                (let ((n (adp-joinable (- (get adp-si) 1))))
                  (if (and (>= n 0) (ado-op2? n))
                      (set adp-src k)
                      (begin (ada-mov d-result k) (ado-hold! 0 slot)))))
              #u))))))

;; A list may be `nil`: `car` of it traps.
(define ado-op1 (subr da-assembles (int) unit)
  (lambda (i)
    (let ((r (adp-o i 0)))
      (if (or (= r routine-pair-car) (= r routine-pair-cdr))
          (begin
            (ada-e (arm-and-low d-x16 d-result 3))
            (ada-e (arm-cmp-imm d-x16 d-tag-pair))
            (ada-trap d-not-a-pair ada-c-ne)
            (ada-e (arm-ldur d-result d-result (if (= r routine-pair-car) -1 7))))
          (adp-decline (string-append "op1 " (d-routine-name r)))))))

;;; ------------------------------------------------------------ `int` operations

;; `op2` and `op2imm`: an `int` sum, difference or comparison, or `eq?`,
;; in line, its slow path (`IntSlow`) after the code. The other operand:
;; a register, or a constant, which an add, a subtract or a compare may
;; take as it is when it is small.
(define ado-op2 (subr da-assembles (int int) unit)
  (lambda (i op)
    (let* ((x (get adp-src))
           (imm? (and (= op rop-op2imm) (adp-oimm? i 1) (< (adp-ob i 1) 4096)))
           (small (if imm? (adp-ob i 1) 0))
           (other (begin
                    (set adp-src d-result)
                    (cond ((= op rop-op2) (adp-o i 1))
                          ((not (adp-oimm? i 1))
                           (begin (ado-ldr-field d-x16 (adp-const-of (adp-oid i 1))) d-x16))
                          (imm? d-x16)
                          (else (begin (ada-imm d-x16 (adp-ob i 1)) d-x16)))))
           (r (adp-o i 0))
           (fast-int (and (get adp-fast) (nr-int-routine? r)))
           (add-sub (or (= r routine-int-add) (= r routine-int-sub)))
           ;; A sum or difference only moved on to a register, and then
           ;; not read: made in that register.
           (j (adp-joinable (- (get adp-si) 1)))
           (d (if (and add-sub (>= j 0) (= (adp-op j) rop-setreg)
                       (< (+ (get adp-si) 1) (adp-ns))
                       (ado-ignores? (adp-start (+ (get adp-si) 1))))
                  (begin (ada-bind (adp-label j)) (set adp-si (+ (get adp-si) 1)) (adp-fix (+ j 1)))
                  d-result)))
      (cond ((not (or add-sub (= r routine-int-less) (= r routine-int-eq) (= r routine-eq)))
             (adp-decline (string-append (d-op-name op) (string-append " " (d-routine-name r)))))
            (else (ado-op2-made i op x imm? small other r fast-int add-sub d))))))

;; The rest of `ado-op2`, its operands placed: the test for fixnums, if a
;; slow path, and the sum in its register, which the slow path undoes to
;; the operand if it is that; in a scratch one if it is the other
;; operand's, which could not be (in the fixnum version, not over an
;; operand either: an overflow goes over to the general version of this
;; instruction, which does it again).
(define ado-op2-made
  (subr da-assembles (int int int bool int int int bool bool int) unit)
  (lambda (i op x imm? small other r fast-int add-sub d)
    (let* ((prim (cond (fast-int -1)
                       ((= r routine-int-add) d-prim-add)
                       ((= r routine-int-sub) d-prim-sub)
                       ((= r routine-int-less) d-prim-int-less)
                       ((and (= r routine-int-eq) (not (and (= op rop-op2imm) (adp-ofix? i 1))))
                        d-prim-int-eq)
                       (else -1)))
           (entry (ada-label))
           (back (ada-label))
           (dst (if (or (and (not imm?) (= d other)) (and fast-int (= d x))) d-x13 d)))
      (begin
        (if (>= prim 0)
            (begin
              (if (or imm? (= other x))
                  (ada-e (arm-tst-low x 3))
                  (begin (ada-e (arm-orr d-x13 x other)) (ada-e (arm-tst-low d-x13 3))))
              (ada-bc ada-c-ne entry))
            #u)
        (ada-e (cond ((and (= r routine-int-add) imm?) (arm-adds-imm dst x small))
                     ((= r routine-int-add) (arm-adds dst x other))
                     ((and (= r routine-int-sub) imm?) (arm-subs-imm dst x small))
                     ((= r routine-int-sub) (arm-subs dst x other))
                     (imm? (arm-cmp-imm x small))
                     (else (arm-cmp x other))))
        (ado-op2-ends i x imm? small other r fast-int add-sub d dst prim entry back)))))

;; Where an `op2`'s value goes: an overflow's way, the flags to a branch
;; just after, or a boolean; its slow path noted.
(define ado-op2-ends
  (subr da-assembles (int int bool int int int bool bool int int int int int) unit)
  (lambda (i x imm? small other r fast-int add-sub d dst prim entry back)
    (let ((cond (if (= r routine-int-less) ada-c-lt ada-c-eq))
          (slow (lambda ((ov int) (into int) (bl int) (bt bool))
                  (product (1 entry) (2 ov) (3 back) (4 x) (5 (if imm? -1 other)) (6 small)
                           (7 into) (8 prim) (9 (= r routine-int-sub)) (10 bl) (11 bt)))))
      (letrec ((note (subr da-assembles (dr-int-slow) unit)
                 (lambda (s) (if (>= prim 0) (set adp-int-slows (cons s (get adp-int-slows))) #u))))
        (begin
          (cond ((and add-sub fast-int)
                 (begin (ada-bc ada-c-vs (adp-label-g i)) (if (= dst d) #u (ada-mov d dst))
                        (note (slow -1 d -1 #f))))
                (add-sub
                 (let ((ov (ada-label)))
                   (begin (ada-bc ada-c-vs ov)
                          (if (= dst d) #u (ada-mov d dst))
                          (note (slow ov d -1 #f)))))
                (else
                 (ado-op2-test cond (lambda ((l int) (t bool)) (note (slow -1 d-result l t))))))
          (ada-bind back))))))

;; A test that only a branch just after reads: the branch on the flags,
;; with no boolean made (on the slow path, on the boolean the call made);
;; else the boolean. `noted` notes the slow path, with the branch's label
;; (-1 for none) and whether it is taken when true.
(define ado-op2-test (subr da-assembles (int (subr da-assembles (int bool) unit)) unit)
  (lambda (cond noted)
    (let ((j (adp-branch-on (- (get adp-si) 1))))
      (if (>= j 0)
          (let* ((to (adp-branch-to j))
                 ;; `branchf` goes where the test fails; `brancht` where it
                 ;; holds.
                 (taken-if-true (= (adp-op j) rop-brancht))
                 (c (cond (taken-if-true cond) ((= cond ada-c-eq) ada-c-ne) (else ada-c-ge))))
            (begin
              (ada-bind (adp-label j))
              (let ((l (adp-edge (get adp-si) to)))
                (begin (ada-bc c l) (noted l taken-if-true)))
              (set adp-si (+ (get adp-si) 1))))
          (begin (ada-imm d-x9 d-true)
                 (ada-imm d-x17 d-false)
                 (ada-e (arm-csel d-result d-x9 d-x17 cond))
                 (noted -1 #f))))))

;;; ------------------------------------------------------------ calls

;; Whether the value of the instruction being compiled is taken raw.
(define ado-raw-ref? (subr da-reads () bool)
  (lambda () (array-ref (get adp-raw-refs) (- (get adp-si) 1))))
;; A call. Of a global's procedure that captures nothing: its code, from
;; this bloblet's field, entered at its start. Of any other procedure: a
;; native closure, in `CLO`, whose field 2 is its code, entered so; one
;; whose field 2 is not in the code area is not native code, and traps.
;; A procedure known here that takes some arguments raw: given them so,
;; entered past its unboxing of them.
(define ado-invoke (subr da-assembles (int int) unit)
  (lambda (i op)
    (let* ((tail (= op rop-tailinvoke))
           (callee (array-ref (get adp-callees) (- (get adp-si) 1)))
           (raws (bitwise-and (arithmetic-shift callee 1) 510))
           (skip (if (= raws 0) 0 (adr-raw-entry-skip (ado-count raws))))
           (stub (ada-label))
           (after (ada-label))
           (cv (adp-o i 1))
           (pending (get adp-pending))
           (note (lambda ()
                   (set adp-foreign
                        (cons (product (1 stub) (2 after) (3 (adp-o i 0)) (4 tail))
                              (get adp-foreign))))))
      (begin
        (set adp-pending -1)
        (if (>= (get adp-bound-cell) 0)
            ;; A global bound as compiled: while its cell has not been
            ;; written since, as bound; else, out of the way, through the
            ;; cell, as what it holds now.
            (let ((slow (ada-label)) (join (ada-label)))
              (begin
                (ado-ldr-field d-x9 (adp-cell-of (get adp-bound-cell)))
                (ada-e (arm-ldur d-clo d-x9 (ado-fld 2)))
                (ado-writes-test (get adp-bound-writes))
                (ada-bc ada-c-ne slow)
                (set adp-bound-cell -1)
                (ado-bound-callee pending skip)
                (ada-bind join)
                (set adp-cell-slows
                     (cons (product (1 slow) (2 join) (3 raws)) (get adp-cell-slows)))))
            (ado-callee pending cv skip stub note))
        ;; The count, for a variadic callee (`vargs`), Larceny's way:
        ;; every call passes it.
        (ada-e (arm-movz d-x9 (adp-o i 0) 0))
        (ada-e (arm-add d-x16 d-x16 d-delta))
        (ada-e (if tail (arm-br d-x16) (arm-blr d-x16)))
        (ada-bind after)
        (if (and (not tail) (ado-raw-ref?)) (adr-take-raw-f64) #u)))))

;; Past the callee's unboxing of its raw parameters.
(define ado-past-raw (subr da-assembles (int) unit)
  (lambda (skip) (if (> skip 0) (ada-e (arm-add-imm d-x16 d-x16 skip)) #u)))
;; The callee of a call bound by its global, while the global holds it.
(define ado-bound-callee (subr da-assembles (int int) unit)
  (lambda (pending skip)
    (let ((tag (bitwise-and pending 7)))
      (cond ((= tag 1) (begin (ado-ldr-field d-x16 pending) (ado-past-raw skip)))
            ;; Another compile's native code (`native_params`), what the
            ;; cell holds while the guard holds.
            ((= tag 2)
             (begin (ada-e (arm-ldur d-x16 d-clo (ado-fld d-closure-word))) (ado-past-raw skip)))
            (else (begin (ado-ldr-field d-clo pending)
                         (ada-e (arm-ldur d-x16 d-clo (ado-fld d-closure-word)))))))))
;; Any other's: the procedure known, through the global's cell when the
;; code runs (what it holds then, native code or not), a closure or a
;; constant, or `RESULT`'s.
(define ado-callee (subr da-assembles (int int int int (subr da-assembles () unit)) unit)
  (lambda (pending cv skip stub note)
    (let ((tag (bitwise-and pending 7))
          ;; The callee's convention, by its type (`regcode::CONVS`):
          ;; cellular, called out (`common_foreign`) with no look; native
          ;; or fx, its code run, native code or a stub that enters
          ;; `foreign` (`docs/research/code-stubs.md`).
          (not-native
           (lambda ()
             (if (= cv rconv-cellular)
                 (ada-b stub)
                 (ada-e (arm-ldur d-x16 d-clo (ado-fld d-closure-word)))))))
      (cond ((< pending 0)
             (begin (ada-mov d-clo d-result) (not-native) (if (= cv rconv-cellular) (note) #u)))
            ((= tag 1) (begin (ado-ldr-field d-x16 pending) (ado-past-raw skip)))
            ((= tag 3)
             (begin
               (ado-ldr-field d-x9 pending)
               (ada-e (arm-ldur d-clo d-x9 (ado-fld 2)))
               (not-native)
               (if (= cv rconv-cellular) (note) #u)))
            (else (begin (ado-ldr-field d-clo pending)
                         (ada-e (arm-ldur d-x16 d-clo (ado-fld d-closure-word)))))))))

(define ado-invokeself (subr da-assembles (int) unit)
  (lambda (i)
    (begin
      (if (and (>= (get adp-clo-slot) 0) (get adp-captures))
          (ada-ld d-clo d-frame (get adp-clo-slot))
          #u)
      (ada-bl (get adp-entry-checked))
      (if (ado-raw-ref?) (adr-take-raw-f64) #u))))

(define ado-return (subr da-assembles (int) unit)
  (lambda (i)
    (if (= (nr-rep (adp-in (- (get adp-si) 1)) 0) nr-f64) (adr-raw-return) (ada-e arm-ret))))

;;; ------------------------------------------------------------ branches

;; The slots live after the instruction being compiled.
(define ado-live-out (subr da-reads () int)
  (lambda () (array-ref (get adp-live-out) (- (get adp-si) 1))))

;; A branch; a loop's (back to its head) polled first, keeping what the
;; head reads, raw or not, with the frame's map for here.
(define ado-branch (subr da-assembles (int int) unit)
  (lambda (i op)
    (let* ((to (+ i (+ 2 (adp-o i 0)))) (l (adp-edge (- (get adp-si) 1) to)))
      (if (= op rop-branch)
          (begin (if (array-ref (get adp-back-to) to) (ado-loop-poll i to) #u) (ada-b l))
          (begin (ada-imm d-x16 d-false)
                 (ada-e (arm-cmp d-result d-x16))
                 (ada-bc (if (= op rop-branchf) ada-c-eq ada-c-ne) l))))))

(define ado-loop-poll (subr da-assembles (int int) unit)
  (lambda (i to)
    (let* ((t (adp-si-of to))
           (rep (adp-in (- (get adp-si) 1)))
           (live (array-ref (get adp-live) t))
           (out (ada-label))
           (back (ada-label)))
      (letrec ((masks (subr da-reads (int int int) (productof (1 int) (2 int)))
                 (lambda (r vals raws)
                   (if (> r 8)
                       (product (1 vals) (2 raws))
                       (let ((kept (and (adp-bit? live r) (not (= (nr-rep rep r) nr-undefined))))
                             (raw? (nr-raw? (nr-rep rep r)))
                             (bit (arithmetic-shift 1 r)))
                         (masks (+ r 1)
                                (if (and kept (not raw?)) (bitwise-ior vals bit) vals)
                                (if (and kept raw?) (bitwise-ior raws bit) raws)))))))
        (let ((m (masks 0 0 0))
              (mapped (and (>= (get adp-frame) 0) (array-ref (get adp-framed) i))))
          (begin
            (ada-e (arm-subs-imm d-fuel d-fuel 1))
            (ada-bc ada-c-lo out)
            (ada-bind back)
            (set adp-polls
                 (cons (product (1 out) (2 back) (3 (extract m 1)) (4 (extract m 2))
                                (5 (and (get adp-captures) (not (array-ref (get adp-framed) i))))
                                (6 mapped)
                                (7 (if mapped (adp-map-word (ado-live-out)) 0)))
                       (get adp-polls)))
            (set adp-map-stored? #f)))))))
)))
