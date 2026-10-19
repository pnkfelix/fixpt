;;; Where native code keeps `i64`, `u64` and `f64` values, in FX-26:
;;; `fixpt-native/src/direct/reps.rs`, step for step, each step `nr-` and
;;; its Rust name. The Rust pass is this one's oracle: on every register
;;; word of the front end, the same results (`tests/native_reps.rs`).
;;;
;;; Raw, as the machine's 64 bits, in registers only (`RESULT`, REG1…REG8),
;;; and as the value they are everywhere else. Register code does not say
;;; which: this pass says, instruction by instruction, forward over the
;;; procedure's register code. An operation of `i64` or `u64` takes its
;;; operands raw and gives its value raw, a comparison and `T->int`
;;; excepted; so does one of `f64` the machine does exactly as IEEE says
;;; (`nr-raw-op`), a comparison excepted. `reg`, `setreg` and `movereg`
;;; move a register as it is. A frame slot that only `f64` operations read
;;; (`nr-raw-slots`) holds an `f64` raw. Anything else that reads a
;;; register reads it as a value: a raw one is boxed first. Where ways
;;; meet, a register raw on one is raw after (`nr-join`).
;;;
;;; The numbers: a register's representation (`Rep`) is `nr-undefined` 0,
;;; `nr-value` 1, `nr-raw-signed` 2, `nr-raw-unsigned` 3, `nr-f64` 4 or
;;; `nr-fix` 5 (a value known to be a fixnum, in a fixnum version only);
;;; those of the nine registers (`Reps`) one int, three bits each,
;;; `RESULT`'s lowest. How a register's value is used (`Demand`), the same
;;; way: none 0, `f64` 1, other 2, both 3, any 4. A conversion (`Convert`)
;;; is 128 times its kind (box 0, unbox 1, check 2), plus 8 times its
;;; register, plus its representation (0 for a check). A way's unboxing
;;; (`nr-unboxes`) is 8 times its register plus its representation.
;;; Instructions are numbered by where they are in `starts`.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the layouts.

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (dl-types (load-module "fx26:native-direct-x64-layout-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx")))
  (lambda ((dl (select dl-types native-direct-x64-layout-sig))
           (layout (select layout-types layout-sig)))
    (module
(hide (include direct-types))
(hide (include dl) (include layout))

;; What `webs` finds: by instruction, the frame slot it touches (-1 for
;; none) and its web; by web, whether an `f64`'s and whether read.
(define-type nr-webs (productof (1 da-ints) (2 da-ints) (3 da-bools) (4 da-bools)))

(define nr-undefined int 0)
(define nr-value int 1)
(define nr-raw-signed int 2)
(define nr-raw-unsigned int 3)
(define nr-f64 int 4)
(define nr-fix int 5)
(define nr-raw? (subr pure (int) bool) (lambda (rep) (and (>= rep 2) (<= rep 4))))

;; Register `r`'s field of `reps` (or of demands), `reps` with it `v`, and
;; all nine `v`.
(define nr-rep (subr pure (int int) int)
  (lambda (reps r) (bitwise-and (arithmetic-shift reps (- 0 (* 3 r))) 7)))
(define nr-with (subr pure (int int int) int)
  (lambda (reps r v)
    (+ (- reps (arithmetic-shift (nr-rep reps r) (* 3 r))) (arithmetic-shift v (* 3 r)))))
(define nr-all (subr pure (int) int) (lambda (v) (* v 19173961)))

;; `f` on each register of `a` and `b`, from register `r` on.
(define nr-each (subr da-reads ((subr pure (int int) int) int int int) int)
  (lambda (f a b r)
    (if (= r 9)
        a
        (nr-each f (nr-with a r (f (nr-rep a r) (nr-rep b r))) b (+ r 1)))))

;; Where two ways meet: raw on either, raw; optimistic, a fixnum where
;; either way knows it, the other way testing it (`nr-checks`).
(define nr-join1 (subr pure (int int) int)
  (lambda (a b)
    (cond ((= a nr-undefined) b)
          ((= b nr-undefined) a)
          ((nr-raw? a) a)
          ((nr-raw? b) b)
          ((or (= a nr-fix) (= b nr-fix)) nr-fix)
          (else nr-value))))
(define nr-join (subr da-reads (int int) int) (lambda (a b) (nr-each nr-join1 a b 0)))

;; The registers a way into `to` must unbox, and to what: a value there,
;; raw at `to`.
(define nr-unboxes (subr da-assembles (int int) da-bytes)
  (lambda (from to)
    (letrec ((go (subr da-assembles (int da-bytes) da-bytes)
               (lambda (r acc)
                 (if (< r 0)
                     acc
                     (let ((f (nr-rep from r)) (t (nr-rep to r)))
                       (go (- r 1)
                           (if (and (or (= f nr-value) (= f nr-fix)) (nr-raw? t))
                               (cons (+ (* 8 r) t) acc)
                               acc)))))))
      (go 8 nil))))
;; The registers a way into `to` must test for a fixnum, in a fixnum
;; version: a value there, known at `to`, and live there (`live`, a mask).
(define nr-checks (subr da-assembles (int int int) da-bytes)
  (lambda (from to live)
    (letrec ((go (subr da-assembles (int da-bytes) da-bytes)
               (lambda (r acc)
                 (cond ((< r 0) acc)
                       ((and (= (nr-rep from r) nr-value) (= (nr-rep to r) nr-fix)
                             (= 1 (bitwise-and (arithmetic-shift live (- 0 r)) 1)))
                        (go (- r 1) (cons r acc)))
                       (else (go (- r 1) acc))))))
      (go 8 nil))))

;;; ------------------------------------------------------------ raw operations

;; Whether `s` begins with `p`.
(define nr-prefix? (subr pure (string string) bool)
  (lambda (p s)
    (and (>= (string-length s) (string-length p))
         (string=? (substring s 0 (string-length p)) p))))
;; `s` from `k` on.
(define nr-from (subr pure (string int) string)
  (lambda (s k) (substring s k (string-length s))))
(define nr-first3 (subr pure (string) string) (lambda (s) (substring s 0 3)))
(define nr-compare? (subr pure (string) bool)
  (lambda (w)
    (or (string=? w "<") (string=? w "<=") (string=? w ">") (string=? w ">=") (string=? w "="))))
;; The `f64` operations the machine does as the runtime does.
(define nr-native-f64? (subr pure (string) bool)
  (lambda (w)
    (or (nr-compare? w) (string=? w "+") (string=? w "-") (string=? w "*") (string=? w "/")
        (string=? w "-abs") (string=? w "-neg") (string=? w "-sqrt") (string=? w "-floor")
        (string=? w "-ceiling") (string=? w "-truncate") (string=? w "-round")
        (string=? w "->int"))))

;; An operation native code does on raw operands, by its primitive's name
;; (`raw_op`): an `i64` or `u64` one (`%fx26-u64*`, `%fx26-int->i64`), or
;; one of `f64` the machine does exactly as the runtime does.
(define nr-raw-op (subr da-assembles (string) nr-raw-op)
  (lambda (name)
    (let ((none (product (1 0) (2 #f) (3 ""))))
      (if (not (nr-prefix? "%fx26-" name))
          none
          (let* ((rest (nr-from name 6)) (n (string-length rest)))
            (cond ((string=? rest "int->f64") (product (1 2) (2 #f) (3 "from-int")))
                  ((nr-prefix? "f64" rest)
                   (let ((what (nr-from rest 3)))
                     (if (nr-native-f64? what) (product (1 2) (2 #f) (3 what)) none)))
                  (else
                   (let* ((from? (nr-prefix? "int->" rest))
                          (t (cond (from? (nr-from rest 5)) ((>= n 3) (nr-first3 rest)) (else "")))
                          (what (cond (from? "from") ((>= n 3) (nr-from rest 3)) (else ""))))
                     (cond ((string=? t "i64") (product (1 1) (2 #t) (3 what)))
                           ((string=? t "u64") (product (1 1) (2 #f) (3 what)))
                           (else none))))))))))

;; What a raw operation takes and gives (`raw_shape`): its first operand,
;; its second, its value, as `Rep`s, packed as the first three registers.
(define nr-shape (subr pure (int int int) int)
  (lambda (x y out) (+ x (+ (* 8 y) (* 64 out)))))
(define nr-raw-shape (subr pure (nr-raw-op) int)
  (lambda (op)
    (let* ((what (extract op 3))
           (plain (and (not (nr-compare? what)) (not (string=? what "->int"))))
           (shape nr-shape))
      (cond ((= (extract op 1) 1)
             (let ((raw (if (extract op 2) nr-raw-signed nr-raw-unsigned)))
               (shape raw
                      (if (or (string=? what "-shl") (string=? what "-shr")) nr-value raw)
                      (if plain raw nr-value))))
            ((string=? what "from-int") (shape nr-value nr-value nr-f64))
            ((= (extract op 1) 2) (shape nr-f64 nr-f64 (if plain nr-f64 nr-value)))
            (else (shape nr-value nr-value nr-value))))))

;;; ------------------------------------------------------------ cells

;; Cell `i`'s value as a fixnum; whether it is one; operand `j` of the
;; instruction at `i`; and how many cells there are.
(define nr-cell (subr da-reads (nr-cells int) int)
  (lambda (c i) (array-ref (extract c 1) i)))
(define nr-k (subr da-reads (nr-cells int int) int)
  (lambda (c i j)
    ;; An instruction's operand read where it has none (as `k0` is read
    ;; of every instruction, `return`'s too) is 0.
    (let ((at (+ i (+ 1 j))))
      (if (< at (array-length (extract c 1))) (array-ref (extract c 1) at) 0))))
(define nr-ncells (subr da-reads (nr-cells) int) (lambda (c) (array-length (extract c 1))))
;; Whether operand `j` of the instruction at `i` is the fixnum `v`.
(define nr-operand-is? (subr da-reads (nr-cells int int int) bool)
  (lambda (c i j v)
    (and (array-ref (extract c 2) (+ i (+ 1 j))) (= (nr-k c i j) v))))
(define nr-prim (subr da-reads (nr-cells int) string)
  (lambda (c i) (d-prim-name (nr-k c i 0))))

;; Whether instruction `i` reads a flat array's element, or an `f64` at a
;; blobref (`is_flat_ref`).
(define nr-is-flat-ref? (subr da-reads (nr-cells int) bool)
  (lambda (c i)
    (let ((op (nr-cell c i)))
      (or (and (or (= op rop-prim2) (= op rop-prim2imm))
               (string=? (nr-prim c i) "%fx26-flatarray-ref"))
          (and (= op rop-prim2imm)
               (string=? (nr-prim c i) "%fx26-suffix-ref-get")
               (nr-operand-is? c i 1 d-flat-f64))))))
;; Whether `prim3imm` at `i` writes an `f64` at a blobref (`is_f64_set`).
(define nr-is-f64-set? (subr da-reads (nr-cells int) bool)
  (lambda (c i)
    (and (string=? (nr-prim c i) "%fx26-suffix-ref-set!") (nr-operand-is? c i 1 d-flat-f64))))

;; Whether routine `n` is one of `int`'s a fixnum version does without
;; testing its operands (`int_routine`).
(define nr-int-routine? (subr pure (int) bool)
  (lambda (n)
    (or (= n routine-int-add) (= n routine-int-sub) (= n routine-int-less) (= n routine-int-eq))))

;; Whether parameter register `r` (REG1…REG8) is one `params` takes raw.
(define nr-raw-param? (subr pure (int int) bool)
  (lambda (params r)
    (and (>= r 1) (<= r 8) (= 1 (bitwise-and (arithmetic-shift params (- 1 r)) 1)))))
;; Whether frame slot `n` holds a raw `f64`.
(define nr-raw-slot? (subr da-reads (da-bools int) bool)
  (lambda (raw n) (and (>= n 0) (< n (array-length raw)) (array-ref raw n))))

;; Where each instruction starts.
(define nr-starts (subr da-assembles (nr-cells) da-ints)
  (lambda (c)
    (let ((n (nr-ncells c)))
      (letrec ((next (subr da-reads (int) int)
                 (lambda (i) (+ i (+ 1 (d-operands (nr-cell c i))))))
               (count (subr da-reads (int int) int)
                 (lambda (i k) (if (>= i n) k (count (next i) (+ k 1)))))
               (fill (subr da-assembles (da-ints int int) unit)
                 (lambda (a i k)
                   (if (>= i n) #u (begin (array-set! a k i) (fill a (next i) (+ k 1)))))))
        (let ((a (the da-ints (make-array (count 0 0) 0))))
          (begin (fill a 0 0) a))))))

;; Each instruction's successors, by number (`successors`): the next, then
;; where it branches.
(define nr-successors (subr da-assembles (nr-cells da-ints) (arrayof da-bytes @k))
  (lambda (c starts)
    (let* ((ns (array-length starts))
           (n (nr-ncells c))
           (at (the da-ints (make-array (+ n 1) -1)))
           (out (the (arrayof da-bytes @k) (make-array ns nil))))
      (letrec ((index (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (begin (array-set! at (array-ref starts si) si) (index (+ si 1))))))
               (target (subr da-reads (int) int)
                 (lambda (i)
                   (let* ((k (d-operands (nr-cell c i)))
                          (to (+ (+ i (+ 1 k)) (nr-cell c (+ i k)))))
                     (if (and (>= to 0) (<= to n)) (array-ref at to) -1))))
               (fill (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (let* ((i (array-ref starts si)) (op (nr-cell c i))
                              (next (the da-bytes (if (< (+ si 1) ns) (cons (+ si 1) nil) nil)))
                              (t (if (or (= op rop-branch) (= op rop-branchf) (= op rop-brancht)
                                         (= op rop-global-guard))
                                     (target i)
                                     -1))
                              (to (the da-bytes (if (>= t 0) (cons t nil) nil))))
                         (begin
                           (array-set! out si
                                       (cond ((or (= op rop-return) (= op rop-tailinvoke)) nil)
                                             ((= op rop-branch) to)
                                             ((or (= op rop-branchf) (= op rop-brancht)
                                                  (= op rop-global-guard))
                                              (append next to))
                                             (else next)))
                           (fill (+ si 1))))))))
        (begin (index 0) (fill 0) out)))))

;;; ------------------------------------------------------------ demands

;; How a register's value is used from a point on (`Demand`).
(define nr-d-none int 0)
(define nr-d-f64 int 1)
(define nr-d-other int 2)
(define nr-d-both int 3)
(define nr-d-any int 4)
;; Both ways' uses.
(define nr-djoin1 (subr pure (int int) int)
  (lambda (a b)
    (cond ((= a nr-d-none) b)
          ((= b nr-d-none) a)
          ((= a nr-d-any) b)
          ((= b nr-d-any) a)
          ((= a b) a)
          (else nr-d-both))))
(define nr-djoin (subr da-reads (int int) int) (lambda (a b) (nr-each nr-djoin1 a b 0)))

;; Register `r` of `d` defined; used `how`; moved from `from` to `to`.
(define nr-def (subr pure (int int) int) (lambda (d r) (nr-with d r nr-d-none)))
(define nr-use (subr pure (int int int) int)
  (lambda (d r how) (nr-with d r (nr-djoin1 (nr-rep d r) how))))
(define nr-mv (subr pure (int int int) int)
  (lambda (d from to)
    (let ((how (nr-rep d to)) (d1 (nr-with d to nr-d-none)))
      (if (or (not (= from 0)) (not (= to 0))) (nr-use d1 from how) d1))))
;; REG1…REGn (eight at most) defined; used `how`.
(define nr-def-regs (subr da-reads (int int) int)
  (lambda (d n)
    (letrec ((go (subr da-reads (int int) int)
               (lambda (d r) (if (or (> r n) (> r 8)) d (go (nr-def d r) (+ r 1))))))
      (go d 1))))
(define nr-use-regs (subr da-reads (int int int) int)
  (lambda (d n how)
    (letrec ((go (subr da-reads (int int) int)
               (lambda (d r) (if (or (> r n) (> r 8)) d (go (nr-use d r how) (+ r 1))))))
      (go d 1))))

;; What instruction `i` asks of the registers before it, given what is
;; asked of them after (`after`): backward, as liveness is (`demand_step`).
;; Moves pass the demand on; an operand of an `f64` operation asks for a
;; raw `f64`; anything else, conservatively, for a value.
(define nr-slot-how (subr da-reads (da-bools int) int)
  (lambda (raw n) (if (nr-raw-slot? raw n) nr-d-f64 nr-d-other)))
(define nr-f64-how (subr pure (int) int) (lambda (r) (if (= r nr-f64) nr-d-f64 nr-d-other)))
(define nr-demand-step (subr da-assembles (nr-cells int int da-bools) int)
  (lambda (c i after raw)
    (let* ((op (nr-cell c i))
           (k0 (nr-k c i 0))
           (d after))
      (cond
        ((= op rop-args) (nr-def-regs d k0))
        ((= op rop-vargs) (nr-def-regs d 8))
        ((or (= op rop-const) (= op rop-global) (= op rop-lexical) (= op rop-stack)) (nr-def d 0))
        ((= op rop-load) (nr-def d k0))
        ((= op rop-reg) (if (= k0 0) (nr-def d 0) (nr-mv d k0 0)))
        ((= op rop-setreg) (nr-mv d 0 k0))
        ((= op rop-movereg) (if (= k0 0) (nr-def d (nr-k c i 1)) (nr-mv d k0 (nr-k c i 1))))
        ((= op rop-store) (nr-use d k0 (nr-slot-how raw (nr-k c i 1))))
        ((= op rop-setstk) (nr-use d 0 (nr-slot-how raw k0)))
        ((or (= op rop-setglbl) (= op rop-return) (= op rop-branchf) (= op rop-brancht))
         (nr-use d 0 nr-d-other))
        ((or (= op rop-op1) (= op rop-op2imm) (= op rop-field) (= op rop-op2) (= op rop-setfield))
         (let ((d1 (nr-use (nr-def d 0) 0 nr-d-other)))
           (if (or (= op rop-op2) (= op rop-setfield)) (nr-use d1 (nr-k c i 1) nr-d-other) d1)))
        ((or (= op rop-prim1) (= op rop-prim2) (= op rop-prim2imm))
         (let* ((rop (nr-raw-op (d-prim-name k0)))
                (shape (if (= (extract rop 1) 2) (nr-raw-shape rop) (nr-all nr-value)))
                (d1 (nr-use (nr-def d 0) 0 (nr-f64-how (nr-rep shape 0)))))
           (if (= op rop-prim2) (nr-use d1 (nr-k c i 1) (nr-f64-how (nr-rep shape 1))) d1)))
        ((= op rop-prim3imm)
         (nr-use (nr-use (nr-def d 0) 0 nr-d-other)
                 (nr-k c i 2)
                 (if (nr-is-f64-set? c i) nr-d-f64 nr-d-other)))
        ((or (= op rop-prim) (= op rop-lambda) (= op rop-cellular) (= op rop-invoke)
             (= op rop-tailinvoke) (= op rop-invokeself))
         (let* ((n (if (or (= op rop-prim) (= op rop-lambda) (= op rop-cellular)) (nr-k c i 1) k0))
                (call? (or (= op rop-invoke) (= op rop-tailinvoke)))
                (d1 (if call? (nr-use 0 0 nr-d-other) 0)))
           (nr-use-regs d1 n (if (or call? (= op rop-invokeself)) nr-d-any nr-d-other))))
        ((or (= op rop-branch) (= op rop-global-guard) (= op rop-save) (= op rop-pop)) d)
        (else (nr-all nr-d-other))))))

;; What each instruction asks of the registers as it starts (the backward
;; fixpoint of `nr-demand-step`), and each instruction's successors.
(define nr-changed (ref bool @k) (new #f))
(define nr-demands
  (subr da-assembles (nr-cells da-ints da-bools)
        (productof (1 da-ints) (2 (arrayof da-bytes @k))))
  (lambda (c starts raw)
    (let* ((ns (array-length starts))
           (succ (nr-successors c starts))
           (before (the da-ints (make-array ns 0))))
      (letrec ((after (subr da-reads (da-bytes int) int)
                 (lambda (ts acc)
                   (if (null? ts) acc (after (cdr ts) (nr-djoin acc (array-ref before (car ts)))))))
               (pass (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (< si 0)
                       #u
                       (let ((d (nr-demand-step c (array-ref starts si)
                                                (after (array-ref succ si) 0) raw)))
                         (begin
                           (if (= d (array-ref before si))
                               #u
                               (begin (array-set! before si d) (set nr-changed #t)))
                           (pass (- si 1)))))))
               (fix (subr da-assembles () unit)
                 (lambda ()
                   (begin (set nr-changed #f)
                          (pass (- ns 1))
                          (if (get nr-changed) (fix) #u)))))
        (begin (fix) (product (1 before) (2 succ)))))))

;; Register `r`'s demands joined over the successors `ts`.
(define nr-demand-after (subr da-reads (da-ints da-bytes int) int)
  (lambda (before ts r)
    (letrec ((go (subr da-reads (da-bytes int) int)
               (lambda (ts acc)
                 (if (null? ts)
                     acc
                     (go (cdr ts) (nr-djoin1 acc (nr-rep (array-ref before (car ts)) r)))))))
      (go ts nr-d-none))))

;; Which instructions are a `flatarray-ref` (or `f64` `blobref-get`) whose
;; element only `f64` operations use, or a call (not in tail position)
;; whose value only they use (`raw_refs`).
(define nr-raw-refs (subr da-assembles (nr-cells da-ints da-bools) da-bools)
  (lambda (c starts raw)
    (let* ((ds (nr-demands c starts raw))
           (ns (array-length starts))
           (out (the da-bools (make-array ns #f))))
      (letrec ((go (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (let* ((i (array-ref starts si)) (op (nr-cell c i)))
                         (begin
                           (array-set! out si
                                       (and (or (nr-is-flat-ref? c i) (= op rop-invoke)
                                                (= op rop-invokeself))
                                            (= (nr-demand-after (extract ds 1)
                                                                (array-ref (extract ds 2) si) 0)
                                               nr-d-f64)))
                           (go (+ si 1))))))))
        (begin (go 0) out)))))

;; The parameters (REG1…REG8, bit 0 for REG1) a procedure takes raw
;; (`raw_params`): those only `f64` operations use, so `f64`s by the
;; program's types; a call's operand counting for neither. None of a
;; variadic procedure's, or one whose first instruction is not `args`.
(define nr-raw-params (subr da-assembles (nr-cells da-ints da-bools) int)
  (lambda (c starts raw)
    (if (or (= (array-length starts) 0) (not (= (nr-cell c (array-ref starts 0)) rop-args)))
        0
        (let* ((ds (nr-demands c starts raw))
               (ts (array-ref (extract ds 2) 0))
               (n (nr-k c (array-ref starts 0) 0)))
          (letrec ((all-f64? (subr da-reads (da-bytes int) bool)
                     (lambda (l r)
                       (or (null? l)
                           (and (= (nr-rep (array-ref (extract ds 1) (car l)) r) nr-d-f64)
                                (all-f64? (cdr l) r)))))
                   (go (subr da-reads (int int) int)
                     (lambda (r m)
                       (if (or (> r n) (> r 8))
                           m
                           (go (+ r 1)
                               (if (and (not (null? ts)) (all-f64? ts r))
                                   (+ m (arithmetic-shift 1 (- r 1)))
                                   m))))))
            (go 1 0))))))

;; Which registers each instruction's value is used from, as it starts: a
;; mask, bit `r` for register `r` (`live_in`).
(define nr-live-in (subr da-assembles (nr-cells da-ints da-bools) da-ints)
  (lambda (c starts raw)
    (let* ((before (extract (nr-demands c starts raw) 1))
           (ns (array-length starts))
           (out (the da-ints (make-array ns 0))))
      (letrec ((mask (subr da-reads (int int int) int)
                 (lambda (d r m)
                   (if (= r 9)
                       m
                       (mask d (+ r 1)
                             (if (= (nr-rep d r) nr-d-none) m (+ m (arithmetic-shift 1 r)))))))
               (go (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (begin (array-set! out si (mask (array-ref before si) 0 0))
                              (go (+ si 1)))))))
        (begin (go 0) out)))))

;;; ------------------------------------------------------------ step

;; `step`'s conversions so far, newest first, and the representations.
(define nr-first (ref da-bytes @k) (new nil))
(define nr-cur (ref int @k) (new 0))
(define nr-convert (subr pure (int int int) int)
  (lambda (kind r rep) (+ (* 128 kind) (+ (* 8 r) rep))))
(define nr-push (subr da-assembles (int) unit)
  (lambda (cv) (set nr-first (cons cv (get nr-first)))))
(define nr-set (subr da-assembles (int int) unit)
  (lambda (r rep) (set nr-cur (nr-with (get nr-cur) r rep))))
(define nr-get (subr da-reads (int) int) (lambda (r) (nr-rep (get nr-cur) r)))

;; Register `r` as `want`, converted first as that needs (`need`): a known
;; fixnum is a value already, and stays known.
(define nr-need (subr da-assembles (int int) unit)
  (lambda (r want)
    (let ((have (nr-get r)))
      (if (and (= have nr-fix) (= want nr-value))
          #u
          (begin
            (cond ((and (nr-raw? have) (= want nr-value)) (nr-push (nr-convert 0 r have)))
                  ((and (or (= have nr-value) (= have nr-fix)) (nr-raw? want))
                   (nr-push (nr-convert 1 r want)))
                  ((and (= have nr-value) (= want nr-fix)) (nr-push (nr-convert 2 r 0)))
                  ((and (nr-raw? have) (= want nr-fix))
                   (begin (nr-push (nr-convert 0 r have)) (nr-push (nr-convert 2 r 0))))
                  (else #u))
            (if (= have nr-undefined) #u (nr-set r want)))))))
;; REG1…REGn (eight at most) as `want-of` says of each, but `skip`.
(define nr-need-regs (subr da-assembles (int int (subr pure (int) int)) unit)
  (lambda (n skip want-of)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r)
                 (if (or (> r n) (> r 8))
                     #u
                     (begin (if (= r skip) #u (nr-need r (want-of r))) (go (+ r 1)))))))
      (go 1))))
(define nr-set-regs (subr da-assembles (int (subr pure (int) int)) unit)
  (lambda (n rep-of)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r)
                 (if (or (> r n) (> r 8)) #u (begin (nr-set r (rep-of r)) (go (+ r 1)))))))
      (go 1))))

;; The calls and call-outs (`step`'s): their operands values (or as a
;; callee known here takes them); the registers then undefined, `RESULT`
;; the value, raw for a call whose value only `f64` operations use.
(define nr-step-call (subr da-assembles (nr-cells int bool int int) unit)
  (lambda (c i raw-ref own callee)
    (let* ((op (nr-cell c i))
           (out? (or (= op rop-prim) (= op rop-lambda) (= op rop-cellular)))
           (n (if out? (nr-k c i 1) (nr-k c i 0)))
           (raw-call? (and raw-ref (or (= op rop-invoke) (= op rop-invokeself))))
           (keep (and (= op rop-prim) (string=? (nr-prim c i) "%fx26-flatarray-set!")
                      (= (nr-get 3) nr-f64)))
           (takes (cond ((= op rop-invokeself) own)
                        ((or (= op rop-invoke) (= op rop-tailinvoke)) callee)
                        (else 0))))
      (begin
        (if (or (= op rop-invoke) (= op rop-tailinvoke)) (nr-need 0 nr-value) #u)
        (nr-need-regs n (if keep 3 -1)
                      (lambda (r) (if (nr-raw-param? takes r) nr-f64 nr-value)))
        (set nr-cur 0)
        (nr-set 0 (if raw-call? nr-f64 nr-value))))))

;; The primitives of one and two: their raw shape (`raw_op`), a flat
;; array's element raw where only `f64` operations use it.
(define nr-step-prim (subr da-assembles (nr-cells int bool) unit)
  (lambda (c i raw-ref)
    (let* ((op (nr-cell c i))
           (rop (nr-raw-op (nr-prim c i)))
           (shape (if (= (extract rop 1) 0) (nr-all nr-value) (nr-raw-shape rop))))
      (begin
        (nr-need 0 (nr-rep shape 0))
        (if (= op rop-prim2) (nr-need (nr-k c i 1) (nr-rep shape 1)) #u)
        (nr-set 0 (if (and raw-ref (nr-is-flat-ref? c i)) nr-f64 (nr-rep shape 2)))))))

;; How a slot's value is held where it is read or written.
(define nr-slot-rep (subr da-reads (da-bools int) int)
  (lambda (raw n) (if (nr-raw-slot? raw n) nr-f64 nr-value)))

;; Instruction `i` on `reps`: the conversions it needs first, and `reps`
;; after it (`step`). `raw-ref`: whether a `flatarray-ref` (or `f64`
;; `blobref-get`) here gives its element raw; `fast`: in a procedure's
;; fixnum version; `own` and `callee`: the parameters this procedure and
;; a callee known here take raw.
(define nr-step (subr da-assembles (nr-cells int bool bool da-bools int int int) nr-stepped)
  (lambda (c i raw-ref fast raw own callee reps)
    (let* ((op (nr-cell c i))
           (k0 (nr-k c i 0)))
      (begin
        (set nr-first nil)
        (set nr-cur reps)
        (cond
          ((= op rop-args) (nr-set-regs k0 (lambda (r) (if (nr-raw-param? own r) nr-f64 nr-value))))
          ((= op rop-vargs) (nr-set-regs 8 (lambda (r) nr-value)))
          ((and (= op rop-const) fast (array-ref (extract c 2) (+ i 1))) (nr-set 0 nr-fix))
          ((= op rop-stack) (nr-set 0 (nr-slot-rep raw k0)))
          ((or (= op rop-const) (= op rop-global) (= op rop-lexical)) (nr-set 0 nr-value))
          ((= op rop-reg) (nr-set 0 (if (= k0 0) nr-value (nr-get k0))))
          ((= op rop-setreg) (nr-set k0 (nr-get 0)))
          ((= op rop-movereg) (nr-set (nr-k c i 1) (if (= k0 0) nr-value (nr-get k0))))
          ((= op rop-load) (nr-set k0 (nr-slot-rep raw (nr-k c i 1))))
          ((= op rop-store) (nr-need k0 (nr-slot-rep raw (nr-k c i 1))))
          ;; In a fixnum version, `int`'s operations: operands known (tested
          ;; first where they are not), a sum or difference one too.
          ((and (or (= op rop-op2) (= op rop-op2imm)) fast (nr-int-routine? k0))
           (begin
             (nr-need 0 nr-fix)
             (if (= op rop-op2) (nr-need (nr-k c i 1) nr-fix) #u)
             (nr-set 0 (if (or (= k0 routine-int-add) (= k0 routine-int-sub)) nr-fix nr-value))))
          ((or (= op rop-op1) (= op rop-op2imm) (= op rop-field))
           (begin (nr-need 0 nr-value) (nr-set 0 nr-value)))
          ((or (= op rop-op2) (= op rop-setfield))
           (begin (nr-need 0 nr-value) (nr-need (nr-k c i 1) nr-value) (nr-set 0 nr-value)))
          ((= op rop-setstk) (nr-need 0 (nr-slot-rep raw k0)))
          ;; An `f64` returned raw, where the caller takes it so.
          ((and (= op rop-return) (= (nr-get 0) nr-f64)) #u)
          ((or (= op rop-setglbl) (= op rop-return) (= op rop-branchf) (= op rop-brancht))
           (nr-need 0 nr-value))
          ((or (= op rop-prim1) (= op rop-prim2) (= op rop-prim2imm)) (nr-step-prim c i raw-ref))
          ((= op rop-prim3imm)
           (begin
             (nr-need 0 nr-value)
             (if (and (nr-is-f64-set? c i) (= (nr-get (nr-k c i 2)) nr-f64))
                 #u
                 (nr-need (nr-k c i 2) nr-value))
             (nr-set 0 nr-value)))
          ((or (= op rop-prim) (= op rop-lambda) (= op rop-cellular) (= op rop-invoke)
               (= op rop-tailinvoke) (= op rop-invokeself))
           (nr-step-call c i raw-ref own callee))
          ((or (= op rop-branch) (= op rop-global-guard) (= op rop-save) (= op rop-pop)) #u)
          ;; Any other: every register a value, to be safe.
          (else (begin (nr-need 0 nr-value) (nr-need-regs 8 -1 (lambda (r) nr-value)))))
        (product (1 (the da-bytes (reverse (get nr-first)))) (2 (get nr-cur)))))))

;; Each instruction's registers where it starts, and where it ends, from
;; the fixpoint of `nr-step` and `nr-join` (`reps_of`). `callees`: by
;; instruction, what a callee known there takes raw.
(define nr-reps-of
  (subr da-assembles (nr-cells da-ints bool da-bools int da-ints) nr-in-out)
  (lambda (c starts fast raw own callees)
    (let* ((refs (nr-raw-refs c starts raw))
           (ns (array-length starts))
           (succ (nr-successors c starts))
           (ins (the da-ints (make-array ns -1)))
           (outs (the da-ints (make-array ns 0))))
      (letrec ((spread (subr da-assembles (da-bytes int) unit)
                 (lambda (ts reps)
                   (if (null? ts)
                       #u
                       (let* ((t (car ts)) (old (array-ref ins t))
                              (new (if (< old 0) reps (nr-join old reps))))
                         (begin
                           (if (= old new) #u (begin (array-set! ins t new) (set nr-changed #t)))
                           (spread (cdr ts) reps))))))
               (pass (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (begin
                         (if (< (array-ref ins si) 0)
                             #u
                             (let* ((i (array-ref starts si))
                                    (callee (array-ref callees si))
                                    (stepped (nr-step c i (array-ref refs si) fast raw own callee
                                                      (array-ref ins si)))
                                    (out (extract stepped 2)))
                               (begin (array-set! outs si out) (spread (array-ref succ si) out))))
                         (pass (+ si 1))))))
               (fix (subr da-assembles () unit)
                 (lambda ()
                   (begin (set nr-changed #f) (pass 0) (if (get nr-changed) (fix) #u))))
               (defined (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (begin (if (< (array-ref ins si) 0) (array-set! ins si 0) #u)
                              (defined (+ si 1)))))))
        (begin
          (if (> ns 0) (array-set! ins 0 0) #u)
          (fix)
          (defined 0)
          (product (1 ins) (2 outs)))))))

;;; ------------------------------------------------------------ slots

;; Instruction `si`'s frame slot access (`webs`'s `access`): the slot (-1
;; for none), whether a read, and its register.
(define nr-access (subr da-reads (nr-cells da-ints int) (productof (1 int) (2 bool) (3 int)))
  (lambda (c starts si)
    (let* ((i (array-ref starts si)) (op (nr-cell c i)) (k0 (nr-k c i 0)))
      (cond ((= op rop-stack) (product (1 k0) (2 #t) (3 0)))
            ((= op rop-load) (product (1 (nr-k c i 1)) (2 #t) (3 k0)))
            ((= op rop-setstk) (product (1 k0) (2 #f) (3 0)))
            ((= op rop-store) (product (1 (nr-k c i 1)) (2 #f) (3 k0)))
            (else (product (1 -1) (2 #f) (3 0)))))))

;; The union-find's representative of `x`, the way there shortened.
(define nr-find (subr da-assembles (da-ints int) int)
  (lambda (parent x)
    (letrec ((root (subr da-reads (int) int)
               (lambda (r) (if (= (array-ref parent r) r) r (root (array-ref parent r)))))
             (shorten (subr da-assembles (int int) unit)
               (lambda (y r)
                 (if (= (array-ref parent y) r)
                     #u
                     (let ((next (array-ref parent y)))
                       (begin (array-set! parent y r) (shorten next r)))))))
      (let ((r (root x))) (begin (shorten x r) r)))))

;; The webs of the procedure's `slots` frame slots (`webs`): register code
;; may use a slot for one variable, then another, so a slot is taken apart
;; into webs, its writes and reads joined where a write reaches a read. A
;; web is an `f64`'s where one of its reads is used by an `f64` operation,
;; or one of its writes stores what an `f64` operation made, each as if no
;; slot were raw. By instruction: its slot (-1 for none) and its web (an
;; instruction standing for it); by web, whether an `f64`'s, and whether
;; read.
(define nr-new-webs (subr da-assembles (int) nr-webs)
  (lambda (ns)
    (let ((slot (the da-ints (make-array ns -1))) (web (the da-ints (make-array ns 0))))
      (product (1 slot) (2 web)
               (3 (the da-bools (make-array ns #f))) (4 (the da-bools (make-array ns #f)))))))
(define nr-webs (subr da-assembles (nr-cells da-ints int) nr-webs)
  (lambda (c starts slots)
    (let* ((ns (array-length starts))
           (none (the da-bools (make-array slots #f)))
           (ds (nr-demands c starts none))
           (ins (extract (nr-reps-of c starts #f none 0 (the da-ints (make-array ns 0))) 1))
           (preds (nr-preds (extract ds 2)))
           (parent (the da-ints (make-array ns 0)))
           (w (nr-new-webs ns)))
      (letrec ((each (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (begin (array-set! parent si si) (each (+ si 1))))))
               (join (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (let ((a (nr-access c starts si)))
                         (begin
                           (if (and (>= (extract a 1) 0) (extract a 2))
                               (nr-search c starts preds parent (the da-bools (make-array ns #f))
                                          (array-ref preds si) (extract a 1) si)
                               #u)
                           (join (+ si 1)))))))
               (show (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (begin (nr-show c starts ds ins parent w si) (show (+ si 1)))))))
        (begin (each 0) (join 0) (show 0) (nr-name-webs parent w 0) w)))))

;; Each instruction's predecessors.
(define nr-preds (subr da-assembles ((arrayof da-bytes @k)) (arrayof da-bytes @k))
  (lambda (succ)
    (let* ((ns (array-length succ)) (preds (the (arrayof da-bytes @k) (make-array ns nil))))
      (letrec ((add (subr da-assembles (int da-bytes) unit)
                 (lambda (si ts)
                   (if (null? ts)
                       #u
                       (begin (array-set! preds (car ts) (cons si (array-ref preds (car ts))))
                              (add si (cdr ts))))))
               (go (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns) #u (begin (add si (array-ref succ si)) (go (+ si 1)))))))
        (begin (go 0) preds)))))

;; The writes of `slot` that reach the read at `si`: back from it, each
;; joined to its web; past any other instruction, on back.
(define nr-search
  (subr da-assembles (nr-cells da-ints (arrayof da-bytes @k) da-ints da-bools da-bytes int int)
        unit)
  (lambda (c starts preds parent seen work slot si)
    (if (null? work)
        #u
        (let ((p (car work)))
          (if (array-ref seen p)
              (nr-search c starts preds parent seen (cdr work) slot si)
              (let ((a (nr-access c starts p)))
                (begin
                  (array-set! seen p #t)
                  (if (and (= (extract a 1) slot) (not (extract a 2)))
                      (let* ((x (nr-find parent p)) (y (nr-find parent si)))
                        (begin
                          (array-set! parent x y)
                          (nr-search c starts preds parent seen (cdr work) slot si)))
                      (nr-search c starts preds parent seen
                                 (append (array-ref preds p) (cdr work)) slot si)))))))))

;; What instruction `si` shows of its web, and its web and slot named.
(define nr-show
  (subr da-assembles
        (nr-cells da-ints (productof (1 da-ints) (2 (arrayof da-bytes @k))) da-ints da-ints
                  nr-webs int)
        unit)
  (lambda (c starts ds ins parent w si)
    (let ((a (nr-access c starts si)))
      (if (< (extract a 1) 0)
          #u
          (let ((web (nr-find parent si)) (reg (extract a 3)))
            (begin
              (if (extract a 2)
                  (let ((after (nr-demand-after (extract ds 1) (array-ref (extract ds 2) si) reg)))
                    (begin
                      (if (or (= after nr-d-f64) (= after nr-d-both))
                          (array-set! (extract w 3) web #t)
                          #u)
                      (if (= after nr-d-none) #u (array-set! (extract w 4) web #t))))
                  (if (= (nr-rep (array-ref ins si) reg) nr-f64)
                      (array-set! (extract w 3) web #t)
                      #u))
              (array-set! (extract w 1) si (extract a 1))))))))

;; The webs' names, by instruction, once every web is joined.
(define nr-name-webs (subr da-assembles (da-ints nr-webs int) unit)
  (lambda (parent w si)
    (if (= si (array-length parent))
        #u
        (begin
          (array-set! (extract w 2) si (nr-find parent si))
          (nr-name-webs parent w (+ si 1))))))

;; Which of the procedure's `slots` frame slots hold a raw `f64`
;; (`raw_slots`): a slot is raw if every web of it is an `f64`'s, or never
;; read. A slot that holds an `f64` and something else in turn is first
;; split (`nr-split-slots`).
(define nr-raw-slots (subr da-assembles (nr-cells da-ints int) da-bools)
  (lambda (c starts slots)
    (let* ((w (nr-webs c starts slots))
           (ns (array-length starts))
           (raw (the da-bools (make-array slots #t))))
      (letrec ((go (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (let ((slot (array-ref (extract w 1) si)) (web (array-ref (extract w 2) si)))
                         (begin
                           (if (and (>= slot 0) (< slot slots) (array-ref (extract w 4) web)
                                    (not (array-ref (extract w 3) web)))
                               (array-set! raw slot #f)
                               #u)
                           (go (+ si 1))))))))
        (begin (go 0) raw)))))

;; The frames' sizes, by `save` and `pop`, in order: those of instructions
;; `si` and before (from the last, -1 for none) before `acc`.
(define nr-frames-to (subr da-assembles (nr-cells da-ints int da-bytes) da-bytes)
  (lambda (c starts si acc)
    (if (< si 0)
        acc
        (let* ((i (array-ref starts si)) (op (nr-cell c i)))
          (nr-frames-to c starts (- si 1)
                        (if (or (= op rop-save) (= op rop-pop)) (cons (nr-k c i 0) acc) acc))))))
(define nr-frames (subr da-assembles (nr-cells da-ints int) da-bytes)
  (lambda (c starts si) (nr-frames-to c starts (- (array-length starts) 1) nil)))
(define nr-all-are? (subr da-reads (da-bytes int) bool)
  (lambda (l m) (or (null? l) (and (= (car l) m) (nr-all-are? (cdr l) m)))))

;; Each mixed slot's new place (`moved`), the next past them, from `slot`
;; on: how many slots then.
(define nr-place (subr da-assembles (da-bools da-bools da-ints int int) int)
  (lambda (f64s others moved slot next)
    (cond ((= slot (array-length moved)) next)
          ((and (array-ref f64s slot) (array-ref others slot))
           (begin (array-set! moved slot next) (nr-place f64s others moved (+ slot 1) (+ next 1))))
          (else (nr-place f64s others moved (+ slot 1) next)))))

;; Which slots under `m` hold an `f64` web, and which another web read.
(define nr-mark (subr da-assembles (nr-webs int da-bools da-bools int) unit)
  (lambda (w m f64s others si)
    (if (= si (array-length (extract w 1)))
        #u
        (let ((slot (array-ref (extract w 1) si)) (web (array-ref (extract w 2) si)))
          (begin
            (cond ((or (< slot 0) (>= slot m)) #u)
                  ((array-ref (extract w 3) web) (array-set! f64s slot #t))
                  ((array-ref (extract w 4) web) (array-set! others slot #t))
                  (else #u))
            (nr-mark w m f64s others (+ si 1)))))))

;; `cells` with each frame slot that holds an `f64` and, in turn,
;; something else split in two (`split_slots`): its `f64` webs moved to a
;; slot of their own, past the frame's others, which `nr-raw-slots` then
;; keeps raw; the frame (`save`, `pop`) that much larger. The same cells
;; if nothing is split, or the frame would pass 64 slots.
(define nr-split-slots (subr da-assembles (nr-cells) nr-cells)
  (lambda (c)
    (let* ((starts (nr-starts c)) (frames (nr-frames c starts 0)))
      (if (or (null? frames) (not (nr-all-are? frames (car frames))))
          c
          (let* ((m (car frames))
                 (w (nr-webs c starts m))
                 (f64s (the da-bools (make-array m #f)))
                 (others (the da-bools (make-array m #f)))
                 (moved (the da-ints (make-array m -1))))
            (begin
              (nr-mark w m f64s others 0)
              (let ((next (nr-place f64s others moved 0 m)))
                (if (or (= next m) (> next 64)) c (nr-moved c starts w moved next)))))))))

;; `split_slots`'s rewrite: the frame `next` slots, and each `f64` web of a
;; slot `moved` in its new slot (the first operand of `stack` and
;; `setstk`, the second of `load` and `store`).
(define nr-moved (subr da-assembles (nr-cells da-ints nr-webs da-ints int) nr-cells)
  (lambda (c starts w moved next)
    (let* ((n (nr-ncells c))
           (ns (array-length starts))
           (out (the da-ints (make-array n 0))))
      (letrec ((copy (subr da-assembles (int) unit)
                 (lambda (i)
                   (if (= i n) #u (begin (array-set! out i (nr-cell c i)) (copy (+ i 1))))))
               (go (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (begin (nr-move c starts w moved next out si) (go (+ si 1)))))))
        (begin (copy 0) (go 0) (product (1 out) (2 (extract c 2))))))))
(define nr-move (subr da-assembles (nr-cells da-ints nr-webs da-ints int da-ints int) unit)
  (lambda (c starts w moved next out si)
    (let* ((i (array-ref starts si)) (op (nr-cell c i))
           (slot (array-ref (extract w 1) si))
           (web (array-ref (extract w 2) si)))
      (cond ((or (= op rop-save) (= op rop-pop)) (array-set! out (+ i 1) next))
            ((and (>= slot 0) (< slot (array-length moved))
                  (array-ref (extract w 3) web) (>= (array-ref moved slot) 0))
             (array-set! out (if (or (= op rop-load) (= op rop-store)) (+ i 2) (+ i 1))
                         (array-ref moved slot)))
            (else #u)))))
)))
