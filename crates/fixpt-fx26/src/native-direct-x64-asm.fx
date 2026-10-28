;;; The assembler of the native convention's compiler to x86_64 written in
;;; FX-26, and the machine sequences its files share: `direct/x64.rs`'s
;;; `Asm` and its free functions of no procedure, step for step, over the
;;; encoder written in FX-26 (`x86_64.fx`) and what the convention's
;;; generator says of it (`native-direct-x64-layout.fx`). Its steps have
;;; the Rust names, with `da-` before them (`da-push-frame-ret` is
;;; `push_frame_ret`).
;;;
;;; Besides `Asm`'s bytes and labels it keeps what the Rust compiler keeps
;;; beside them as it compiles a procedure: the call-outs it numbers (from
;;; the machine's count, `da-reset`), the traps to place after the code
;;; (`stubs`), and the first reason it cannot compile ("" for none).
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder and the layout.

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (layout-types (load-module "fx26:native-direct-x64-layout-types.fx"))
       (x86-64-types (load-module "fx26:x86_64-types.fx")))
  (lambda ((x86 (select x86-64-types x86-64-sig))
           (dl (select layout-types native-direct-x64-layout-sig)))
    (module
(hide (include direct-types))
(hide (include x86) (include dl))

;; Conditions, operations and shifts, by the hardware's numbers.
(define da-c-o int 0)
(define da-c-b int 2)
(define da-c-ae int 3)
(define da-c-e int 4)
(define da-c-ne int 5)
(define da-c-be int 6)
(define da-c-a int 7)
(define da-c-s int 8)
(define da-c-ns int 9)
(define da-c-p int 10)
(define da-c-l int 12)
(define da-c-ge int 13)
(define da-c-le int 14)
(define da-c-g int 15)
(define da-add int 0)
(define da-or int 1)
(define da-and int 4)
(define da-sub int 5)
(define da-xor int 6)
(define da-cmp int 7)
(define da-shl int 4)
(define da-shr int 5)
(define da-sar int 7)

;; 64 bits read as signed.
(define da-signed (subr pure (int) int)
  (lambda (b) (if (>= b 9223372036854775808) (- b 18446744073709551616) b)))

;;; ------------------------------------------------------------ the assembler
;;; Bytes, and labels patched when everything is placed: a label is where
;;; it is, in bytes from the start, -1 until placed.

(define da-code (ref da-ints @k) (new (make-array 16384 0)))
(define da-len (ref int @k) (new 0))
(define da-labels (ref da-ints @k) (new (make-array 1024 -1)))
(define da-nlabels (ref int @k) (new 0))
;; Each displacement to patch: where it is, and its label; newest first.
(define da-fixups (ref da-pairs @k) (new nil))
;; Where the last instruction starts, if it is a jump to a label; else -1.
(define da-last-jump (ref int @k) (new -1))
;; The call-outs numbered, newest first, from `da-base`; the traps to place,
;; newest first (label, code); and why not, if not.
(define da-base (ref int @k) (new 0))
(define da-made (ref da-bytes @k) (new nil))
(define da-nmade (ref int @k) (new 0))
(define da-stubs (ref da-pairs @k) (new nil))
(define da-why (ref string @k) (new ""))
;; Each load of a call-out's number from its field (`da-call-out`), newest
;; first: where it is, and the call-out's number, its field not yet given.
(define da-callout-loads (ref da-pairs @k) (new nil))

(define da-copy-ints (subr da-assembles (da-ints da-ints int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (da-copy-ints from to (+ i 1))))))

;; A procedure begins, its call-outs numbered from `base`.
(define da-reset (subr da-assembles (int) unit)
  (lambda (base)
    (begin
      (set da-len 0)
      (set da-nlabels 0)
      (set da-fixups nil)
      (set da-last-jump -1)
      (set da-base base)
      (set da-made nil)
      (set da-nmade 0)
      (set da-stubs nil)
      (set da-callout-loads nil)
      (set da-why ""))))

(define da-here (subr da-reads () int) (lambda () (get da-len)))

(define da-byte (subr da-assembles (int) unit)
  (lambda (b)
    (let ((n (get da-len)))
      (begin
        (if (= n (array-length (get da-code)))
            (let ((bigger (the da-ints (make-array (* 2 n) 0))))
              (begin (da-copy-ints (get da-code) bigger 0) (set da-code bigger)))
            #u)
        (array-set! (get da-code) n b)
        (set da-len (+ n 1))))))
(define da-bytes-in (subr da-assembles (da-bytes) unit)
  (lambda (bs) (if (null? bs) #u (begin (da-byte (car bs)) (da-bytes-in (cdr bs))))))
;; An instruction, or bytes.
(define da-e (subr da-assembles (da-bytes) unit)
  (lambda (bs) (begin (da-bytes-in bs) (set da-last-jump -1))))

(define da-label (subr da-assembles () int)
  (lambda ()
    (let ((n (get da-nlabels)))
      (begin
        (if (= n (array-length (get da-labels)))
            (let ((more (the da-ints (make-array (* 2 n) -1))))
              (begin (da-copy-ints (get da-labels) more 0) (set da-labels more)))
            #u)
        (array-set! (get da-labels) n -1)
        (set da-nlabels (+ n 1))
        n))))

;; Whether the newest fixup is the jump just before here, to `l`.
(define da-jump-to-here? (subr da-reads (int) bool)
  (lambda (l)
    (let ((fs (get da-fixups)) (at (get da-last-jump)))
      (and (>= at 0)
           (not (null? fs))
           (= (extract (car fs) 1) (+ at 1))
           (= (extract (car fs) 2) l)))))
;; Label `l` here; a jump to it just before it goes.
;; Where label `l` is in the code, or -1 if it was never placed.
(define da-label-offset (subr da-reads (int) int)
  (lambda (l) (array-ref (get da-labels) l)))
(define da-bind (subr da-assembles (int) unit)
  (lambda (l)
    (begin
      (if (da-jump-to-here? l)
          (begin (set da-fixups (cdr (get da-fixups))) (set da-len (get da-last-jump)))
          #u)
      (set da-last-jump -1)
      (array-set! (get da-labels) l (get da-len)))))

;; Which labels a branch so far goes to, each `#t`.
(define da-targets (subr da-assembles () da-bools)
  (lambda ()
    (let ((to (the da-bools (make-array (+ 1 (get da-nlabels)) #f))))
      (letrec ((mark (subr da-assembles (da-pairs) unit)
                 (lambda (fs)
                   (if (null? fs)
                       #u
                       (begin (array-set! to (extract (car fs) 2) #t) (mark (cdr fs)))))))
        (begin (mark (get da-fixups)) to)))))
;; Whether a branch so far goes to `l`.
(define da-used-in? (subr da-reads (da-pairs int) bool)
  (lambda (fs l)
    (cond ((null? fs) #f)
          ((= (extract (car fs) 2) l) #t)
          (else (da-used-in? (cdr fs) l)))))
(define da-used? (subr da-reads (int) bool) (lambda (l) (da-used-in? (get da-fixups) l)))

;; `bs`, whose last four bytes are a displacement to `l`.
(define da-to (subr da-assembles (int da-bytes) unit)
  (lambda (l bs)
    (begin
      (da-e bs)
      (set da-fixups (cons (product (1 (- (get da-len) 4)) (2 l)) (get da-fixups))))))
(define da-jmp (subr da-assembles (int) unit)
  (lambda (l)
    (let ((at (get da-len)))
      (begin (da-to l (x86-jmp 0)) (set da-last-jump at)))))
(define da-jcc (subr da-assembles (int int) unit) (lambda (c l) (da-to l (x86-jcc c 0))))
(define da-call-l (subr da-assembles (int) unit) (lambda (l) (da-to l (x86-call 0))))
;; `r` := where `l` is.
(define da-lea-l (subr da-assembles (int int) unit) (lambda (r l) (da-to l (x86-lea-rip r 0))))
;; `t` := field `k` of the code bloblet being made, by its distance: field
;; `k` is `8k` bytes before the code's first.
(define da-field (subr da-assembles (int int) unit)
  (lambda (t k) (da-e (x86-load-rip t (- (- 0 (* 8 k)) (+ (get da-len) 7))))))
;; `r` := the constant `v`, its bits (or the signed integer they are), in
;; as few bytes as do it.
(define da-imm (subr da-assembles (int int) unit)
  (lambda (r v) (da-e (x86-mov-imm r (da-signed v)))))
;; Compare `r` with the constant `v`, its bits (`X16` may be used for it).
(define da-cmp-k (subr da-assembles (int int) unit)
  (lambda (r v)
    (let ((k (da-signed v)))
      (if (and (>= k -2147483648) (< k 2147483648))
          (da-e (x86-alu-imm da-cmp r k))
          (begin (da-imm d-x16 v) (da-e (x86-alu da-cmp r d-x16)))))))
;; `RESULT` := `#t` where `c` holds after the comparison just made, else
;; `#f` (uses `t`).
(define da-flag (subr da-assembles (int int) unit)
  (lambda (c t)
    (begin (da-imm t d-true) (da-imm d-result d-false) (da-e (x86-cmov c d-result t)))))

;; `REGk`'s register (-1 for none: it is in the state), and its place in
;; the state.
(define da-in-reg (subr pure (int) int)
  (lambda (k) (case k ((0) d-result) ((1) d-rdi) ((2) d-rsi) ((3) d-r8) (else -1))))
(define da-reg-off (subr pure (int) int) (lambda (k) (+ d-st-regs (* 8 k))))
(define da-ld (subr da-assembles (int int int) unit)
  (lambda (d base disp) (da-e (x86-load d base disp))))
(define da-sto (subr da-assembles (int int int) unit)
  (lambda (base disp s) (da-e (x86-store base disp s))))
(define da-mov (subr da-assembles (int int) unit) (lambda (d s) (da-e (x86-mov d s))))
;; `REGk` in a register: its own, or `tmp`, loaded.
(define da-get (subr da-assembles (int int) int)
  (lambda (k tmp)
    (let ((r (da-in-reg k)))
      (if (>= r 0) r (begin (da-ld tmp d-st (da-reg-off k)) tmp)))))
;; `REGk` := `src`.
(define da-put (subr da-assembles (int int) unit)
  (lambda (k src)
    (let ((r (da-in-reg k)))
      (cond ((= r src) #u)
            ((>= r 0) (da-mov r src))
            (else (da-sto d-st (da-reg-off k) src))))))
;; `[base + disp]` := `REGk` (uses `tmp` for one in the state).
(define da-store-reg (subr da-assembles (int int int int) unit)
  (lambda (base disp k tmp) (da-sto base disp (da-get k tmp))))
;; `REGk` := `[base + disp]` (uses `tmp` for one in the state).
(define da-load-reg (subr da-assembles (int int int int) unit)
  (lambda (k base disp tmp)
    (let ((r (da-in-reg k)))
      (if (>= r 0)
          (da-ld r base disp)
          (begin (da-ld tmp base disp) (da-sto d-st (da-reg-off k) tmp))))))
;; Where the state's `args` keeps argument `j`.
(define da-arg-off (subr pure (int) int) (lambda (j) (+ d-st-args (* 8 j))))
;; REG1…REGn into the state's `args` (uses `X11`).
(define da-regs-to-args (subr da-assembles (int) unit)
  (lambda (n)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (j)
                 (if (= j n)
                     #u
                     (begin (da-store-reg d-st (da-arg-off j) (+ 1 j) d-x11) (go (+ j 1)))))))
      (go 0))))

;; The byte at `i`.
(define da-byte-at (subr da-reads (int) int) (lambda (i) (array-ref (get da-code) i)))
;; The four bytes of `v` at `at`, lowest first.
(define da-put4 (subr da-assembles (int int int) unit)
  (lambda (at v i)
    (if (= i 4)
        #u
        (begin (array-set! (get da-code) (+ at i) (modulo v 256))
               (da-put4 at (quotient v 256) (+ i 1))))))
;; The fixups, oldest first: a jump to a `ret` is that `ret` (a fast path
;; that joins the slow one only to return).
(define da-patch (subr da-assembles (da-pairs) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (let* ((at (extract (car fs) 1)) (to (array-ref (get da-labels) (extract (car fs) 2))))
          (begin
            (cond ((< to 0) (da-fail "a label never placed"))
                  ((and (= (da-byte-at (- at 1)) 233) (= (da-byte-at to) 195))
                   (begin (array-set! (get da-code) (- at 1) 195)
                          (da-put4 at 3435973836 0)))
                  (else (da-put4 at (modulo (- to (+ at 4)) 4294967296) 0)))
            (da-patch (cdr fs)))))))
(define da-list (subr da-assembles (int da-bytes) da-bytes)
  (lambda (i acc) (if (< i 0) acc (da-list (- i 1) (cons (array-ref (get da-code) i) acc)))))
(define da-finish (subr da-assembles () da-bytes)
  (lambda ()
    (begin
      (da-patch (the da-pairs (reverse (get da-fixups))))
      (set da-fixups nil)
      (da-list (- (get da-len) 1) nil))))

;; Where the assembler is, to come back to (`da-rewind`): code emitted
;; after it measured, then taken back, as `raw_entry_skip` measures code
;; in an assembler of its own. Its length, labels, fixups and last jump.
(define da-mark (subr da-reads () da-mark)
  (lambda ()
    (product (1 (get da-len)) (2 (get da-nlabels)) (3 (get da-fixups)) (4 (get da-last-jump)))))
(define da-rewind (subr da-assembles (da-mark) unit)
  (lambda (m)
    (begin
      (set da-len (extract m 1))
      (set da-nlabels (extract m 2))
      (set da-fixups (extract m 3))
      (set da-last-jump (extract m 4)))))

;; Why the procedure cannot be compiled: the first reason.
(define da-fail (subr da-assembles (string) unit)
  (lambda (m) (if (string=? (get da-why) "") (set da-why m) #u)))
(define da-err (subr da-reads () string) (lambda () (get da-why)))
(define da-ok? (subr da-reads () bool) (lambda () (string=? (get da-why) "")))

;; A call-out's code (`fx::callout_code`): of kind `kind` (`d-co-…`), its
;; operands `a` and `b`.
(define da-co (subr pure (int int int) int)
  (lambda (kind a b) (+ kind (* 32 (+ a (* 4096 b))))))
;; Call-out `code` numbered: its number.
(define da-callout (subr da-assembles (int) int)
  (lambda (code)
    (let ((n (+ (get da-base) (get da-nmade))))
      (begin (set da-made (cons code (get da-made))) (set da-nmade (+ 1 (get da-nmade))) n))))
;; Those numbered, oldest first.
(define da-callouts (subr da-assembles () da-bytes)
  (lambda () (the da-bytes (reverse (get da-made)))))

;; A trap of `code` at label `l`, placed after the code (`stubs`).
(define da-stub (subr da-assembles (int int) unit)
  (lambda (l code) (set da-stubs (cons (product (1 l) (2 code)) (get da-stubs)))))
;; To a trap of `code` where `c` holds (`procedure`'s `trap`).
(define da-trap (subr da-assembles (int int) unit)
  (lambda (code c) (let ((l (da-label))) (begin (da-stub l code) (da-jcc c l)))))

;; Whether a stub of `code` is among `ss`.
(define da-stub-of? (subr da-reads (da-pairs int) bool)
  (lambda (ss code)
    (cond ((null? ss) #f)
          ((= (extract (car ss) 2) code) #t)
          (else (da-stub-of? (cdr ss) code)))))
;; The traps, out of the way: a stub per site, calling its kind's stub,
;; which goes to the machine's common trap.
(define da-place-stubs (subr da-assembles () unit)
  (lambda ()
    (let ((kinds (the da-ints (make-array d-traps 0)))
          (ss (the da-pairs (reverse (get da-stubs)))))
      (letrec ((labels (subr da-assembles (int) unit)
                 (lambda (k)
                   (if (= k d-traps) #u (begin (array-set! kinds k (da-label)) (labels (+ k 1))))))
               (sites (subr da-assembles (da-pairs) unit)
                 (lambda (l)
                   (if (null? l)
                       #u
                       (begin (da-bind (extract (car l) 1))
                              (da-call-l (array-ref kinds (extract (car l) 2)))
                              (sites (cdr l))))))
               (kind (subr da-assembles (int) unit)
                 (lambda (k)
                   (if (= k d-traps)
                       #u
                       (begin
                         (if (da-stub-of? ss k)
                             (begin (da-bind (array-ref kinds k))
                                    (da-imm d-x9 k)
                                    (da-e (x86-jmp-m d-st -1 1 d-st-trap-stub)))
                             #u)
                         (kind (+ k 1)))))))
        (begin (labels 0) (sites ss) (kind 1))))))

;;; ------------------------------------------------------------ sequences

;; Back to Rust from anywhere on the native stack.
(define da-leave (subr da-assembles () unit)
  (lambda ()
    (begin
      (da-ld d-sp d-st d-st-rust-sp)
      (da-e (x86-alu-imm da-add d-sp 8))
      (da-e (x86-pop 15)) (da-e (x86-pop 14)) (da-e (x86-pop 13)) (da-e (x86-pop 12))
      (da-e (x86-pop 3))
      (da-e (x86-pop d-frame))
      (da-e (x86-ret)))))

;; Where a call-out that does not return to its caller said to go.
(define da-resume (subr da-assembles () unit)
  (lambda ()
    (begin
      (da-ld d-sp d-st d-st-resume-sp)
      (da-ld d-frame d-st d-st-resume-fp)
      (da-ld d-result d-st d-st-resume-x0)
      (da-e (x86-jmp-m d-st -1 1 d-st-resume-pc)))))

;; `RSI` := call-out `n`'s number (`callout_number`): one of a machine's
;; own as a constant; another from its field, a call-out, given when the
;; procedure is done (`dx-callout-fields`).
(define da-callout-number (subr da-assembles (int) unit)
  (lambda (n)
    (if (< n d-own-callouts)
        (da-imm d-rsi n)
        (begin (set da-callout-loads (cons (product (1 (get da-len)) (2 n)) (get da-callout-loads)))
               (da-e (x86-load-rip d-rsi 0))
               (da-e (x86-shift-imm da-shr d-rsi d-callout-shift))))))
;; The loads of call-outs' numbers, oldest first.
(define da-callout-loads-made (subr da-assembles () da-pairs)
  (lambda () (the da-pairs (reverse (get da-callout-loads)))))
;; The load at `at` given field `k`.
(define da-callout-field (subr da-assembles (int int) unit)
  (lambda (at k) (da-put4 (+ at 3) (modulo (- (- 0 (* 8 k)) (+ at 7)) 4294967296) 0)))
;; Call-out `n`, its arguments in the state already: on Rust's stack, with
;; where the native frames are for its collections to find.
(define da-call-out (subr da-assembles (int) unit)
  (lambda (n)
    (begin
      (da-sto d-st d-st-fp d-frame)
      (da-sto d-st d-st-native-sp d-sp)
      (da-ld d-sp d-st d-st-rust-sp)
      (da-mov d-rdi d-st)
      (da-callout-number n)
      (da-e (x86-call-m d-st d-st-callout))
      (da-ld d-sp d-st d-st-native-sp)
      (da-ld d-frame d-st d-st-fp))))

;; The state's trap tested after a call-out: to `failed` if one was set.
(define da-trapped (subr da-assembles (int) unit)
  (lambda (failed)
    (begin (da-e (x86-alu-mi da-cmp d-st d-st-trap 0)) (da-jcc da-c-ne failed))))
;; The same, to a trap of a primitive failed.
(define da-trap-set (subr da-assembles () unit)
  (lambda ()
    (begin (da-e (x86-alu-mi da-cmp d-st d-st-trap 0)) (da-trap d-prim-failed da-c-ne))))

;; The common trap's way from code with no stub of its own.
(define da-fail-here (subr da-assembles (int) unit)
  (lambda (code)
    (let ((stub (da-label)))
      (begin
        (da-call-l stub)
        (da-bind stub)
        (da-imm d-x9 code)
        (da-e (x86-jmp-m d-st -1 1 d-st-trap-stub))))))

;; `RESULT` and REG1…REG(n-1) into the state's `kept`, or back.
(define da-keep (subr da-assembles (int bool) unit)
  (lambda (n back)
    (letrec ((go (subr da-assembles (int) unit)
               (lambda (r)
                 (if (= r n)
                     #u
                     (begin
                       (if back
                           (da-load-reg r d-st (+ d-st-kept (* 8 r)) d-x11)
                           (da-store-reg d-st (+ d-st-kept (* 8 r)) r d-x11))
                       (go (+ r 1)))))))
      (go 0))))

;; A frame of `size` bytes pushed below the stack's top: its link and
;; `second` stored, `fp` at its link, its header word below.
(define da-push-frame (subr da-assembles (int int) unit)
  (lambda (second size)
    (begin
      (da-e (x86-alu-imm da-sub d-sp size))
      (da-sto d-sp 8 d-frame)
      (da-sto d-sp 16 second)
      (da-e (x86-lea d-frame d-sp 8)))))
;; Under the return address a `call` left on top, that address its second
;; word. Uses `X11`.
(define da-push-frame-ret (subr da-assembles (int) unit)
  (lambda (size) (begin (da-e (x86-pop d-x11)) (da-push-frame d-x11 size))))
;; The frame on top popped, `fp` its link again and its second word in
;; `X11`.
(define da-pop-frame (subr da-assembles (int) unit)
  (lambda (size)
    (begin (da-ld d-x11 d-sp 16) (da-ld d-frame d-sp 8) (da-e (x86-alu-imm da-add d-sp size)))))
;; The same, its second word on the stack's top again. Uses `X11`.
(define da-pop-frame-ret (subr da-assembles (int) unit)
  (lambda (size)
    (begin
      (da-ld d-x11 d-sp 16)
      (da-ld d-frame d-sp 8)
      (da-e (x86-alu-imm da-add d-sp (- size 8)))
      (da-sto d-sp 0 d-x11))))
(define da-stub-return (subr da-assembles () unit)
  (lambda () (begin (da-pop-frame-ret d-stub-frame) (da-e (x86-ret)))))

;; After call-out `POLL`: the scheduler's `preempt`, if it gave it, called,
;; and call-out `POLL_DONE` after it.
(define da-preempt (subr da-assembles () unit)
  (lambda ()
    (let ((back (da-label)))
      (begin
        (da-ld d-clo d-st d-st-aux)
        (da-e (x86-test d-clo d-clo))
        (da-jcc da-c-e back)
        (da-ld d-x16 d-clo (da-field-off d-closure-word))
        (da-e (x86-alu-rm da-add d-x16 d-st d-st-delta))
        (da-imm d-x9 0)
        (da-e (x86-call-r d-x16))
        (da-call-out d-poll-done)
        (da-bind back)))))

;; A call-out's arguments, registers, as `da-pure-call` takes them.
(define da-args1 (subr da-assembles (int) da-bytes) (lambda (a) (cons a nil)))
(define da-args2 (subr da-assembles (int int) da-bytes)
  ;; cons-chain: in `@k`, the assembler's region, which `list` would not be
  (lambda (a b) (cons a (cons b nil))))
(define da-args3 (subr da-assembles (int int int) da-bytes)
  ;; cons-chain: in `@k`, the assembler's region, which `list` would not be
  (lambda (a b c) (cons a (cons b (cons c nil)))))
;; Call-out `code`, which never collects, on `args` (registers, put in the
;; state), its value into `into`: `RESULT` and REG1…REG3 kept around it.
(define da-pure-call (subr da-assembles (int da-bytes int) unit)
  (lambda (code args into)
    (let ((n (da-callout code)))
      (letrec ((put (subr da-assembles (da-bytes int) unit)
                 (lambda (rs j)
                   (if (null? rs)
                       #u
                       (begin (da-sto d-st (da-arg-off j) (car rs)) (put (cdr rs) (+ j 1)))))))
        (begin
          (put args 0)
          (da-keep 4 #f)
          (da-call-out n)
          (da-mov d-x17 d-result)
          (da-keep 4 #t)
          (if (= into d-x17) #u (da-mov into d-x17)))))))

;; `f` on `REGr` in a register: its own, or `X12`, loaded first and stored
;; back after.
(define da-in-place (subr da-assembles (int da-on-reg) unit)
  (lambda (r f)
    (let ((x (da-in-reg r)))
      (if (>= x 0)
          (f x)
          (begin (da-ld d-x12 d-st (da-reg-off r)) (f d-x12) (da-sto d-st (da-reg-off r) d-x12))))))

;; `d` := bits `lo` to `lo + width - 1` of `s`.
(define da-ubfx (subr da-assembles (int int int int) unit)
  (lambda (d s lo width)
    (begin
      (if (= d s) #u (da-mov d s))
      (cond ((< (+ lo width) 64)
             (begin (da-e (x86-shift-imm da-shl d (- (- 64 lo) width)))
                    (da-e (x86-shift-imm da-shr d (- 64 width)))))
            ((> lo 0) (da-e (x86-shift-imm da-shr d lo)))
            (else #u)))))

;; Register `r` tested for a fixnum, to `general` if it is not one; and
;; `REGr` (r ≥ 1) so.
(define da-check-reg (subr da-assembles (int int) unit)
  (lambda (r general) (begin (da-e (x86-test-imm r 7)) (da-jcc da-c-ne general))))
(define da-check-fixnum (subr da-assembles (int int) unit)
  (lambda (r general) (da-check-reg (da-get r d-x16) general)))

;; The card of the word at `[obj + disp]` marked (`x86_64::card_mark`).
(define da-card-mark (subr da-assembles (int int int int) unit)
  (lambda (obj disp t1 t2)
    (begin
      (da-e (x86-lea t1 obj disp))
      (da-e (x86-shift-imm da-shr t1 9))
      (da-ld t2 d-st d-st-cards)
      (da-e (x86-store8-imm t2 t1 1 0 1)))))

;; Where field `k` of a bloblet is from its reference.
(define da-field-off (subr pure (int) int) (lambda (k) (- 0 (+ 4 (* 8 k)))))
;; A header of a kind, `fields` and `bytes`; a trailer `distance` back.
(define da-header (subr pure (int int int) int)
  (lambda (kind fields bytes)
    (+ d-tag-header
       (+ (arithmetic-shift kind d-h-kind-lo)
          (+ (arithmetic-shift fields d-h-fields-lo) (arithmetic-shift bytes d-h-bytes-lo))))))
(define da-trailer (subr pure (int) int)
  (lambda (distance) (+ d-tag-trailer (arithmetic-shift distance d-t-distance-lo))))

;; The continuation procedure's code, as `continuation_code`: in a frame of
;; its own it calls out (`n`) to put the continuation's frames back.
(define da-continuation-code (subr da-assembles (int) da-bytes)
  (lambda (n)
    (let ((failed (begin (da-reset 0) (da-label))))
      (begin
        (da-push-frame-ret d-stub-frame)
        (da-store-reg d-st d-st-args 1 d-x11)
        (da-sto d-st (+ d-st-args 8) d-clo)
        (da-call-out n)
        (da-trapped failed)
        (da-resume)
        (da-bind failed)
        (da-leave)
        (da-finish)))))
)))
