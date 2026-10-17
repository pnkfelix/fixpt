;;; Words compiled to x86_64 machine code, in FX-26: the x86_64 machine's
;;; `assemble_word` (`fixpt-native/src/cellular/x64.rs`), routine for
;;; routine and instruction for instruction, over the encoder written in
;;; FX-26 (`x86_64.fx`) and what the machine's generator says of it
;;; (`native-x64-layout.fx`), as `native.fx` is for arm64. The Rust
;;; compiler is this one's oracle: for every word, the same bytes
;;; (`tests/native_x64.rs`). Placing them, and making the word's entry name
;;; them, is the loader's, in Rust.
;;;
;;; Its steps have the names the Rust ones have (`x-save` is `save`,
;;; `x-push-return` is `push_return`), so that a change to one is made to
;;; the other by reading them side by side.
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, its assembler's state new, which the conductor applies to the
;;; encoders, and to the layouts the routines' numbers (`layout.fx`) and the
;;; machine (`native-x64-layout.fx`) are generated into.

;; Its types (`native-x64-types.fx`), and the signatures of what it is given.
(let* ((native-x64-types (load-module "fx26:native-x64-types.fx"))
       (x86-64-types (load-module "fx26:x86_64-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx")))
  (lambda ((x86 (select x86-64-types x86-64-sig))
           (layout (select layout-types layout-sig))
           (native-layout (select native-x64-types native-x64-layout-sig)))
    (module
(hide (include native-x64-types))
(hide (include x86) (include layout) (include native-layout))

;; Conditions, operations and shifts, by the hardware's numbers.
(define x-c-o int 0)
(define x-c-b int 2)
(define x-c-ae int 3)
(define x-c-e int 4)
(define x-c-ne int 5)
(define x-c-be int 6)
(define x-c-a int 7)
(define x-c-l int 12)
(define x-c-g int 15)
(define x-add int 0)
(define x-or int 1)
(define x-and int 4)
(define x-sub int 5)
(define x-cmp int 7)
(define x-shr int 5)
(define x-sar int 7)
;; The registers a call into Rust takes its arguments in, and gives its
;; result in.
(define x-rdi int 7)
(define x-rsi int 6)
(define x-rax int 0)

;;; ------------------------------------------------------------ the assembler
;;; Bytes, and labels patched when everything is placed. A label is where
;;; it is, in bytes from the start.

(define x-code (ref (arrayof int @k) @k) (new (make-array 16384 0)))
(define x-len (ref int @k) (new 0))
(define x-labels (ref (arrayof int @k) @k) (new (make-array 1024 0)))
(define x-bound (ref (arrayof bool @k) @k) (new (make-array 1024 #f)))
(define x-nlabels (ref int @k) (new 0))
(define x-fixups (ref x-fix-list @k) (new nil))
;; Where the last instruction starts, if it is a jump to a label; else -1.
(define x-last-jump (ref int @k) (new -1))
(define x-stubs (ref x-stub-list @k) (new nil))

;; Compiling a word: where its next cell's code is, and a branch's
;; target's, with the target's cell; -1 for none.
(define x-cont (ref int @k) (new -1))
(define x-target (ref int @k) (new -1))
(define x-target-cell (ref int @k) (new -1))
;; Compiling a word: the cell being compiled.
(define x-at (ref int @k) (new 0))
(define x-trap-common (ref int @k) (new 0))
(define x-exit-common (ref int @k) (new 0))

;; Elements `i` on of `from` into `to`.
(define x-copy-ints (subr x-writes (x-ints x-ints int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i))
               (x-copy-ints from to (+ i 1))))))
(define x-copy-bools (subr x-writes (x-bools x-bools int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i))
               (x-copy-bools from to (+ i 1))))))

(define x-here (subr (maxeff (read @globals) (read @k)) () int) (lambda () (get x-len)))

;; One byte, the array grown if it is full.
(define x-byte (subr (maxeff x-assembles spin) (int) unit)
  (lambda (b)
    (let ((n (get x-len)))
      (begin
        (if (= n (array-length (get x-code)))
            (let ((bigger (the (arrayof int @k) (make-array (* 2 n) 0))))
              (begin (x-copy-ints (get x-code) bigger 0) (set x-code bigger)))
            #u)
        (array-set! (get x-code) n b)
        (set x-len (+ n 1))))))
(define x-bytes (subr (maxeff x-assembles spin) (x-out) unit)
  (lambda (bs) (if (null? bs) #u (begin (x-byte (car bs)) (x-bytes (cdr bs))))))
;; An instruction.
(define x-e (subr (maxeff x-assembles spin) (x-out) unit)
  (lambda (bs) (begin (x-bytes bs) (set x-last-jump -1))))

(define x-label (subr (maxeff x-assembles spin) () int)
  (lambda ()
    (let ((n (get x-nlabels)))
      (begin
        (if (= n (array-length (get x-labels)))
            (let ((more (the (arrayof int @k) (make-array (* 2 n) 0)))
                  (flags (the (arrayof bool @k) (make-array (* 2 n) #f))))
              (begin (x-copy-ints (get x-labels) more 0) (x-copy-bools (get x-bound) flags 0)
                     (set x-labels more) (set x-bound flags)))
            #u)
        (array-set! (get x-bound) n #f)
        (set x-nlabels (+ n 1))
        n))))
;; Whether the newest fixup is the jump just before here, to `l`.
(define x-jump-to-here? (subr (maxeff (read @globals) (read @k)) (int) bool)
  (lambda (l)
    (let ((fs (get x-fixups)) (at (get x-last-jump)))
      (and (>= at 0)
           (not (null? fs))
           (= (extract (car fs) 1) (+ at 1))
           (= (extract (car fs) 2) l)))))
;; Label `l` here; a jump to it just before it goes.
(define x-bind (subr (maxeff x-assembles spin) (int) unit)
  (lambda (l)
    (begin
      (if (x-jump-to-here? l)
          (begin (set x-fixups (cdr (get x-fixups))) (set x-len (get x-last-jump)))
          #u)
      (set x-last-jump -1)
      (array-set! (get x-labels) l (x-here))
      (array-set! (get x-bound) l #t))))

;; A branch to `l`, its 32-bit displacement the last four bytes of `bs`.
(define x-to (subr (maxeff x-assembles spin) (int x-out) unit)
  (lambda (l bs)
    (begin
      (x-e bs)
      (set x-fixups (cons (product (1 (- (x-here) 4)) (2 l)) (get x-fixups))))))
(define x-jmp (subr (maxeff x-assembles spin) (int) unit)
  (lambda (l)
    (let ((at (x-here)))
      (begin (x-to l (x86-jmp 0)) (set x-last-jump at)))))
(define x-jcc (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (c l) (x-to l (x86-jcc c 0))))

;; Where label `l` is bound, in bytes from the code's start.
(define x-label-at (subr (maxeff (read @globals) (read @k)) (int) int)
  (lambda (l) (array-ref (get x-labels) l)))

;; To the common trap with `code` and `detail`.
(define x-trap (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (code detail)
    (begin
      (x-e (x86-mov-imm n-x13 code))
      (x-e (x86-mov-imm n-x14 detail))
      (x-jmp (get x-trap-common)))))
;; Trap with `code` and `detail` if condition `c` holds.
(define x-trap-if (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (c code detail)
    (let ((l (x-label)))
      (begin (x-jcc c l)
             (set x-stubs (cons (product (1 l) (2 code) (3 detail)) (get x-stubs)))))))
(define x-place-stubs (subr (maxeff x-assembles spin) (x-stub-list) unit)
  (lambda (ss)
    (if (null? ss)
        #u
        (let ((st (car ss)))
          (begin
            (x-bind (extract st 1))
            (x-trap (extract st 2) (extract st 3))
            (x-place-stubs (cdr ss)))))))
(define x-flush-stubs (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (let ((stubs (the x-stub-list (reverse (get x-stubs)))))
      (begin (set x-stubs nil) (x-place-stubs stubs)))))

;; The four bytes of `v` at `at`, lowest first.
(define x-put4 (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (at v i)
    (if (= i 4)
        #u
        (begin (array-set! (get x-code) (+ at i) (modulo v 256))
               (x-put4 at (quotient v 256) (+ i 1))))))
(define x-patch (subr (maxeff x-assembles spin) (x-fix-list) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (let ((at (extract (car fs) 1)) (l (extract (car fs) 2)))
          (begin
            (x-put4 at (modulo (- (array-ref (get x-labels) l) (+ at 4)) 4294967296) 0)
            (x-patch (cdr fs)))))))
(define x-code-list (subr x-lists (int x-out) x-out)
  (lambda (i acc) (if (< i 0) acc (x-code-list (- i 1) (cons (array-ref (get x-code) i) acc)))))

;; The code, every branch patched.
(define x-finish (subr (maxeff x-assembles spin) () x-out)
  (lambda ()
    (begin
      (x-patch (get x-fixups))
      (x-code-list (- (get x-len) 1) nil))))

(define x-reset (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (set x-len 0) (set x-nlabels 0) (set x-fixups nil) (set x-stubs nil) (set x-last-jump -1)
      (set x-cont -1) (set x-target -1) (set x-target-cell -1)
      (set x-trap-common (x-label))
      (set x-exit-common (x-label)))))

;;; ------------------------------------------------------------ machine sequences

;; Field `k` of the bloblet whose `suffix + 4` is in a register.
(define x-field (subr pure (int) int) (lambda (k) (- 0 (+ 4 (* 8 k)))))
(define x-load (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (d base disp) (x-e (x86-load d base disp))))
(define x-store (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (base disp s) (x-e (x86-store base disp s))))
(define x-mov (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (d s) (x-e (x86-mov d s))))
(define x-alu (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (op d s) (x-e (x86-alu op d s))))
(define x-alu-imm (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (op d imm) (x-e (x86-alu-imm op d imm))))
(define x-lea (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (d base disp) (x-e (x86-lea d base disp))))

;; Dispatch on the word in W: the tail of `NEXT`. Leaves the word in X11
;; too, where `docol` takes it.
(define x-run-word-in-w (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-mov n-x11 n-w)
      (x-load n-x10 n-w (x-field n-word-entry))
      (x-e (x86-jmp-m n-table n-x10 1 0)))))

(define x-next (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (let ((word (x-label)))
      (begin
        (x-load n-w n-ip 0)
        (x-alu-imm x-sub n-ip 8)
        (x-e (x86-test-imm n-w 7))
        (x-jcc x-c-ne word)
        (x-e (x86-jmp-m n-table n-w 1 0))
        (x-bind word)
        (x-run-word-in-w)))))

;; On to the next cell of this word.
(define x-cont-code (subr (maxeff x-assembles spin) () unit)
  (lambda () (if (< (get x-cont) 0) (x-next) (x-jmp (get x-cont)))))

;; On from where CUR and the ip now are, `d` in `dreg`.
(define x-enter-cur (subr (maxeff x-assembles spin) (int) unit)
  (lambda (dreg)
    (let ((cellular (x-label)))
      (begin
        (x-load n-x10 n-cur (x-field n-word-entry))
        (x-e (x86-test n-x10 n-x10))
        (x-jcc x-c-e cellular)
        (x-load n-x16 n-st n-st-resume)
        (x-e (x86-load-ix n-x16 n-x16 n-x10 1 0))
        (x-e (x86-test n-x16 n-x16))
        (x-jcc x-c-e cellular)
        (x-e (x86-load-ix n-x16 n-x16 dreg 1 0))
        (x-e (x86-test n-x16 n-x16))
        (x-jcc x-c-e cellular)
        (x-e (x86-jmp-r n-x16))
        (x-bind cellular)
        (x-next)))))

(define x-fp-encode (subr (maxeff x-assembles spin) (int) unit)
  (lambda (reg)
    (begin
      (x-load reg n-st n-st-ds-base)
      (x-alu-imm x-sub reg 8)
      (x-alu x-sub reg n-fp))))
(define x-fp-decode (subr (maxeff x-assembles spin) (int) unit)
  (lambda (reg)
    (begin
      (x-load n-fp n-st n-st-ds-base)
      (x-alu-imm x-sub n-fp 8)
      (x-alu x-sub n-fp reg))))

(define x-save (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-store n-st n-st-cur n-cur)
      (x-lea n-x13 n-cur -4)
      (x-alu x-sub n-x13 n-ip)
      (x-store n-st n-st-d n-x13)
      (x-store n-st n-st-dsp n-dsp)
      (x-store n-st n-st-rsp n-rsp)
      (x-fp-encode n-x13)
      (x-store n-st n-st-fp n-x13)
      (x-store n-st n-st-clo n-clo))))

;; Compare `reg` with a constant Value (X16 may be used for it).
(define x-cmp-value (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (reg v)
    (if (and (>= v -2147483648) (< v 2147483648))
        (x-alu-imm x-cmp reg v)
        (begin (x-e (x86-mov-imm n-x16 v)) (x-alu x-cmp reg n-x16)))))

;; `reg` = `#t` if `c` holds after the comparison just made, else `#f`.
(define x-boolean (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (reg c)
    (begin
      (x-load reg n-st n-st-fal)
      (x-e (x86-cmov-m c reg n-st n-st-tru)))))

(define x-push-ds (subr (maxeff x-assembles spin) (int) unit)
  (lambda (reg) (begin (x-alu-imm x-sub n-dsp 8) (x-store n-dsp 0 reg))))
(define x-pop-ds (subr (maxeff x-assembles spin) (int) unit)
  (lambda (reg) (begin (x-load reg n-dsp 0) (x-alu-imm x-add n-dsp 8))))
;; The next cell, an operand, into `reg`.
(define x-operand (subr (maxeff x-assembles spin) (int) unit)
  (lambda (reg) (begin (x-load reg n-ip 0) (x-alu-imm x-sub n-ip 8))))

;; A taken branch's new ip. In a compiled word it is made from the word,
;; not from the ip, so that a loop's iterations do not wait on one chain of
;; ip updates through them all.
(define x-branch-ip (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (if (< (get x-target-cell) 0)
        (x-alu x-sub n-ip n-x13)
        (x-lea n-ip n-cur (- 0 (+ 4 (* 8 (+ n-word-cell0 (get x-target-cell)))))))))

(define x-push-return (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-lea n-x13 n-cur -4)
      (x-alu x-sub n-x13 n-ip)
      (x-fp-encode n-x14)
      (x-alu-imm x-sub n-rsp 32)
      (x-store n-rsp 0 n-cur)
      (x-store n-rsp 8 n-x13)
      (x-store n-rsp 16 n-x14)
      (x-store n-rsp 24 n-clo))))

(define x-pass-mark (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (mark again)
    (let ((not-it (x-label)))
      (begin
        (x-cmp-value n-x13 mark)
        (x-jcc x-c-ne not-it)
        (x-alu-imm x-add n-rsp 32)
        (x-jmp again)
        (x-bind not-it)))))

(define x-pop-return (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (let ((again (x-label)))
      (begin
        (x-bind again)
        (x-load n-x13 n-rsp 0)
        (x-pass-mark n-prompt-mark again)
        (x-pass-mark n-mark-mark again)
        (x-load n-cur n-rsp 0)
        (x-load n-x13 n-rsp 8)
        (x-load n-x14 n-rsp 16)
        (x-load n-clo n-rsp 24)
        (x-alu-imm x-add n-rsp 32)
        (x-cmp-value n-cur n-false)
        (x-jcc x-c-e (get x-exit-common))
        (x-lea n-ip n-cur -4)
        (x-alu x-sub n-ip n-x13)
        (x-fp-decode n-x14)
        (x-enter-cur n-x13)))))

;; `d` = the kind in the header of the bloblet in `obj`, whose trailer is
;; in `trailer`.
(define x-header-kind (subr (maxeff x-assembles spin) (int int int) unit)
  (lambda (d obj trailer)
    (begin
      (x-mov d obj)
      (x-alu x-sub d trailer)
      (x-load d d -7)
      (x-e (x86-shift-imm x-shr d 3))
      (x-alu-imm x-and d 255))))

;; Whether `reg` is a cellular closure, else to `not-it`; leaves it in X11
;; and its trailer in X15.
(define x-is-closure (subr (maxeff x-assembles spin) (int int) unit)
  (lambda (reg not-it)
    (begin
      (x-mov n-x13 reg)
      (x-alu-imm x-and n-x13 7)
      (x-alu-imm x-cmp n-x13 n-tag-bloblet)
      (x-jcc x-c-ne not-it)
      (x-mov n-x11 reg)
      (x-load n-x15 n-x11 (x-field 1))
      (x-mov n-x13 n-x15)
      (x-alu-imm x-and n-x13 7)
      (x-alu-imm x-cmp n-x13 n-tag-trailer)
      (x-jcc x-c-ne not-it)
      (x-header-kind n-x14 n-x11 n-x15)
      (x-alu-imm x-cmp n-x14 n-kind-closure)
      (x-jcc x-c-ne not-it))))

;; Load them back, recomputing the ip from `cur` and `d`, which is left in
;; X13.
(define x-load-state (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-load n-cur n-st n-st-cur)
      (x-load n-x13 n-st n-st-d)
      (x-lea n-ip n-cur -4)
      (x-alu x-sub n-ip n-x13)
      (x-load n-dsp n-st n-st-dsp)
      (x-load n-rsp n-st n-st-rsp)
      (x-load n-table n-st n-st-table)
      (x-load n-clo n-st n-st-clo)
      (x-load n-x14 n-st n-st-fp)
      (x-fp-decode n-x14))))

;; A poll, at a cell boundary: `CUR` and `IP` say where to go on, so that a
;; time slice's end leaves the machine (detail 0) and comes back there.
(define x-fuel (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-e (x86-alu-mi x-sub n-st n-st-fuel 1))
      (x-trap-if x-c-e n-trap-out-of-fuel 0))))
;; A call's poll, before anything is done: its cell, one before `IP`, is
;; where to go on (detail 1).
(define x-fuel-call (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-e (x86-alu-mi x-sub n-st n-st-fuel 1))
      (x-trap-if x-c-e n-trap-out-of-fuel 1))))
;; A taken branch's poll: only a backward one can make a loop, so a branch
;; known to go forward (in a compiled word) makes none.
(define x-fuel-unless-forward (subr (maxeff x-assembles spin) () unit)
  (lambda () (if (> (get x-target-cell) (get x-at)) #u (x-fuel))))
(define x-ds-limit (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-e (x86-alu-rm x-cmp n-dsp n-st n-st-ds-limit))
      (x-trap-if x-c-b n-trap-stack-overflow 0))))
(define x-rs-limit (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-e (x86-alu-rm x-cmp n-rsp n-st n-st-rs-limit))
      (x-trap-if x-c-be n-trap-too-deep 0))))

;; Leave machine code for the Rust side of routine `n`.
(define x-callout (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (begin
      (x-save)
      (x-mov x-rdi n-st)
      (x-e (x86-mov-imm x-rsi n))
      (x-e (x86-call-m n-st n-st-callout))
      (x-e (x86-test x-rax x-rax))
      (x-jcc x-c-ne (get x-exit-common))
      (x-load-state)
      (if (n-control? n) (x-enter-cur n-x13) (x-cont-code)))))

;; X13 = top, X14 = the one below; `ne` unless both are fixnums.
(define x-both-fixnums (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (begin
      (x-load n-x13 n-dsp 0)
      (x-load n-x14 n-dsp 8)
      (x-mov n-x15 n-x13)
      (x-alu x-or n-x15 n-x14)
      (x-e (x86-test-imm n-x15 7)))))
(define x-two-fixnums (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n) (begin (x-both-fixnums) (x-trap-if x-c-ne n-trap-type n))))

(define x-check-tag (subr (maxeff x-assembles spin) (int int int int) unit)
  (lambda (reg tag code detail)
    (begin
      (x-mov n-x13 reg)
      (x-alu-imm x-and n-x13 7)
      (x-alu-imm x-cmp n-x13 tag)
      (x-trap-if x-c-ne code detail))))

;; The value in X15 pushed over the top two: the result of a routine of two.
(define x-replace-two (subr (maxeff x-assembles spin) () unit)
  (lambda () (begin (x-alu-imm x-add n-dsp 8) (x-store n-dsp 0 n-x15))))

;;; ------------------------------------------------------------ routines

(define x-execute (subr (maxeff x-assembles spin) () unit)
  (lambda ()
    (let ((is-ref (x-label)) (bad (x-label)))
      (begin
        (x-pop-ds n-w)
        (x-e (x86-test-imm n-w 7))
        (x-jcc x-c-ne is-ref)
        (x-e (x86-test n-w n-w))
        (x-jcc x-c-e bad)
        (x-alu-imm x-cmp n-w (* 8 n-primitives))
        (x-jcc x-c-ae bad)
        (x-e (x86-jmp-m n-table n-w 1 0))
        (x-bind bad)
        (x-e (x86-mov-imm n-x13 n-trap-no-routine))
        (x-mov n-x14 n-w)
        (x-e (x86-shift-imm x-sar n-x14 3))
        (x-jmp (get x-trap-common))
        (x-bind is-ref)
        (x-check-tag n-w n-tag-bloblet n-trap-not-a-word 0)
        (x-mov n-x11 n-w)
        (x-load n-x15 n-x11 (x-field 1))
        (x-check-tag n-x15 n-tag-trailer n-trap-not-a-word 0)
        (x-header-kind n-x14 n-x11 n-x15)
        (x-alu-imm x-cmp n-x14 n-kind-word)
        (x-trap-if x-c-ne n-trap-not-a-word 0)
        (x-run-word-in-w)))))

;; `+` or `-` (routine `n`): `add`, or `sub`.
(define x-arith (subr (maxeff x-assembles spin) (int bool) unit)
  (lambda (n add?)
    (begin
      (x-mov n-x15 n-x14)
      (x-alu (if add? x-add x-sub) n-x15 n-x13))))

(define x-field-ref (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (let ((slow (x-label)))
      (begin
        (x-load n-x15 n-dsp 0)
        (x-load n-x14 n-dsp 8)
        (x-e (x86-test-imm n-x15 7))
        (x-trap-if x-c-ne n-trap-type n)
        (x-check-tag n-x14 n-tag-bloblet n-trap-type n)
        (x-load n-x16 n-x14 (x-field 1))
        (x-mov n-x13 n-x16)
        (x-alu-imm x-and n-x13 7)
        (x-alu-imm x-cmp n-x13 n-tag-trailer)
        (x-jcc x-c-ne slow)
        (x-alu-imm x-cmp n-x15 16)
        (x-trap-if x-c-l n-trap-field n)
        (x-alu-imm x-sub n-x16 n-tag-trailer)
        (x-alu x-cmp n-x15 n-x16)
        (x-trap-if x-c-g n-trap-field n)
        (x-alu x-sub n-x14 n-x15)
        (x-load n-x15 n-x14 -4)
        (x-replace-two)
        (x-cont-code)
        (x-bind slow)
        (x-callout n)))))

(define x-free (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (let ((bad (x-label)))
      (begin
        (x-operand n-x10)
        (x-is-closure n-clo bad)
        (x-alu-imm x-add n-x10 (* 8 n-closure-free0))
        (x-mov n-x16 n-x15)
        (x-alu-imm x-sub n-x16 n-tag-trailer)
        (x-alu x-cmp n-x10 n-x16)
        (x-jcc x-c-g bad)
        (x-mov n-x14 n-x11)
        (x-alu x-sub n-x14 n-x10)
        (x-load n-x15 n-x14 -4)
        (x-push-ds n-x15)
        (x-cont-code)
        (x-bind bad)
        (x-trap n-trap-field n)))))

;; Untyped, a callee not a cellular closure (a continuation, not a
;; procedure, or a native closure) goes the Rust machine's way. Typed
;; (`tcall`), the callee's type says `cellular`, so it is a cellular closure:
;; nothing is checked (`TODO.md` §97); a typed tail call, which grows
;; neither stack, does not check them.
(define x-call (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (let ((other (x-label))
          (typed (or (= n routine-tcall) (= n routine-ttailcall)))
          (tail (or (= n routine-tailcall) (= n routine-ttailcall))))
      (begin
        (x-load n-w n-dsp 0)
        (if typed #u (x-is-closure n-w other))
        (x-fuel-call)
        (if (and typed tail) #u (begin (x-ds-limit) (x-rs-limit)))
        (x-operand n-x10)
        (x-alu-imm x-add n-dsp 8)
        (if (not tail)
            (begin
              (x-push-return)
              (x-e (x86-lea-ix n-fp n-dsp n-x10 1 -8)))
            (let ((top (x-label)) (done (x-label)))
              (begin
                (x-e (x86-lea-ix n-x14 n-dsp n-x10 1 -8))
                (x-mov n-x15 n-fp)
                (x-mov n-x16 n-x10)
                (x-bind top)
                (x-e (x86-test n-x16 n-x16))
                (x-jcc x-c-e done)
                (x-load n-x10 n-x14 0)
                (x-alu-imm x-sub n-x14 8)
                (x-store n-x15 0 n-x10)
                (x-alu-imm x-sub n-x15 8)
                (x-alu-imm x-sub n-x16 8)
                (x-jmp top)
                (x-bind done)
                (x-lea n-dsp n-x15 8))))
        (x-mov n-clo n-w)
        (x-load n-cur n-w (x-field n-closure-word))
        (x-lea n-ip n-cur (- 0 (+ 4 (* 8 n-word-cell0))))
        (x-e (x86-mov-imm n-x13 (* 8 n-word-cell0)))
        (x-enter-cur n-x13)
        (if typed #u (begin (x-bind other) (x-callout n)))))))

;; `int-add` or `int-sub` (routine `n`) on two fixnums; the Rust machine's
;; on a bignum, or past a fixnum.
(define x-int-arith (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (let ((slow (x-label)))
      (begin
        (x-both-fixnums)
        (x-jcc x-c-ne slow)
        (x-arith n (= n routine-int-add))
        (x-jcc x-c-o slow)
        (x-replace-two)
        (x-cont-code)
        (x-bind slow)
        (x-callout n)))))
;; `int-less` or `int-eq` (routine `n`) on two fixnums; the Rust machine's
;; on a bignum.
(define x-int-compare (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (let ((slow (x-label)))
      (begin
        (x-both-fixnums)
        (x-jcc x-c-ne slow)
        (x-alu x-cmp n-x14 n-x13)
        (x-boolean n-x15 (if (= n routine-int-less) x-c-l x-c-e))
        (x-replace-two)
        (x-cont-code)
        (x-bind slow)
        (x-callout n)))))

;; Routine `n`'s code, going on to the next cell's.
(define x-routine (subr (maxeff x-assembles spin) (int) unit)
  (lambda (n)
    (cond
      ((= n routine-docol)
       (begin
         (x-ds-limit) (x-rs-limit) (x-push-return)
         (x-mov n-cur n-w)
         (x-lea n-ip n-x11 (- 0 (+ 4 (* 8 n-word-cell0))))
         (x-fuel)
         (x-next)))
      ((= n routine-exit) (x-pop-return))
      ((= n routine-halt) (x-jmp (get x-exit-common)))
      ((= n routine-lit) (begin (x-operand n-x13) (x-push-ds n-x13) (x-cont-code)))
      ((= n routine-branch)
       (begin
         (if (< (get x-target) 0) (x-operand n-x13) #u)
         (x-branch-ip) (x-fuel-unless-forward) (x-ds-limit)
         (if (< (get x-target) 0) (x-next) (x-jmp (get x-target)))))
      ((= n routine-zbranch)
       (let ((skip (x-label)))
         (begin
           (x-pop-ds n-x14)
           (x-operand n-x13)
           (x-cmp-value n-x14 n-false)
           (x-jcc x-c-ne skip)
           (x-branch-ip)
           (x-fuel-unless-forward) (x-ds-limit)
           (if (< (get x-target) 0)
               (begin (x-bind skip) (x-next))
               (begin (x-jmp (get x-target)) (x-bind skip) (x-cont-code))))))
      ((= n routine-execute) (x-execute))
      ((= n routine-dup) (begin (x-load n-x13 n-dsp 0) (x-push-ds n-x13) (x-cont-code)))
      ((= n routine-drop) (begin (x-alu-imm x-add n-dsp 8) (x-cont-code)))
      ((= n routine-swap)
       (begin
         (x-load n-x13 n-dsp 0)
         (x-load n-x14 n-dsp 8)
         (x-store n-dsp 0 n-x14)
         (x-store n-dsp 8 n-x13)
         (x-cont-code)))
      ((= n routine-over) (begin (x-load n-x13 n-dsp 8) (x-push-ds n-x13) (x-cont-code)))
      ((or (= n routine-add) (= n routine-sub))
       (begin
         (x-two-fixnums n)
         (x-arith n (= n routine-add))
         (x-trap-if x-c-o n-trap-overflow n)
         (x-replace-two)
         (x-cont-code)))
      ((= n routine-less)
       (begin
         (x-two-fixnums n)
         (x-alu x-cmp n-x14 n-x13)
         (x-boolean n-x15 x-c-l)
         (x-replace-two)
         (x-cont-code)))
      ((= n routine-eq)
       (begin
         (x-load n-x13 n-dsp 0)
         (x-load n-x14 n-dsp 8)
         (x-alu x-cmp n-x14 n-x13)
         (x-boolean n-x15 x-c-e)
         (x-replace-two)
         (x-cont-code)))
      ;; A list may be `nil`: `car` of it traps, as the Rust machine's does.
      ((or (= n routine-car) (= n routine-cdr) (= n routine-pair-car) (= n routine-pair-cdr))
       (begin
         (x-load n-x15 n-dsp 0)
         (x-check-tag n-x15 n-tag-pair n-trap-type n)
         (x-load n-x15 n-x15 (if (or (= n routine-car) (= n routine-pair-car)) -1 7))
         (x-store n-dsp 0 n-x15)
         (x-cont-code)))
      ;; Typed: the checker has proved the operands ints. Fixnums here; a
      ;; bignum, or a sum past a fixnum, the Rust machine's (PLAN.md, Q2).
      ((or (= n routine-int-add) (= n routine-int-sub)) (x-int-arith n))
      ((or (= n routine-int-less) (= n routine-int-eq)) (x-int-compare n))
      ((= n routine-field)
       (begin
         (x-operand n-x13)
         (x-load n-x16 n-dsp 0)
         (x-alu x-sub n-x16 n-x13)
         (x-load n-x15 n-x16 -4)
         (x-store n-dsp 0 n-x15)
         (x-cont-code)))
      ((= n routine-field-ref) (x-field-ref n))
      ((or (= n routine-slot) (= n routine-slot!))
       (begin
         (x-operand n-x13)
         (x-mov n-x14 n-fp)
         (x-alu x-sub n-x14 n-x13)
         (if (= n routine-slot!) (x-pop-ds n-x15) #u)
         (x-alu x-cmp n-x14 n-dsp)
         (x-trap-if x-c-b n-trap-field n)
         (if (= n routine-slot)
             (begin (x-load n-x15 n-x14 0) (x-push-ds n-x15))
             (x-store n-x14 0 n-x15))
         (x-cont-code)))
      ((= n routine-free) (x-free n))
      ((or (= n routine-global) (= n routine-global!))
       (begin
         (x-operand n-x11)
         (if (= n routine-global)
             (begin (x-load n-x15 n-x11 (x-field 2)) (x-push-ds n-x15))
             (begin
               (x-pop-ds n-x15)
               (x-store n-x11 (x-field 2) n-x15)
               ;; One more write, for the guards (`global-guard`).
               (x-e (x86-alu-mi x-add n-x11 (x-field global-writes) 8))
               ;; The write barrier, as `x86_64::card_mark` makes it.
               (x-lea n-x13 n-x11 (x-field 2))
               (x-e (x86-shift-imm x-shr n-x13 9))
               (x-load n-x16 n-st n-st-cards)
               (x-e (x86-store8-imm n-x16 n-x13 1 0 1))))
         (x-cont-code)))
      ((or (= n routine-call) (= n routine-tailcall) (= n routine-tcall) (= n routine-ttailcall))
       (x-call n))
      ((= n routine-return)
       (begin
         (x-pop-ds n-x15)
         (x-lea n-x14 n-fp 8)
         (x-alu x-cmp n-dsp n-x14)
         (x-trap-if x-c-a n-trap-underflow n)
         (x-mov n-dsp n-fp)
         (x-store n-dsp 0 n-x15)
         (x-pop-return)))
      (else (x-callout n)))))

;;; ------------------------------------------------------------ words

;; Where each instruction of `w`'s cells starts: for cell i, whether one
;; does, marked from cell `i` on.
(define x-mark-starts (subr x-writes (x-bools tword int int) unit)
  (lambda (a w i n)
    (if (>= i n)
        #u
        (let* ((k (+ n-word-cell0 i))
               (width (if (tword-int? w k) (+ 1 (n-operands (tword-int w k))) 1)))
          (begin
            (array-set! a i #t)
            (x-mark-starts a w (+ i width) n))))))
(define x-starts (subr (maxeff x-writes (alloc @k)) (tword int) x-bools)
  (lambda (w n)
    (let ((a (the (arrayof bool @k) (make-array (+ n 1) #f))))
      (begin (x-mark-starts a w 0 n) a))))
(define x-fill-labels (subr (maxeff x-assembles spin) ((arrayof int @k) int) unit)
  (lambda (a i)
    (if (= i (array-length a))
        #u
        (begin (array-set! a i (x-label))
               (x-fill-labels a (+ i 1))))))
(define x-labels-for (subr (maxeff x-assembles spin) (int) (arrayof int @k))
  (lambda (n)
    (let ((a (the (arrayof int @k) (make-array n 0))))
      (begin (x-fill-labels a 0) a))))
;; Where each of cells 0 to `i` starts in the code, or -1, onto `acc`.
(define x-starts-at (subr x-lists (int x-bools x-ints x-out) x-out)
  (lambda (i starts labels acc)
    (if (< i 0)
        acc
        (let ((start (if (array-ref starts i) (array-ref (get x-labels) (array-ref labels i)) -1)))
          (x-starts-at (- i 1) starts labels (cons start acc))))))

;; The cell after `i` where an instruction starts, or `n`.
(define x-next-start (subr (maxeff (read @globals) (read @k)) (int int (arrayof bool @k)) int)
  (lambda (i n starts) (if (or (>= i n) (array-ref starts i)) i (x-next-start (+ i 1) n starts))))

(define x-cells (subr (maxeff x-assembles spin) (tword int int x-bools x-ints) unit)
  (lambda (w i n starts labels)
    (if (= i n)
        #u
        (begin
          (if (array-ref starts i)
              (let ((k (+ n-word-cell0 i)))
                (begin
                  (x-bind (array-ref labels i))
                  (if (tword-int? w k)
                      (let* ((r (tword-int w k))
                             (next (x-next-start (+ i 1) n starts)))
                        (begin
                          (set x-cont (if (< next n) (array-ref labels next) -1))
                          (set x-target-cell
                               (if (or (= r routine-branch) (= r routine-zbranch))
                                   (+ (+ i 2) (tword-int w (+ k 1)))
                                   -1))
                          (set x-target
                               (if (< (get x-target-cell) 0)
                                   -1
                                   (array-ref labels (get x-target-cell))))
                          (set x-at i)
                          (x-alu-imm x-sub n-ip 8)
                          (x-routine r)))
                      (begin
                        (set x-cont -1)
                        (set x-target -1)
                        (set x-target-cell -1)
                        (x-operand n-w)
                        (x-run-word-in-w)))))
              #u)
          (x-cells w (+ i 1) n starts labels)))))

;; `w`'s cells as x86_64 machine code: the bytes, and where each cell's
;; code starts in them, or -1. What `x64::assemble_word` makes.
(define native-assemble-x64 (subr (maxeff x-assembles spin) (tword) x-assembled)
  (lambda (w)
    (begin
      (x-reset)
      (let* ((cells (- (+ (tword-fields w) 1) n-word-cell0))
             (starts (x-starts w cells))
             (labels (x-labels-for (+ cells 1))))
        (begin
          ;; As a cell: `docol`'s work, then the first cell.
          (x-ds-limit) (x-rs-limit) (x-push-return)
          (x-mov n-cur n-w)
          (x-lea n-ip n-x11 (- 0 (+ 4 (* 8 n-word-cell0))))
          (x-fuel)
          (x-jmp (array-ref labels 0))
          (x-cells w 0 cells starts labels)
          ;; The traps, after all the cells, so that each cell's code runs
          ;; on into the next's.
          (x-flush-stubs)
          ;; The machine's common trap and exit, through the state: no
          ;; branch leaves this code, so it may be placed anywhere.
          (x-bind (get x-trap-common))
          (x-e (x86-jmp-m n-st -1 1 n-st-trap))
          (x-bind (get x-exit-common))
          (x-e (x86-jmp-m n-st -1 1 n-st-exit))
          (let ((at (x-starts-at (- cells 1) starts labels nil)))
            (product (1 (x-finish)) (2 at)))))))))))
