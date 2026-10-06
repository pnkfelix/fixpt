;;; Words compiled to machine code, in FX-26 (PLAN.md §11, step 11c): the
;;; hand-encoded machine's `assemble_word` (`fixpt-native/src/cellular.rs`),
;;; routine for routine and instruction for instruction, over the encoder
;;; written in FX-26 (`arm64.fx`) and what the machine's generator says of
;;; it (`native-layout.fx`). The Rust compiler is this one's oracle: for
;;; every word, the same instructions (`tests/native.rs`). Placing them, and
;;; making the word's entry name them, is the loader's, in Rust.
;;;
;;; A word's code does what its cells do, routine for routine, with the ip
;;; kept in step, so that it and cellular code mix freely; branches become
;;; jumps, and the dispatch between cells goes.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define native-module (module
(define-effect assembles (maxeff (read @globals) (read @k) (write @k) (alloc @k)))
;; Writing the assembler's arrays, and looping; reading them to make lists.
(define-effect n-writes (maxeff (read @globals) (read @k) (write @k) spin))
(define-effect n-lists (maxeff (read @globals) (read @k) (alloc @k) spin))
;; The assembler's arrays; the code it gives; and that with where each
;; cell's code starts.
(define-type n-ints (arrayof int @k))
(define-type n-bools (arrayof bool @k))
(define-type n-instrs (listof int @k))
(define-type n-assembled (productof (1 n-instrs) (2 n-instrs)))

;;; ------------------------------------------------------------ the assembler
;;; Instructions, and labels patched when everything is placed. A label is
;;; where it is, in instructions from the start: below zero for one in the
;;; machine the code is placed after.

(define n-code (ref (arrayof int @k) @k) (new (make-array 4096 0)))
(define n-len (ref int @k) (new 0))
(define n-labels (ref (arrayof int @k) @k) (new (make-array 1024 0)))
(define n-bound (ref (arrayof bool @k) @k) (new (make-array 1024 #f)))
(define n-nlabels (ref int @k) (new 0))

;; A branch to patch: where it is, its label, and for a conditional one
;; its condition or register.
(define-datatype n-fix
  (fix-b int int)
  (fix-bcond int int int)
  (fix-cbz int int int)
  (fix-cbnz int int int))
(define n-fixups (ref (listof n-fix @k) @k) (new nil))
;; Traps raised in the code being emitted, placed after it: label, code,
;; detail; newest first.
(define-type n-stub-list (listof (productof (1 int) (2 int) (3 int)) @k))
(define n-stubs (ref n-stub-list @k) (new nil))

;; Compiling a word: where its next cell's code is, and a branch's
;; target's, with the target's cell; -1 for none.
(define n-cont (ref int @k) (new -1))
(define n-target (ref int @k) (new -1))
(define n-target-cell (ref int @k) (new -1))
;; Compiling a word: the cell being compiled.
(define n-at (ref int @k) (new 0))
(define n-trap-common (ref int @k) (new 0))
(define n-exit-common (ref int @k) (new 0))

;; Elements `i` on of `from` into `to`.
(define n-copy-ints (subr n-writes (n-ints n-ints int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i))
               (n-copy-ints from to (+ i 1))))))
(define n-copy-bools (subr n-writes (n-bools n-bools int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i))
               (n-copy-bools from to (+ i 1))))))

(define n-here (subr (maxeff (read @globals) (read @k)) () int) (lambda () (get n-len)))

(define n-e (subr (maxeff assembles spin) (int) unit)
  (lambda (w)
    (let ((n (get n-len)))
      (begin
        (if (= n (array-length (get n-code)))
            (let ((bigger (the (arrayof int @k) (make-array (* 2 n) 0))))
              (begin (n-copy-ints (get n-code) bigger 0) (set n-code bigger)))
            #u)
        (array-set! (get n-code) n w)
        (set n-len (+ n 1))))))
(define n-es (subr (maxeff assembles spin) ((listof int @k)) unit)
  (lambda (ws) (if (null? ws) #u (begin (n-e (car ws)) (n-es (cdr ws))))))

(define n-label (subr (maxeff assembles spin) () int)
  (lambda ()
    (let ((n (get n-nlabels)))
      (begin
        (if (= n (array-length (get n-labels)))
            (let ((more (the (arrayof int @k) (make-array (* 2 n) 0)))
                  (flags (the (arrayof bool @k) (make-array (* 2 n) #f))))
              (begin (n-copy-ints (get n-labels) more 0) (n-copy-bools (get n-bound) flags 0)
                     (set n-labels more) (set n-bound flags)))
            #u)
        (array-set! (get n-bound) n #f)
        (set n-nlabels (+ n 1))
        n))))
(define n-bind-at (subr assembles (int int) unit)
  (lambda (l at) (begin (array-set! (get n-labels) l at) (array-set! (get n-bound) l #t))))
(define n-bind (subr assembles (int) unit) (lambda (l) (n-bind-at l (n-here))))

(define n-fixup (subr (maxeff assembles spin) (n-fix) unit)
  (lambda (f) (begin (set n-fixups (cons f (get n-fixups))) (n-e 0))))
(define n-b (subr (maxeff assembles spin) (int) unit) (lambda (l) (n-fixup (fix-b (n-here) l))))
(define n-b-cond (subr (maxeff assembles spin) (int int) unit)
  (lambda (c l) (n-fixup (fix-bcond (n-here) l c))))
(define n-cbz (subr (maxeff assembles spin) (int int) unit)
  (lambda (r l) (n-fixup (fix-cbz (n-here) l r))))
(define n-cbnz (subr (maxeff assembles spin) (int int) unit)
  (lambda (r l) (n-fixup (fix-cbnz (n-here) l r))))

;; Trap with `code` and `detail` if condition `c` holds.
(define n-trap-if (subr (maxeff assembles spin) (int int int) unit)
  (lambda (c code detail)
    (let ((l (n-label)))
      (begin (n-b-cond c l)
             (set n-stubs (cons (product (1 l) (2 code) (3 detail)) (get n-stubs)))))))
(define n-place-stubs (subr (maxeff assembles spin) (n-stub-list) unit)
  (lambda (ss)
    (if (null? ss)
        #u
        (let ((st (car ss)))
          (begin
            (n-bind (extract st 1))
            (n-e (arm-movz n-x13 (extract st 2) 0))
            (n-e (arm-movz n-x14 (extract st 3) 0))
            (n-b (get n-trap-common))
            (n-place-stubs (cdr ss)))))))
(define n-flush-stubs (subr (maxeff assembles spin) () unit)
  (lambda ()
    (let ((stubs (the n-stub-list (reverse (get n-stubs)))))
      (begin (set n-stubs nil) (n-place-stubs stubs)))))
;; From instruction `at` to label `l`, which must be bound: else an
;; impossible distance, which no encoder takes.
(define n-dist (subr (maxeff (read @globals) (read @k)) (int int) int)
  (lambda (at l)
    (if (array-ref (get n-bound) l) (- (array-ref (get n-labels) l) at) (* 4 67108864))))
(define n-patch (subr (maxeff assembles spin) ((listof n-fix @k)) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (begin
          (tagcase (car fs)
            (fix-b (at l) (array-set! (get n-code) at (arm-b (n-dist at l))))
            (fix-bcond (at l c) (array-set! (get n-code) at (arm-b-cond c (n-dist at l))))
            (fix-cbz (at l r) (array-set! (get n-code) at (arm-cbz r (n-dist at l))))
            (fix-cbnz (at l r) (array-set! (get n-code) at (arm-cbnz r (n-dist at l)))))
          (n-patch (cdr fs))))))
(define n-code-list (subr n-lists (int n-instrs) n-instrs)
  (lambda (i acc) (if (< i 0) acc (n-code-list (- i 1) (cons (array-ref (get n-code) i) acc)))))

;; The code, every branch patched.
(define n-finish (subr (maxeff assembles spin) () (listof int @k))
  (lambda ()
    (begin
      (n-patch (get n-fixups))
      (n-code-list (- (get n-len) 1) nil))))

(define n-reset (subr (maxeff assembles spin) () unit)
  (lambda ()
    (begin
      (set n-len 0) (set n-nlabels 0) (set n-fixups nil) (set n-stubs nil)
      (set n-cont -1) (set n-target -1) (set n-target-cell -1)
      (set n-trap-common (n-label))
      (set n-exit-common (n-label)))))

;;; ------------------------------------------------------------ machine sequences

;; Field `k` of the bloblet whose `suffix + 4` is in a register.
(define n-field-off (subr pure (int) int) (lambda (k) (- 0 (+ 4 (* 8 k)))))
;; The write barrier after a value is stored at `[obj, #off]`, as the Rust
;; machine's `card_mark` makes it: that word's card marked in the card
;; table, whose biased address is the state's `cards`; `x13` and `x16` lost.
(define n-card-mark (subr (maxeff assembles spin) (int int) unit)
  (lambda (obj off)
    (begin
      (n-e (if (< off 0) (arm-sub-imm n-x13 obj (- 0 off)) (arm-add-imm n-x13 obj off)))
      (n-e (arm-lsr-imm n-x13 n-x13 9))
      (n-e (arm-ldr n-x16 n-st n-st-cards))
      (n-e (arm-add n-x16 n-x16 n-x13))
      (n-e (arm-movz n-x13 1 0))
      (n-e (arm-strb n-x13 n-x16)))))

;; Dispatch on the cell in x9: the tail of `NEXT`.
(define n-run-word-in-w (subr (maxeff assembles spin) () unit)
  (lambda ()
    (begin
      (n-e (arm-add n-x11 n-base n-w))
      (n-e (arm-ldur n-x10 n-x11 (n-field-off n-word-entry)))
      (n-e (arm-ldr-reg n-x10 n-table n-x10))
      (n-e (arm-br n-x10)))))

(define n-next (subr (maxeff assembles spin) () unit)
  (lambda ()
    (begin
      (n-e (arm-ldr-post n-w n-ip -8))
      (n-e (arm-tst-low n-w 3))
      (n-e (arm-b-cond 1 3))
      (n-e (arm-ldr-reg n-x10 n-table n-w))
      (n-e (arm-br n-x10))
      (n-run-word-in-w))))

;; On to the next cell of this word.
(define n-cont-code (subr (maxeff assembles spin) () unit)
  (lambda () (if (< (get n-cont) 0) (n-next) (n-b (get n-cont)))))

;; On from where CUR and the ip now are, `d` in `dreg`.
(define n-enter-cur (subr (maxeff assembles spin) (int) unit)
  (lambda (dreg)
    (let ((cellular (n-label)))
      (begin
        (n-e (arm-add n-x11 n-base n-cur))
        (n-e (arm-ldur n-x10 n-x11 (n-field-off n-word-entry)))
        (n-cbz n-x10 cellular)
        (n-e (arm-ldr n-x16 n-st n-st-resume))
        (n-e (arm-ldr-reg n-x16 n-x16 n-x10))
        (n-cbz n-x16 cellular)
        (n-e (arm-ldr-reg n-x16 n-x16 dreg))
        (n-cbz n-x16 cellular)
        (n-e (arm-br n-x16))
        (n-bind cellular)
        (n-next)))))

(define n-fp-encode (subr (maxeff assembles spin) (int) unit)
  (lambda (reg)
    (begin
      (n-e (arm-ldr reg n-st n-st-ds-base))
      (n-e (arm-sub-imm reg reg 8))
      (n-e (arm-sub reg reg n-fp)))))
(define n-fp-decode (subr (maxeff assembles spin) (int) unit)
  (lambda (reg)
    (begin
      (n-e (arm-ldr n-x16 n-st n-st-ds-base))
      (n-e (arm-sub-imm n-x16 n-x16 8))
      (n-e (arm-sub n-fp n-x16 reg)))))

(define n-value (subr (maxeff assembles spin) (int int) unit)
  (lambda (reg v) (n-es (arm-mov-imm64 reg v))))

;; A taken branch's new ip. In a compiled word it is made from the word,
;; not from the ip, so that a loop's iterations do not wait on one chain of
;; ip updates through them all.
(define n-branch-ip (subr (maxeff assembles spin) () unit)
  (lambda ()
    (if (< (get n-target) 0)
        (n-e (arm-sub n-ip n-ip n-x13))
        (begin
          (n-value n-x13 (+ 4 (* 8 (+ n-word-cell0 (get n-target-cell)))))
          (n-e (arm-add n-ip n-base n-cur))
          (n-e (arm-sub n-ip n-ip n-x13))))))

(define n-push-return (subr (maxeff assembles spin) () unit)
  (lambda ()
    (begin
      (n-e (arm-add n-x13 n-base n-cur))
      (n-e (arm-sub-imm n-x13 n-x13 4))
      (n-e (arm-sub n-x13 n-x13 n-ip))
      (n-fp-encode n-x14)
      (n-e (arm-stp-pre n-x14 n-clo n-rsp -16))
      (n-e (arm-stp-pre n-cur n-x13 n-rsp -16)))))
(define n-pass-mark (subr (maxeff assembles spin) (int int) unit)
  (lambda (mark again)
    (let ((not-it (n-label)))
      (begin
        (n-value n-x15 mark)
        (n-e (arm-cmp n-x13 n-x15))
        (n-b-cond 1 not-it)
        (n-e (arm-add-imm n-rsp n-rsp 32))
        (n-b again)
        (n-bind not-it)))))

(define n-pop-return (subr (maxeff assembles spin) () unit)
  (lambda ()
    (let ((again (n-label)))
      (begin
        (n-bind again)
        (n-e (arm-ldr n-x13 n-rsp 0))
        (n-pass-mark n-prompt-mark again)
        (n-pass-mark n-mark-mark again)
        (n-e (arm-ldp-post n-cur n-x13 n-rsp 16))
        (n-e (arm-ldp-post n-x14 n-clo n-rsp 16))
        (n-value n-x15 n-false)
        (n-e (arm-cmp n-cur n-x15))
        (n-b-cond 0 (get n-exit-common))
        (n-e (arm-add n-ip n-base n-cur))
        (n-e (arm-sub-imm n-ip n-ip 4))
        (n-e (arm-sub n-ip n-ip n-x13))
        (n-fp-decode n-x14)
        (n-enter-cur n-x13)))))

(define n-is-closure (subr (maxeff assembles spin) (int int) unit)
  (lambda (reg not-it)
    (begin
      (n-e (arm-and-low n-x13 reg 3))
      (n-e (arm-cmp-imm n-x13 n-tag-bloblet))
      (n-b-cond 1 not-it)
      (n-e (arm-add n-x11 n-base reg))
      (n-e (arm-ldur n-x15 n-x11 (n-field-off 1)))
      (n-e (arm-and-low n-x13 n-x15 3))
      (n-e (arm-cmp-imm n-x13 n-tag-trailer))
      (n-b-cond 1 not-it)
      (n-e (arm-sub n-x14 n-x11 n-x15))
      (n-e (arm-ldur n-x14 n-x14 -7))
      (n-e (arm-ubfx n-x14 n-x14 3 8))
      (n-e (arm-cmp-imm n-x14 n-kind-closure))
      (n-b-cond 1 not-it))))

(define n-save (subr (maxeff assembles spin) () unit)
  (lambda ()
    (begin
      (n-e (arm-str n-cur n-st n-st-cur))
      (n-e (arm-add n-x13 n-base n-cur))
      (n-e (arm-sub-imm n-x13 n-x13 4))
      (n-e (arm-sub n-x13 n-x13 n-ip))
      (n-e (arm-str n-x13 n-st n-st-d))
      (n-e (arm-str n-dsp n-st n-st-dsp))
      (n-e (arm-str n-rsp n-st n-st-rsp))
      (n-e (arm-str n-fuel n-st n-st-fuel))
      (n-fp-encode n-x13)
      (n-e (arm-str n-x13 n-st n-st-fp))
      (n-e (arm-str n-clo n-st n-st-clo)))))

(define n-load (subr (maxeff assembles spin) () unit)
  (lambda ()
    (begin
      (n-e (arm-ldr n-base n-st n-st-base))
      (n-e (arm-ldr n-cur n-st n-st-cur))
      (n-e (arm-ldr n-x13 n-st n-st-d))
      (n-e (arm-add n-ip n-base n-cur))
      (n-e (arm-sub-imm n-ip n-ip 4))
      (n-e (arm-sub n-ip n-ip n-x13))
      (n-e (arm-ldr n-dsp n-st n-st-dsp))
      (n-e (arm-ldr n-rsp n-st n-st-rsp))
      (n-e (arm-ldr n-table n-st n-st-table))
      (n-e (arm-ldr n-fuel n-st n-st-fuel))
      (n-e (arm-ldr n-clo n-st n-st-clo))
      (n-e (arm-ldr n-x14 n-st n-st-fp))
      (n-fp-decode n-x14))))

(define n-fuel-check (subr (maxeff assembles spin) () unit)
  (lambda () (begin (n-e (arm-subs-imm n-fuel n-fuel 1)) (n-trap-if 0 n-trap-out-of-fuel 0))))
;; A taken branch's poll: only a backward one can make a loop, so a branch
;; known to go forward (in a compiled word) makes none.
(define n-fuel-unless-forward (subr (maxeff assembles spin) () unit)
  (lambda () (if (> (get n-target-cell) (get n-at)) #u (n-fuel-check))))
(define n-ds-limit (subr (maxeff assembles spin) () unit)
  (lambda ()
    (begin
      (n-e (arm-ldr n-x13 n-st n-st-ds-limit))
      (n-e (arm-cmp n-dsp n-x13))
      (n-trap-if 3 n-trap-stack-overflow 0))))
(define n-rs-limit (subr (maxeff assembles spin) () unit)
  (lambda ()
    (begin
      (n-e (arm-ldr n-x13 n-st n-st-rs-limit))
      (n-e (arm-cmp n-rsp n-x13))
      (n-trap-if 9 n-trap-too-deep 0))))

(define n-callout (subr (maxeff assembles spin) (int) unit)
  (lambda (n)
    (begin
      (n-save)
      (n-e (arm-mov 0 n-st))
      (n-e (arm-movz 1 n 0))
      (n-e (arm-ldr n-x16 n-st n-st-callout))
      (n-e (arm-blr n-x16))
      (n-cbnz 0 (get n-exit-common))
      (n-load)
      (if (n-control? n) (n-enter-cur n-x13) (n-cont-code)))))

(define n-two-fixnums (subr (maxeff assembles spin) (int) unit)
  (lambda (n)
    (begin
      (n-e (arm-ldp n-x13 n-x14 n-dsp 0))
      (n-e (arm-orr n-x15 n-x13 n-x14))
      (n-e (arm-tst-low n-x15 3))
      (n-trap-if 1 n-trap-type n))))

(define n-check-tag (subr (maxeff assembles spin) (int int int int) unit)
  (lambda (reg tag code detail)
    (begin
      (n-e (arm-and-low n-x13 reg 3))
      (n-e (arm-cmp-imm n-x13 tag))
      (n-trap-if 1 code detail))))

(define n-execute (subr (maxeff assembles spin) () unit)
  (lambda ()
    (let ((is-ref (n-label)) (bad (n-label)))
      (begin
        (n-e (arm-ldr-post n-w n-dsp 8))
        (n-e (arm-tst-low n-w 3))
        (n-b-cond 1 is-ref)
        (n-cbz n-w bad)
        (n-e (arm-cmp-imm n-w (* 8 n-primitives)))
        (n-b-cond 2 bad)
        (n-e (arm-ldr-reg n-x10 n-table n-w))
        (n-e (arm-br n-x10))
        (n-bind bad)
        (n-e (arm-movz n-x13 n-trap-no-routine 0))
        (n-e (arm-asr-imm n-x14 n-w 3))
        (n-b (get n-trap-common))
        (n-bind is-ref)
        (n-check-tag n-w n-tag-bloblet n-trap-not-a-word 0)
        (n-e (arm-add n-x11 n-base n-w))
        (n-e (arm-ldur n-x15 n-x11 (n-field-off 1)))
        (n-check-tag n-x15 n-tag-trailer n-trap-not-a-word 0)
        (n-e (arm-sub n-x14 n-x11 n-x15))
        (n-e (arm-ldur n-x14 n-x14 -7))
        (n-e (arm-ubfx n-x14 n-x14 3 8))
        (n-e (arm-cmp-imm n-x14 n-kind-word))
        (n-trap-if 1 n-trap-not-a-word 0)
        (n-run-word-in-w)))))

(define n-field-ref (subr (maxeff assembles spin) (int) unit)
  (lambda (n)
    (let ((slow (n-label)))
      (begin
        (n-e (arm-ldp n-x15 n-x14 n-dsp 0))
        (n-e (arm-tst-low n-x15 3))
        (n-trap-if 1 n-trap-type n)
        (n-check-tag n-x14 n-tag-bloblet n-trap-type n)
        (n-e (arm-add n-x11 n-base n-x14))
        (n-e (arm-ldur n-x16 n-x11 (n-field-off 1)))
        (n-e (arm-and-low n-x13 n-x16 3))
        (n-e (arm-cmp-imm n-x13 n-tag-trailer))
        (n-b-cond 1 slow)
        (n-e (arm-cmp-imm n-x15 16))
        (n-trap-if 11 n-trap-field n)
        (n-e (arm-sub-imm n-x16 n-x16 n-tag-trailer))
        (n-e (arm-cmp n-x15 n-x16))
        (n-trap-if 12 n-trap-field n)
        (n-e (arm-sub n-x16 n-x11 n-x15))
        (n-e (arm-ldur n-x15 n-x16 -4))
        (n-e (arm-str-pre n-x15 n-dsp 8))
        (n-cont-code)
        (n-bind slow)
        (n-callout n)))))

(define n-free (subr (maxeff assembles spin) (int) unit)
  (lambda (n)
    (let ((bad (n-label)))
      (begin
        (n-e (arm-ldr-post n-x10 n-ip -8))
        (n-is-closure n-clo bad)
        (n-e (arm-add-imm n-x10 n-x10 (* 8 n-closure-free0)))
        (n-e (arm-sub-imm n-x16 n-x15 n-tag-trailer))
        (n-e (arm-cmp n-x10 n-x16))
        (n-b-cond 12 bad)
        (n-e (arm-sub n-x14 n-x11 n-x10))
        (n-e (arm-ldur n-x15 n-x14 -4))
        (n-e (arm-str-pre n-x15 n-dsp -8))
        (n-cont-code)
        (n-bind bad)
        (n-e (arm-movz n-x13 n-trap-field 0))
        (n-e (arm-movz n-x14 n 0))
        (n-b (get n-trap-common))))))

;; A typed call's callee is a closure, so it is not tested; and a typed
;; tail call, which grows neither stack, does not check them.
(define n-call (subr (maxeff assembles spin) (int) unit)
  (lambda (n)
    (let ((other (n-label))
          (typed (or (= n routine-tcall) (= n routine-ttailcall)))
          (tail (or (= n routine-tailcall) (= n routine-ttailcall))))
      (begin
        (n-e (arm-ldr n-w n-dsp 0))
        (if typed #u (n-is-closure n-w other))
        (n-fuel-check)
        (if (and typed tail) #u (begin (n-ds-limit) (n-rs-limit)))
        (n-e (arm-ldr-post n-x10 n-ip -8))
        (n-e (arm-add-imm n-dsp n-dsp 8))
        (if (not tail)
            (begin
              (n-push-return)
              (n-e (arm-add n-x14 n-dsp n-x10))
              (n-e (arm-sub-imm n-fp n-x14 8)))
            (let ((top (n-label)) (done (n-label)))
              (begin
                (n-e (arm-add n-x14 n-dsp n-x10))
                (n-e (arm-sub-imm n-x14 n-x14 8))
                (n-e (arm-mov n-x15 n-fp))
                (n-e (arm-mov n-x16 n-x10))
                (n-bind top)
                (n-cbz n-x16 done)
                (n-e (arm-ldr-post n-x10 n-x14 -8))
                (n-e (arm-str-post n-x10 n-x15 -8))
                (n-e (arm-sub-imm n-x16 n-x16 8))
                (n-b top)
                (n-bind done)
                (n-e (arm-add-imm n-dsp n-x15 8)))))
        (n-e (arm-mov n-clo n-w))
        (n-e (arm-add n-x11 n-base n-w))
        (n-e (arm-ldur n-cur n-x11 (n-field-off n-closure-word)))
        (n-e (arm-add n-ip n-base n-cur))
        (n-e (arm-sub-imm n-ip n-ip (+ 4 (* 8 n-word-cell0))))
        (n-e (arm-movz n-x13 (* 8 n-word-cell0) 0))
        (n-enter-cur n-x13)
        (n-bind other)
        (if typed #u (n-callout n))))))

;;; ------------------------------------------------------------ routines

;; `x13` = top, `x14` = the one below; to `slow` unless both are fixnums.
(define n-both-fixnums (subr (maxeff assembles spin) (int) unit)
  (lambda (slow)
    (begin
      (n-e (arm-ldp n-x13 n-x14 n-dsp 0))
      (n-e (arm-orr n-x15 n-x13 n-x14))
      (n-e (arm-tst-low n-x15 3))
      (n-b-cond 1 slow))))
;; `int-add` or `int-sub` (routine `n`) on two fixnums; the Rust machine's on a bignum, or past a
;; fixnum.
(define n-int-arith (subr (maxeff assembles spin) (int) unit)
  (lambda (n)
    (let ((slow (n-label)))
      (begin
        (n-both-fixnums slow)
        (n-e (if (= n routine-int-add) (arm-adds n-x15 n-x14 n-x13) (arm-subs n-x15 n-x14 n-x13)))
        (n-b-cond 6 slow)
        (n-e (arm-str-pre n-x15 n-dsp 8))
        (n-cont-code)
        (n-bind slow)
        (n-callout n)))))
;; `int-less` or `int-eq` (routine `n`) on two fixnums; the Rust machine's on a bignum.
(define n-int-compare (subr (maxeff assembles spin) (int) unit)
  (lambda (n)
    (let ((slow (n-label)))
      (begin
        (n-both-fixnums slow)
        (n-e (arm-cmp n-x14 n-x13))
        (n-value n-x16 n-true)
        (n-value n-x15 n-false)
        (n-e (arm-csel n-x15 n-x16 n-x15 (if (= n routine-int-less) 11 0)))
        (n-e (arm-str-pre n-x15 n-dsp 8))
        (n-cont-code)
        (n-bind slow)
        (n-callout n)))))
;; Routine `n`'s code, going on to the next cell's.
(define n-routine (subr (maxeff assembles spin) (int) unit)
  (lambda (n)
    (cond
      ((= n routine-docol)
       (begin
         (n-fuel-check) (n-ds-limit) (n-rs-limit) (n-push-return)
         (n-e (arm-mov n-cur n-w))
         (n-e (arm-sub-imm n-ip n-x11 (+ 4 (* 8 n-word-cell0))))
         (n-next)))
      ((= n routine-exit) (n-pop-return))
      ((= n routine-halt) (n-b (get n-exit-common)))
      ((= n routine-lit)
       (begin (n-e (arm-ldr-post n-x13 n-ip -8)) (n-e (arm-str-pre n-x13 n-dsp -8)) (n-cont-code)))
      ((= n routine-branch)
       (begin
         (if (< (get n-target) 0) (n-e (arm-ldr-post n-x13 n-ip -8)) #u)
         (n-branch-ip) (n-fuel-unless-forward) (n-ds-limit)
         (if (< (get n-target) 0) (n-next) (n-b (get n-target)))))
      ((= n routine-zbranch)
       (let ((skip (n-label)))
         (begin
           (n-e (arm-ldr-post n-x14 n-dsp 8))
           (n-e (arm-ldr-post n-x13 n-ip -8))
           (n-value n-x15 n-false)
           (n-e (arm-cmp n-x14 n-x15))
           (n-b-cond 1 skip)
           (n-branch-ip)
           (n-fuel-unless-forward) (n-ds-limit)
           (if (< (get n-target) 0)
               (begin (n-bind skip) (n-next))
               (begin (n-b (get n-target)) (n-bind skip) (n-cont-code))))))
      ((= n routine-execute) (n-execute))
      ((= n routine-dup)
       (begin
         (n-e (arm-ldr n-x13 n-dsp 0))
         (n-e (arm-str-pre n-x13 n-dsp -8))
         (n-cont-code)))
      ((= n routine-drop) (begin (n-e (arm-add-imm n-dsp n-dsp 8)) (n-cont-code)))
      ((= n routine-swap)
       (begin
         (n-e (arm-ldp n-x13 n-x14 n-dsp 0))
         (n-e (arm-stp n-x14 n-x13 n-dsp 0))
         (n-cont-code)))
      ((= n routine-over)
       (begin
         (n-e (arm-ldr n-x13 n-dsp 8))
         (n-e (arm-str-pre n-x13 n-dsp -8))
         (n-cont-code)))
      ((or (= n routine-add) (= n routine-sub))
       (begin
         (n-two-fixnums n)
         (n-e (if (= n routine-add) (arm-adds n-x15 n-x14 n-x13) (arm-subs n-x15 n-x14 n-x13)))
         (n-trap-if 6 n-trap-overflow n)
         (n-e (arm-str-pre n-x15 n-dsp 8))
         (n-cont-code)))
      ((or (= n routine-less) (= n routine-eq))
       (begin
         (if (= n routine-less) (n-two-fixnums n) (n-e (arm-ldp n-x13 n-x14 n-dsp 0)))
         (n-e (arm-cmp n-x14 n-x13))
         (n-value n-x16 n-true)
         (n-value n-x15 n-false)
         (n-e (arm-csel n-x15 n-x16 n-x15 (if (= n routine-less) 11 0)))
         (n-e (arm-str-pre n-x15 n-dsp 8))
         (n-cont-code)))
      ((or (= n routine-car) (= n routine-cdr))
       (begin
         (n-e (arm-ldr n-x15 n-dsp 0))
         (n-check-tag n-x15 n-tag-pair n-trap-type n)
         (n-e (arm-add n-x14 n-base n-x15))
         (n-e (arm-ldur n-x15 n-x14 (if (= n routine-car) -1 7)))
         (n-e (arm-str n-x15 n-dsp 0))
         (n-cont-code)))
      ;; Typed: the checker has proved the operands ints. Fixnums here; a bignum, or a sum past a
      ;; fixnum, the Rust machine's (PLAN.md, Q2).
      ((or (= n routine-int-add) (= n routine-int-sub)) (n-int-arith n))
      ((or (= n routine-int-less) (= n routine-int-eq)) (n-int-compare n))
      ;; A list may be `nil`: `car` of it traps, as the Rust machine's does.
      ((or (= n routine-pair-car) (= n routine-pair-cdr))
       (begin
         (n-e (arm-ldr n-x15 n-dsp 0))
         (n-check-tag n-x15 n-tag-pair n-trap-type n)
         (n-e (arm-add n-x14 n-base n-x15))
         (n-e (arm-ldur n-x15 n-x14 (if (= n routine-pair-car) -1 7)))
         (n-e (arm-str n-x15 n-dsp 0))
         (n-cont-code)))
      ((= n routine-field)
       (begin
         (n-e (arm-ldr-post n-x13 n-ip -8))
         (n-e (arm-ldr n-x14 n-dsp 0))
         (n-e (arm-add n-x11 n-base n-x14))
         (n-e (arm-sub n-x16 n-x11 n-x13))
         (n-e (arm-ldur n-x15 n-x16 -4))
         (n-e (arm-str n-x15 n-dsp 0))
         (n-cont-code)))
      ((= n routine-field-ref) (n-field-ref n))
      ((or (= n routine-slot) (= n routine-slot!))
       (begin
         (n-e (arm-ldr-post n-x13 n-ip -8))
         (n-e (arm-sub n-x14 n-fp n-x13))
         (if (= n routine-slot!) (n-e (arm-ldr-post n-x15 n-dsp 8)) #u)
         (n-e (arm-cmp n-x14 n-dsp))
         (n-trap-if 3 n-trap-field n)
         (if (= n routine-slot)
             (begin (n-e (arm-ldr n-x15 n-x14 0)) (n-e (arm-str-pre n-x15 n-dsp -8)))
             (n-e (arm-str n-x15 n-x14 0)))
         (n-cont-code)))
      ((= n routine-free) (n-free n))
      ((or (= n routine-global) (= n routine-global!))
       (begin
         (n-e (arm-ldr-post n-x13 n-ip -8))
         (n-e (arm-add n-x11 n-base n-x13))
         (if (= n routine-global)
             (begin (n-e (arm-ldur n-x15 n-x11 (n-field-off 2))) (n-e (arm-str-pre n-x15 n-dsp -8)))
             (begin
               (n-e (arm-ldr-post n-x15 n-dsp 8))
               (n-e (arm-stur n-x15 n-x11 (n-field-off 2)))
               (n-card-mark n-x11 (n-field-off 2))))
         (n-cont-code)))
      ((or (= n routine-call) (= n routine-tailcall) (= n routine-tcall) (= n routine-ttailcall))
       (n-call n))
      ((= n routine-return)
       (begin
         (n-e (arm-ldr-post n-x15 n-dsp 8))
         (n-e (arm-add-imm n-x14 n-fp 8))
         (n-e (arm-cmp n-dsp n-x14))
         (n-trap-if 8 n-trap-underflow n)
         (n-e (arm-mov n-dsp n-fp))
         (n-e (arm-str n-x15 n-dsp 0))
         (n-pop-return)))
      (else (n-callout n)))))

;;; ------------------------------------------------------------ words

;; Where each instruction of `w`'s cells starts: for cell i, whether one
;; does, in an array, marked from cell `i` on: a loop, stepping from each
;; instruction to the next.
(define n-mark-starts (subr n-writes (n-bools tword int int) unit)
  (lambda (a w i n)
    (if (>= i n)
        #u
        ;; The cell's routine takes its operands' cells after it.
        (let* ((k (+ n-word-cell0 i))
               (width (if (tword-int? w k) (+ 1 (n-operands (tword-int w k))) 1)))
          (begin
            (array-set! a i #t)
            (n-mark-starts a w (+ i width) n))))))
(define n-starts (subr (maxeff n-writes (alloc @k)) (tword int) n-bools)
  (lambda (w n)
    (let ((a (the (arrayof bool @k) (make-array (+ n 1) #f))))
      (begin (n-mark-starts a w 0 n) a))))
(define n-fill-labels (subr (maxeff assembles spin) ((arrayof int @k) int) unit)
  (lambda (a i)
    (if (= i (array-length a))
        #u
        (begin (array-set! a i (n-label))
               (n-fill-labels a (+ i 1))))))
(define n-labels-for (subr (maxeff assembles spin) (int) (arrayof int @k))
  (lambda (n)
    (let ((a (the (arrayof int @k) (make-array n 0))))
      (begin (n-fill-labels a 0) a))))
;; Where each of cells 0 to `i` starts in the code, or -1, onto `acc`: a
;; loop, from the last cell down.
(define n-starts-at (subr n-lists (int n-bools n-ints n-instrs) n-instrs)
  (lambda (i starts labels acc)
    (if (< i 0)
        acc
        (let ((start (if (array-ref starts i) (array-ref (get n-labels) (array-ref labels i)) -1)))
          (n-starts-at (- i 1) starts labels (cons start acc))))))

;; The cell after `i` where an instruction starts, or `n`.
(define n-next-start (subr (maxeff (read @globals) (read @k)) (int int (arrayof bool @k)) int)
  (lambda (i n starts) (if (or (>= i n) (array-ref starts i)) i (n-next-start (+ i 1) n starts))))

(define n-cells (subr (maxeff assembles spin) (tword int int n-bools n-ints int) unit)
  (lambda (w i n starts labels far-exit)
    (if (= i n)
        #u
        (begin
          (if (array-ref starts i)
              (let ((near-exit (n-label)) (k (+ n-word-cell0 i)))
                (begin
                  (n-bind (array-ref labels i))
                  (set n-exit-common near-exit)
                  (if (tword-int? w k)
                      (let* ((r (tword-int w k))
                             (next (n-next-start (+ i 1) n starts)))
                        (begin
                          (set n-cont (if (< next n) (array-ref labels next) -1))
                          (set n-target-cell
                               (if (or (= r routine-branch) (= r routine-zbranch))
                                   (+ (+ i 2) (tword-int w (+ k 1)))
                                   -1))
                          (set n-target
                               (if (< (get n-target-cell) 0)
                                   -1
                                   (array-ref labels (get n-target-cell))))
                          (set n-at i)
                          (n-e (arm-sub-imm n-ip n-ip 8))
                          (n-routine r)))
                      (begin
                        (set n-cont -1)
                        (set n-target -1)
                        (set n-target-cell -1)
                        (n-e (arm-ldr-post n-w n-ip -8))
                        (n-run-word-in-w)))
                  (n-flush-stubs)
                  (n-bind near-exit)
                  (n-b far-exit)))
              #u)
          (n-cells w (+ i 1) n starts labels far-exit)))))

;; `w`'s cells as machine code, for a place from which the machine's common
;; trap and exit are `far-trap` and `far-exit` instructions away: the code,
;; and where each cell's code starts, or -1. What `assemble_word` makes.
(define native-assemble (subr (maxeff assembles spin) (tword int int) n-assembled)
  (lambda (w far-trap far-exit)
    (begin
      (n-reset)
      (let* ((cells (- (+ (tword-fields w) 1) n-word-cell0))
             (starts (n-starts w cells))
             (labels (n-labels-for (+ cells 1)))
             (far-exit-label (get n-exit-common)))
        (begin
          (n-fuel-check) (n-ds-limit) (n-rs-limit) (n-push-return)
          (n-e (arm-mov n-cur n-w))
          (n-e (arm-sub-imm n-ip n-x11 (+ 4 (* 8 n-word-cell0))))
          (n-b (array-ref labels 0))
          (n-flush-stubs)
          (n-cells w 0 cells starts labels far-exit-label)
          (set n-exit-common far-exit-label)
          ;; The machine's common trap and exit, through the state: no
          ;; branch leaves this code, so it may be placed anywhere, and run
          ;; by any machine. `far-trap` and `far-exit` are no longer needed.
          (n-bind (get n-trap-common))
          (n-e (arm-ldr n-x16 n-st n-st-trap))
          (n-e (arm-br n-x16))
          (n-bind far-exit-label)
          (n-e (arm-ldr n-x16 n-st n-st-exit))
          (n-e (arm-br n-x16))
          (let ((at (n-starts-at (- cells 1) starts labels nil)))
            (product (1 (n-finish)) (2 at))))))))))

(define-effect assembles (select native-module assembles))
(define native-assemble (with native-module native-assemble))
