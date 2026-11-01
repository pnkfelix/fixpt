;;; The assembler of the native convention's compiler to arm64 written in
;;; FX-26, and the machine sequences its files share: `direct.rs`'s `Asm`
;;; and its free functions of no procedure, step for step, over the encoder
;;; written in FX-26 (`arm64.fx`) and what the convention's generator says
;;; of it (`native-direct-arm64-layout.fx`). Its steps have the Rust names,
;;; with `ada-` before them (`ada-push-frame` is `push_frame`).
;;;
;;; Besides `Asm`'s instructions and labels it keeps what the Rust compiler
;;; keeps beside them as it compiles a procedure: the call-outs it numbers
;;; (from the machine's count, `ada-reset`), the traps to place after the
;;; code (`stubs`), and the first reason it cannot compile ("" for none).
;;;
;;; A file of one expression (`load-input`, `TODO.md` §68): what makes the
;;; module, which the conductor applies to the encoder and the layout.

(let* ((direct-types (load-module "fx26:native-direct-x64-types.fx"))
       (arm-direct-types (load-module "fx26:native-direct-arm64-types.fx"))
       (layout-types (load-module "fx26:native-direct-arm64-layout-types.fx"))
       (arm64-types (load-module "fx26:arm64-types.fx")))
  (lambda ((arm (select arm64-types arm64-direct-sig))
           (dl (select layout-types native-direct-arm64-layout-sig)))
    (module
(hide (include direct-types) (include arm-direct-types))
(hide (include arm) (include dl))

;; Conditions, by the hardware's numbers.
(define ada-c-eq int 0)
(define ada-c-ne int 1)
(define ada-c-hs int 2)
(define ada-c-lo int 3)
(define ada-c-mi int 4)
(define ada-c-vs int 6)
(define ada-c-vc int 7)
(define ada-c-hi int 8)
(define ada-c-ls int 9)
(define ada-c-ge int 10)
(define ada-c-lt int 11)
(define ada-c-gt int 12)
(define ada-c-le int 13)
;; Condition `c` the other way (`Cond::not`).
(define ada-not (subr pure (int) int)
  (lambda (c) (if (= (modulo c 2) 0) (+ c 1) (- c 1))))
;; A branch's kind (`Fix`): `b.cond` is its condition's number.
(define ada-fix-b int 16)
(define ada-fix-bl int 17)
(define ada-fix-adr int 32)

;; `v` as 64 bits, as `as u64` has it.
(define ada-bits (subr pure (int) int) (lambda (v) (modulo v 18446744073709551616)))
;; The bits of fixnum `n` (`Value::fixnum(n).raw()`).
(define ada-fixnum (subr pure (int) int) (lambda (n) (ada-bits (* 8 n))))

;;; ------------------------------------------------------------ the assembler
;;; Instructions, and labels patched when everything is placed: a label is
;;; where it is, in instructions from the start, -1 until placed.

(define ada-code (ref da-ints @k) (new (make-array 8192 0)))
(define ada-len (ref int @k) (new 0))
(define ada-labels (ref da-ints @k) (new (make-array 1024 -1)))
(define ada-nlabels (ref int @k) (new 0))
;; Each branch to patch: where it is, and its label and kind
;; (`8192 label + kind`); newest first.
(define ada-fixups (ref da-pairs @k) (new nil))
;; A field loaded from further than `ldr`'s 19 bits reach (`too_far`).
(define ada-far (ref bool @k) (new #f))
;; The call-outs numbered, newest first, from `ada-base`; the traps to
;; place, newest first (label, code); and why not, if not.
(define ada-base (ref int @k) (new 0))
(define ada-made (ref da-bytes @k) (new nil))
(define ada-nmade (ref int @k) (new 0))
(define ada-stubs (ref da-pairs @k) (new nil))
(define ada-why (ref string @k) (new ""))
;; Each load of a call-out's number from its field (`ada-call-out`),
;; newest first: where it is, and the call-out's number, its field not yet
;; given.
(define ada-callout-loads (ref da-pairs @k) (new nil))

(define ada-copy-ints (subr da-assembles (da-ints da-ints int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (ada-copy-ints from to (+ i 1))))))

;; A procedure begins, its call-outs numbered from `base`.
(define ada-reset (subr da-assembles (int) unit)
  (lambda (base)
    (begin
      (set ada-len 0)
      (set ada-nlabels 0)
      (set ada-fixups nil)
      (set ada-far #f)
      (set ada-base base)
      (set ada-made nil)
      (set ada-nmade 0)
      (set ada-stubs nil)
      (set ada-callout-loads nil)
      (set ada-why ""))))

;; How many instructions so far.
(define ada-here (subr da-reads () int) (lambda () (get ada-len)))

;; An instruction.
(define ada-e (subr da-assembles (int) unit)
  (lambda (w)
    (let ((n (get ada-len)))
      (begin
        (if (= n (array-length (get ada-code)))
            (let ((bigger (the da-ints (make-array (* 2 n) 0))))
              (begin (ada-copy-ints (get ada-code) bigger 0) (set ada-code bigger)))
            #u)
        (array-set! (get ada-code) n w)
        (set ada-len (+ n 1))))))
;; Instructions, in order.
(define ada-es (subr da-assembles (da-bytes) unit)
  (lambda (ws) (if (null? ws) #u (begin (ada-e (car ws)) (ada-es (cdr ws))))))
(define ada-word-at (subr da-reads (int) int) (lambda (i) (array-ref (get ada-code) i)))
(define ada-set-word! (subr da-assembles (int int) unit)
  (lambda (i w) (array-set! (get ada-code) i w)))

(define ada-label (subr da-assembles () int)
  (lambda ()
    (let ((n (get ada-nlabels)))
      (begin
        (if (= n (array-length (get ada-labels)))
            (let ((more (the da-ints (make-array (* 2 n) -1))))
              (begin (ada-copy-ints (get ada-labels) more 0) (set ada-labels more)))
            #u)
        (array-set! (get ada-labels) n -1)
        (set ada-nlabels (+ n 1))
        n))))
;; Label `l` here.
(define ada-bind (subr da-assembles (int) unit)
  (lambda (l) (array-set! (get ada-labels) l (get ada-len))))
;; Where label `l` is, in instructions, or -1 if it was never placed.
(define ada-label-at (subr da-reads (int) int)
  (lambda (l) (array-ref (get ada-labels) l)))

;; A fixup's label and kind.
(define ada-fix-label (subr pure (int) int) (lambda (lk) (quotient lk 8192)))
(define ada-fix-kind (subr pure (int) int) (lambda (lk) (modulo lk 8192)))
;; Whether a branch so far goes to `l`.
(define ada-used-in? (subr da-reads (da-pairs int) bool)
  (lambda (fs l)
    (cond ((null? fs) #f)
          ((= (ada-fix-label (extract (car fs) 2)) l) #t)
          (else (ada-used-in? (cdr fs) l)))))
(define ada-used? (subr da-reads (int) bool) (lambda (l) (ada-used-in? (get ada-fixups) l)))

;; A branch of kind `f` to `l`, a `nop` until it is patched.
(define ada-to (subr da-assembles (int int) unit)
  (lambda (l f)
    (begin
      (set ada-fixups (cons (product (1 (get ada-len)) (2 (+ (* 8192 l) f))) (get ada-fixups)))
      (ada-e arm-nop))))
(define ada-b (subr da-assembles (int) unit) (lambda (l) (ada-to l ada-fix-b)))
(define ada-bl (subr da-assembles (int) unit) (lambda (l) (ada-to l ada-fix-bl)))
;; `b.c l`.
(define ada-bc (subr da-assembles (int int) unit) (lambda (c l) (ada-to l c)))
;; `adr r, l`.
(define ada-adr (subr da-assembles (int int) unit) (lambda (r l) (ada-to l (+ ada-fix-adr r))))
;; Refused at `ada-finish` (`too_far`).
(define ada-too-far! (subr da-assembles () unit) (lambda () (set ada-far #t)))

;; Why the procedure cannot be compiled: the first reason.
(define ada-fail (subr da-assembles (string) unit)
  (lambda (m) (if (string=? (get ada-why) "") (set ada-why m) #u)))
(define ada-err (subr da-reads () string) (lambda () (get ada-why)))
(define ada-ok? (subr da-reads () bool) (lambda () (string=? (get ada-why) "")))

;; What a branch or load out of reach says.
(define ada-too-far (subr da-reads () string)
  (lambda ()
    (string-append "its code, "
                   (string-append (int->string (get ada-len))
                                  (string-append " instructions, is too long for a branch"
                                                 " or load to reach across")))))
;; The first fixup of `fs` (oldest first) out of reach or to no place, said.
(define ada-reach (subr da-assembles (da-pairs) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (let* ((at (extract (car fs) 1)) (lk (extract (car fs) 2))
               (to (array-ref (get ada-labels) (ada-fix-label lk))) (f (ada-fix-kind lk))
               (reach (if (or (= f ada-fix-b) (= f ada-fix-bl)) 33554432 262144)))
          (cond ((< to 0) (ada-fail "a label never placed"))
                ((or (< (- to at) (- 0 reach)) (>= (- to at) reach)) (ada-fail (ada-too-far)))
                (else (ada-reach (cdr fs))))))))
;; The fixups, oldest first: a branch to a `ret` is that `ret` (a fast path
;; that joins the slow one only to return).
(define ada-patch (subr da-assembles (da-pairs) unit)
  (lambda (fs)
    (if (null? fs)
        #u
        (let* ((at (extract (car fs) 1)) (lk (extract (car fs) 2))
               (to (array-ref (get ada-labels) (ada-fix-label lk))) (f (ada-fix-kind lk))
               (d (- to at)))
          (begin
            (ada-set-word! at
              (cond ((and (= f ada-fix-b) (= (ada-word-at to) arm-ret)) arm-ret)
                    ((= f ada-fix-b) (arm-b d))
                    ((= f ada-fix-bl) (arm-bl d))
                    ((>= f ada-fix-adr) (arm-adr (- f ada-fix-adr) d))
                    (else (arm-b-cond f d))))
            (ada-patch (cdr fs)))))))
;; An instruction's four bytes, lowest first, before `acc`.
(define ada-word-bytes (subr da-assembles (int da-bytes) da-bytes)
  (lambda (w acc)
    (cons (modulo w 256)
          (cons (modulo (quotient w 256) 256)
                (cons (modulo (quotient w 65536) 256) (cons (quotient w 16777216) acc))))))
(define ada-list (subr da-assembles (int da-bytes) da-bytes)
  (lambda (i acc)
    (if (< i 0) acc (ada-list (- i 1) (ada-word-bytes (array-ref (get ada-code) i) acc)))))
;; The code, as bytes (`finish`, then `arm64::bytes`); or why not
;; (`ada-err`): too long for a branch or load to reach across, or a label
;; never placed.
(define ada-finish (subr da-assembles () da-bytes)
  (lambda ()
    (let ((fs (the da-pairs (reverse (get ada-fixups)))))
      (begin
        (if (get ada-far) (ada-fail (ada-too-far)) (ada-reach fs))
        (if (ada-ok?) (ada-patch fs) #u)
        (set ada-fixups nil)
        (if (ada-ok?) (ada-list (- (get ada-len) 1) nil) nil)))))

;; Where the assembler is, to come back to (`ada-rewind`): code emitted
;; after it measured, then taken back. Its length, labels and fixups.
(define ada-mark (subr da-reads () da-mark)
  (lambda () (product (1 (get ada-len)) (2 (get ada-nlabels)) (3 (get ada-fixups)) (4 0))))
(define ada-rewind (subr da-assembles (da-mark) unit)
  (lambda (m)
    (begin
      (set ada-len (extract m 1))
      (set ada-nlabels (extract m 2))
      (set ada-fixups (extract m 3)))))

;; A call-out's code (`fx::callout_code`): of kind `kind` (`d-co-…`), its
;; operands `a` and `b`.
(define ada-co (subr pure (int int int) int)
  (lambda (kind a b) (+ kind (* 32 (+ a (* 4096 b))))))
;; Call-out `code` numbered: its number.
(define ada-callout (subr da-assembles (int) int)
  (lambda (code)
    (let ((n (+ (get ada-base) (get ada-nmade))))
      (begin (set ada-made (cons code (get ada-made))) (set ada-nmade (+ 1 (get ada-nmade))) n))))
;; Those numbered, oldest first.
(define ada-callouts (subr da-assembles () da-bytes)
  (lambda () (the da-bytes (reverse (get ada-made)))))

;; A trap of `code` at label `l`, placed after the code (`stubs`).
(define ada-stub (subr da-assembles (int int) unit)
  (lambda (l code) (set ada-stubs (cons (product (1 l) (2 code)) (get ada-stubs)))))
;; To a trap of `code` where `c` holds, by a stub of its own (`trap_at`).
(define ada-trap (subr da-assembles (int int) unit)
  (lambda (code c) (let ((l (ada-label))) (begin (ada-stub l code) (ada-bc c l)))))

;; Whether a stub of `code` is among `ss`.
(define ada-stub-of? (subr da-reads (da-pairs int) bool)
  (lambda (ss code)
    (cond ((null? ss) #f)
          ((= (extract (car ss) 2) code) #t)
          (else (ada-stub-of? (cdr ss) code)))))
;; The traps, out of the way: a stub per site, calling its kind's stub,
;; which goes to the machine's common trap (`common_trap`).
(define ada-place-stubs (subr da-assembles () unit)
  (lambda ()
    (let ((kinds (the da-ints (make-array d-traps 0)))
          (ss (the da-pairs (reverse (get ada-stubs)))))
      (letrec ((labels (subr da-assembles (int) unit)
                 (lambda (k)
                   (if (= k d-traps) #u (begin (array-set! kinds k (ada-label)) (labels (+ k 1))))))
               (sites (subr da-assembles (da-pairs) unit)
                 (lambda (l)
                   (if (null? l)
                       #u
                       (begin (ada-bind (extract (car l) 1))
                              (ada-bl (array-ref kinds (extract (car l) 2)))
                              (sites (cdr l))))))
               (kind (subr da-assembles (int) unit)
                 (lambda (k)
                   (if (= k d-traps)
                       #u
                       (begin
                         (if (ada-stub-of? ss k)
                             (begin (ada-bind (array-ref kinds k))
                                    (ada-e (arm-movz d-x9 k 0))
                                    (ada-ld d-x16 d-st d-st-trap-stub)
                                    (ada-e (arm-br d-x16)))
                             #u)
                         (kind (+ k 1)))))))
        (begin (labels 0) (sites ss) (kind 1))))))

;;; ------------------------------------------------------------ sequences

;; `r` := the 64 bits of `v` (`mov_imm64`).
(define ada-imm (subr da-assembles (int int) unit)
  (lambda (r v) (ada-es (arm-mov-imm64 r (ada-bits v)))))
(define ada-ld (subr da-assembles (int int int) unit)
  (lambda (t n off) (ada-e (arm-ldr t n off))))
(define ada-sto (subr da-assembles (int int int) unit)
  (lambda (t n off) (ada-e (arm-str t n off))))
(define ada-mov (subr da-assembles (int int) unit) (lambda (d m) (ada-e (arm-mov d m))))

;; A frame of `size` bytes pushed (a multiple of 16, at most `MOST_FRAME`):
;; its link and `second` stored, `x29` at its link, its header word below.
;; Past one `sub`'s reach, its 4 KB pages first.
(define ada-push-frame (subr da-assembles (int int) unit)
  (lambda (second size)
    (let ((pages (quotient size 4096)) (rest (modulo size 4096)))
      (begin
        (if (> pages 0) (ada-e (arm-sub-imm-pages d-sp d-sp pages)) #u)
        (if (or (> rest 0) (= pages 0)) (ada-e (arm-sub-imm d-sp d-sp rest)) #u)
        (ada-e (arm-stp d-frame second d-sp 8))
        (ada-e (arm-add-imm d-frame d-sp 8))))))
;; The frame of `size` bytes on top popped: the link and return address
;; back.
(define ada-pop-frame (subr da-assembles (int) unit)
  (lambda (size)
    (let ((pages (quotient size 4096)) (rest (modulo size 4096)))
      (begin
        (ada-e (arm-ldp d-frame d-link d-sp 8))
        (if (> pages 0) (ada-e (arm-add-imm-pages d-sp d-sp pages)) #u)
        (if (or (> rest 0) (= pages 0)) (ada-e (arm-add-imm d-sp d-sp rest)) #u)))))

;; Back to Rust from anywhere on the native stack.
(define ada-leave (subr da-assembles () unit)
  (lambda ()
    (letrec ((pairs (subr da-assembles (int) unit)
               (lambda (i)
                 (if (= i 5)
                     #u
                     (let ((r (+ 19 (* 2 i))))
                       (begin (ada-e (arm-ldp r (+ r 1) d-sp (+ 16 (* 16 i)))) (pairs (+ i 1))))))))
      (begin
        (ada-ld d-x9 d-st d-st-rust-sp)
        (ada-e (arm-add-imm d-sp d-x9 0))
        (pairs 0)
        (ada-e (arm-ldp-post d-frame d-link d-sp 96))
        (ada-e arm-ret)))))

;; Where a call-out that does not return to its caller said to go: its
;; stack, frame and value, and there.
(define ada-resume (subr da-assembles () unit)
  (lambda ()
    (begin
      (ada-ld d-x9 d-st d-st-resume-sp)
      (ada-e (arm-add-imm d-sp d-x9 0))
      (ada-ld d-frame d-st d-st-resume-fp)
      (ada-ld d-result d-st d-st-resume-x0)
      (ada-ld d-x16 d-st d-st-resume-pc)
      (ada-e (arm-br d-x16)))))

;; Call-out `n`, its arguments in the state already: on Rust's stack, with
;; where the native frames are for its collections to find. Its number:
;; one of the machine's own as a constant; another from its field, a
;; call-out, given when the procedure is done (`ada-callout-field`).
(define ada-call-out (subr da-assembles (int) unit)
  (lambda (n)
    (begin
      (ada-sto d-frame d-st d-st-fp)
      (ada-e (arm-add-imm d-x9 d-sp 0))
      (ada-sto d-x9 d-st d-st-native-sp)
      (ada-ld d-x9 d-st d-st-rust-sp)
      (ada-e (arm-add-imm d-sp d-x9 0))
      (ada-mov 0 d-st)
      (if (< n d-own-callouts)
          (ada-imm 1 n)
          (begin (set ada-callout-loads
                      (cons (product (1 (get ada-len)) (2 n)) (get ada-callout-loads)))
                 (ada-e arm-nop)
                 (ada-e (arm-lsr-imm 1 1 d-callout-shift))))
      (ada-ld d-x16 d-st d-st-callout)
      (ada-e (arm-blr d-x16))
      (ada-ld d-x9 d-st d-st-native-sp)
      (ada-e (arm-add-imm d-sp d-x9 0))
      (ada-ld d-frame d-st d-st-fp))))
;; The loads of call-outs' numbers, oldest first.
(define ada-callout-loads-made (subr da-assembles () da-pairs)
  (lambda () (the da-pairs (reverse (get ada-callout-loads)))))
;; The load at `at` given field `k` (`callout_fields`).
(define ada-callout-field (subr da-assembles (int int) unit)
  (lambda (at k)
    (let ((d (- (* -2 k) at)))
      (if (< d -262144) (ada-too-far!) (ada-set-word! at (arm-ldr-lit 1 d))))))

;; `t` := field `k` of the code bloblet being made, PC-relatively
;; (`ldr_field`): field `k` is `8k` bytes before the code's first
;; instruction.
(define ada-ldr-field (subr da-assembles (int int) unit)
  (lambda (t k)
    (let ((d (- (* -2 k) (get ada-len))))
      (if (< d -262144)
          (begin (ada-too-far!) (ada-e arm-nop))
          (ada-e (arm-ldr-lit t d))))))

;; The state's trap tested after a call-out: a trap of a primitive failed
;; if one was set.
(define ada-trap-set (subr da-assembles () unit)
  (lambda ()
    (begin (ada-ld d-x9 d-st d-st-trap) (ada-e (arm-cmp-imm d-x9 0))
           (ada-trap d-prim-failed ada-c-ne))))

;; A call-out's arguments, registers, as `ada-pure-call` takes them.
(define ada-args1 (subr da-assembles (int) da-bytes) (lambda (a) (cons a nil)))
(define ada-args2 (subr da-assembles (int int) da-bytes)
  ;; cons-chain: in `@k`, the assembler's region, which `list` would not be
  (lambda (a b) (cons a (cons b nil))))
(define ada-args3 (subr da-assembles (int int int) da-bytes)
  ;; cons-chain: in `@k`, the assembler's region, which `list` would not be
  (lambda (a b c) (cons a (cons b (cons c nil)))))
;; Each pair kept around a pure call, and back (`pure_call`'s `pairs`):
;; (1, 2), (3, 4), (5, 6), (7, 8), (CLO, LINK), (RESULT, XZR).
(define ada-kept-pairs (subr da-assembles (bool) unit)
  (lambda (back)
    (letrec ((one (subr da-assembles (int int int) unit)
               (lambda (r1 r2 j)
                 (ada-e (if back (arm-ldp r1 r2 d-x16 (* 16 j)) (arm-stp r1 r2 d-x16 (* 16 j)))))))
      (begin
        (ada-e (arm-add-imm d-x16 d-st d-st-kept))
        (one 1 2 0) (one 3 4 1) (one 5 6 2) (one 7 8 3) (one d-clo d-link 4)
        (one d-result d-xzr 5)))))
;; Call-out `code`, which never collects, on `args` (registers, put in the
;; state), its value into `into`: `RESULT`, REG1…REG8, the closure and the
;; link kept in the state around it, as they are (raw or not: nothing
;; moves), and put back.
(define ada-pure-call (subr da-assembles (int da-bytes int) unit)
  (lambda (code args into)
    (let ((n (ada-callout code)))
      (letrec ((put (subr da-assembles (da-bytes int) unit)
                 (lambda (rs j)
                   (if (null? rs)
                       #u
                       (begin (ada-sto (car rs) d-st (+ d-st-args (* 8 j)))
                              (put (cdr rs) (+ j 1)))))))
        (begin
          (put args 0)
          (ada-kept-pairs #f)
          (ada-call-out n)
          (ada-mov d-x17 d-result)
          (ada-kept-pairs #t)
          (if (= into d-x17) #u (ada-mov into d-x17)))))))

;; Register `r` tested for a fixnum, to `general` if it is not one.
(define ada-check-fixnum (subr da-assembles (int int) unit)
  (lambda (r general) (begin (ada-e (arm-tst-low r 3)) (ada-bc ada-c-ne general))))

;; The card of the word at `obj + off` marked (`arm64::card_mark`), with
;; `t1` and `t2`.
(define ada-card-mark (subr da-assembles (int int int int) unit)
  (lambda (obj off t1 t2) (ada-es (arm-card-mark obj off d-st d-st-cards t1 t2))))

;; Where field `k` of a bloblet is from its reference (`field_off`).
(define ada-field-off (subr pure (int) int) (lambda (k) (- 0 (+ 4 (* 8 k)))))
;; A header of a kind, `fields` and `bytes`; a trailer `distance` back.
(define ada-header (subr pure (int int int) int)
  (lambda (kind fields bytes)
    (+ d-tag-header
       (+ (arithmetic-shift kind d-h-kind-lo)
          (+ (arithmetic-shift fields d-h-fields-lo) (arithmetic-shift bytes d-h-bytes-lo))))))
(define ada-trailer (subr pure (int) int)
  (lambda (distance) (+ d-tag-trailer (arithmetic-shift distance d-t-distance-lo))))

;; The continuation procedure's code, as `continuation_code`: in a frame of
;; its own it calls out (`n`) to put the continuation's frames back.
(define ada-continuation-code (subr da-assembles (int) da-bytes)
  (lambda (n)
    (begin
      (ada-reset 0)
      (ada-push-frame d-link d-stub-frame)
      (ada-sto 1 d-st d-st-args)
      (ada-sto d-clo d-st (+ d-st-args 8))
      (ada-call-out n)
      (let ((failed (ada-label)))
        (begin
          (ada-ld d-x9 d-st d-st-trap)
          (ada-e (arm-cmp-imm d-x9 0))
          (ada-bc ada-c-ne failed)
          (ada-resume)
          (ada-bind failed)
          (ada-sto d-fuel d-st d-st-fuel)
          (ada-leave)
          (ada-finish))))))

;; The labels a branch so far goes to (`a.fixups`' labels), by label.
(define ada-targets (subr da-assembles () da-bools)
  (lambda ()
    (let ((to (the da-bools (make-array (+ 1 (get ada-nlabels)) #f))))
      (letrec ((mark (subr da-assembles (da-pairs) unit)
                 (lambda (fs)
                   (if (null? fs)
                       #u
                       (begin (array-set! to (ada-fix-label (extract (car fs) 2)) #t)
                              (mark (cdr fs)))))))
        (begin (mark (get ada-fixups)) to)))))
)))
