;;; Every procedure's code runs (`docs/research/code-stubs.md`): a
;;; convention declared with `(code-always-runs)`, on arm64, and code made
;;; to it that calls the procedure it is given with no test of what it is,
;;; its code at its closure's field 2 plus the code distance: native code,
;;; or a stub that enters `foreign`. Given a primitive, a continuation, and
;;; a closure kept cellular. Where this machine runs no native code, the
;;; answers it would give. `made-code-x86_64/stubs.fx` is this on x86_64.
(define-convention arm64-native
  (target arm64)
  (registers
    (arguments x1 x2 x3 x4 x5 x6 x7 x8) (rest-in x8) (count x9) (result x0) (closure x10)
    (link x30) (frame x29) (pinned (state x24) (fuel x28) (stack-limit x27) (code-distance x26))
    (lost-across-calls all-but-pinned))
  (values
    (tags
      (fixnum 0) (pair 1) (suffix-ref 2) (immediate 3) (bloblet 4) (trailer 5) (header 6)
      (forward 7))
    (fixnum (shift 3) (bits 61))
    (immediates
      (false 3) (true 11) (null 19) (unit 27) (eof 35) (unspecified 43) (default 51) (unbound 59))
    (character (subtag 8) (payload-shift 8)) (pair (car -1) (cdr 7))
    (bloblet (reference suffix 4) (field-k-before-suffix 8))
    (header
      (tag 0 3) (kind 3 8) (large 11 1) (fields-frozen 12 1) (suffix-frozen 13 1) (fields 14 18)
      (bytes 32 32))
    (kinds
      (string 1) (symbol 2) (vector 3) (bytevector 4) (flonum 5) (bignum 6) (ratnum 7) (closure 8)
      (code 9) (box 10) (record 11) (record-type 12) (port 13) (continuation 14) (values 15)
      (promise 16) (hash-table 17) (environment 18) (primitive 19) (bloblet 32) (cellular-code 33)
      (compiled-code 34) (env-frame 35) (sum 36) (product 37) (cellular-closure 38)
      (cellular-continuation 39) (register-code 40) (native-closure 41) (flat-array 42)
      (eqtable 43) (weak-pair 44) (native-frame 45) (icell 46) (mailbox 47)))
  (closures (kind 41) (code-field 2) (first-free-field 3) (code-always-runs))
  (code (runs-at reference plus x26) (field-k-before-code 8))
  (frames
    (align 16) (header x29 -8) (link x29 0) (return x29 8)
    (map x29 16
      (live-slots-below 48) (fields-above 48 link return map values) (all-live negative))
    (values-from x29 24) (raw-after-values) (keeps-its-code)
    (map-stored-before calls routines-that-collect) (made sub sp stp x29 x30 add x29 sp 8)
    (stub 32))
  (state
    (fuel 24) (reserve 552) (trap 32) (pc 40) (args 48) (nargs 192) (aux 184) (callout 112)
    (rust-sp 0) (native-sp 136) (fp 144) (top 152) (words 160) (alloc-limit 168) (code 176)
    (clo 200) (delta 208) (code-lo 216) (trap-stub 280) (foreign 288) (closure 296) (cards 304)
    (stack-limit 16) (overflow 480) (poll 560) (cons 568) (bloblet 576))
  (routines
    (foreign
      (entry state foreign) (in (closure x10) (count x9) (arguments x1 x2 x3 x4 x5 x6 x7 x8))
      (out x0) (may-collect))
    (overflow
      (when sp below x27 after-frame-made) (entry state overflow by x30)
      (in (code x16) (info x17 (arguments-held 0 8) (closure-read 8) (variadic 9)))
      (keeps x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))
    (poll (entry state poll) (in) (may-collect) (traps-when-spent 1))
    (cons (entry state cons) (in (car x1) (cdr x2)) (out x0) (may-collect))
    (bloblet
      (entry state bloblet) (in (bytes x1) (fields x2)) (out x0) (may-collect)
      (makes (kind bloblet) (trailer 1) zeroed) (traps-when-refused 3))
    (trap
      (entry state trap-stub) (in (kind x9))
      (kinds
        (1 evaluation-step-limit-exceeded) (2 stack-overflow) (3 a-primitive-failed)
        (4 car-or-cdr-of-a-non-pair) (5 division-by-zero))))
  (fuel (register x28) (subtract 1) (on entry back-edge) (borrow poll))
  (barrier (cards state cards) (card-shift 9) (mark 1)))

;; `(call-it f x)`, a procedure of the native convention with a frame, as
;; `frames.fx`'s: its four value slots `f`, `x`, `'()` and its own code
;; bloblet, all live; the stack's limit checked when the frame is made
;; (`overflow`), fuel counted on entry (`poll`); then `(f x)`, with no test:
;; whatever `f` is, its code runs. The instruction beside each word, in the
;; terms of `fx26:arm64.fx`, as `frames.fx` has them.
(define* call-code (subr (alloc @heap) () (listof int @heap))
  (lambda ()
    (list
      3506504703 ;  0  (sub-imm sp sp 64)                     the frame: 64 bytes
      2835414013 ;  1  (stp 29 30 sp 8)
      2432705533 ;  2  (add-imm 29 sp 8)
      2432697328 ;  3  (add-imm 16 sp 0)                      past the stack's limit?
      3944415775 ;  4  (cmp 16 27)
      1409286915 ;  5  (b-cond lo 24)                         to 29
      4166959440 ;  6  (ldur 16 10 -20)                       its code: the closure's field 2
      4177530785 ;  7  (str 1 29 24)                          f
      4177531810 ;  8  (str 2 29 32)                          x
      3531604593 ;  9  (movz 17 19 0)                         '()
      4177532849 ; 10  (str 17 29 40)
      4177533872 ; 11  (str 16 29 48)                         its code
      3531607825 ; 12  (movz 17 120 0)                        the map: four slots live, seven fields
      4074768145 ; 13  (movk 17 56 3)
      4177529777 ; 14  (str 17 29 16)
      4043311004 ; 15  (subs-imm 28 28 1)                     fuel
      1409286467 ; 16  (b-cond lo 10)                         to 26
      4181725098 ; 17  (ldr 10 29 24)                         (f x)
      4181726113 ; 18  (ldr 1 29 32)
      4166959440 ; 19  (ldur 16 10 -20)                       its code, whatever f is
      2333737488 ; 20  (add 16 16 26)
      3531604009 ; 21  (movz 9 1 0)                           the count
      3594453504 ; 22  (blr 16)
      2839608317 ; 23  (ldp 29 30 sp 8)                       its value, returned
      2432762879 ; 24  (add-imm sp sp 64)
      3596551104 ; 25  ret
      4181793552 ; 26  (ldr 16 24 560)                        `poll`
      3594453504 ; 27  (blr 16)
      402653173  ; 28  (b -11)                                to 17
      4166959440 ; 29  (ldur 16 10 -20)                       `overflow`: its code in x16,
      3531612241 ; 30  (movz 17 258 0)                        x1 and x2 held, the closure read
      4181783326 ; 31  (ldr 30 24 480)
      3594453952 ; 32  (blr 30)
      402653157)))  ; 33  (b -27)                             to 6

;; The instructions from byte `at` of `b`'s suffix, little-endian.
(define* put-all (subr (maxeff (write @heap) (read @heap) spin)
                      ((bloblet (fields) @heap) int (listof int @heap)) unit)
  (lambda (b at ws)
    (if (null? ws)
        #u
        (let ((w (car ws)))
          (begin (bloblet-set-byte! b at (modulo w 256))
                 (bloblet-set-byte! b (+ at 1) (modulo (quotient w 256) 256))
                 (bloblet-set-byte! b (+ at 2) (modulo (quotient w 65536) 256))
                 (bloblet-set-byte! b (+ at 3) (quotient w 16777216))
                 (put-all b (+ at 4) (cdr ws)))))))

;; The code, sealed: made code.
(define* sealed (subr (maxeff (alloc @heap) (write @heap) (read @heap) spin (io native))
                     () (bloblet (fields) @heap))
  (lambda ()
    (let* ((ws (call-code))
           (b (the (bloblet (fields) @heap) (make-bloblet (* 4 (list-length ws))))))
      (begin (put-all b 0 ws) (seal-code b)))))

;; It, as a procedure given a procedure; and as one given a continuation.
(define-type caller
  (subr (conv arm64-native) (maxeff (read @heap) (read @globals) spin)
        ((subr (conv fx) (maxeff (read @heap) (read @globals) spin) (int) int) int) int))
(define-type k-caller
  (subr (conv arm64-native) (maxeff (goto @k) spin) ((subr (conv fx) (goto @k) (int) void) int)
        int))
;; Made each time, on a machine that runs native code.
(define-effect makes
  (maxeff (alloc @heap) (write @heap) (read @heap) (read @globals) spin (io native)))
(define* call-it (subr makes () caller) (lambda () (the caller (native-procedure (sealed)))))
(define* call-k (subr makes () k-caller) (lambda () (the k-caller (native-procedure (sealed)))))

;; A primitive, the standard operation as a value.
(if (native-code?) ((call-it) bitwise-not 41) -42)
;; A continuation, given a value from the made code's frame, which it leaves.
(if (native-code?)
    (let ((c (call-k)))
      (+ 1 ((proj (proj (proj cwcc @k) int) (maxeff (goto @k) spin))
            (lambda ((k (subr (goto @k) (int) void))) (c k 41)))))
    42)
;; A closure that stays cellular, so that on a machine whose code is native
;; it is a cellular word's.
(if (native-code?) ((call-it) (lambda (x) (stay-cellular (+ x 1))) 41) 42)
