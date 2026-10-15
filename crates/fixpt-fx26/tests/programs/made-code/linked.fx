;;; A primitive reached by made code through its own field, not by a number
;;; (`TODO.md` §97, `docs/research/declared-conventions.md`, "Primitives"):
;;; the program puts the standard operation `*`, a procedure value, in
;;; field 0 of the code bloblet it makes; the code reads the field
;;; PC-relatively and calls it as any procedure, native code directly,
;;; anything else by `foreign`. So `(square x)` is `(* x x)`. Made from the
;;; convention read as data (`fx26:convention.fx`) by the arm64 encoder
;;; written in FX-26. Where this machine runs no native code, the answer
;;; it would give.
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
  (closures (kind 41) (code-field 2) (first-free-field 3) (native-when-code-at-least code-lo))
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

(define cv (load-input "fx26:convention.fx"))
(define cvt (load-module "fx26:convention-types.fx"))
(define-type convention (select cvt convention))
(define a64 (load-input "fx26:arm64.fx"))

;; `(square x)` for convention `c`: a frame of one value slot, `x`, live
;; across `poll`; the stack's limit checked once it is made (`overflow`);
;; then field 0, read PC-relatively, called with `x` and `x`. Field 0 is 16
;; bytes before the code (field 1 is the trailer). Scratch: `x16`, `x17`.
(define* square-code (subr (maxeff (read @globals) (alloc @heap) spin) (convention)
                           (listof int @heap))
  (lambda (c)
    (let* ((rg (extract c registers)) (vs (extract c values)) (fr (extract c frames))
           (st (extract c state)) (rs (extract c routines))
           (fp (extract rg frame)) (lr (extract rg link)) (s (extract rg state))
           (cl (extract rg closure)) (a1 (car (extract rg arguments)))
           (a2 (car (cdr (extract rg arguments)))) (n (extract rg count))
           (fixnum (lambda ((k int)) (arithmetic-shift k (extract vs fixnum-shift))))
           (slot0 (extract fr values-from))
           (size (let ((a (extract fr align)) (b (- (+ slot0 8) (extract fr header))))
                   (* a (quotient (+ b (- a 1)) a))))
           (pair-at (- (extract fr link) (extract fr header)))
           ;; A closure's code bloblet: field `code-field` of its reference.
           (code-at (- 0 (+ (* (extract vs field-k-before-suffix)
                               (extract (extract c closures) code-field))
                            (extract vs bloblet-past-suffix))))
           ;; The map, a fixnum: slot 0 live, and the frame's fields, from
           ;; its link to slot 0, above `fields-above`.
           (fields (+ (quotient (- slot0 (extract fr link)) 8) 1))
           (map (fixnum (+ (arithmetic-shift fields (extract fr fields-above)) 1)))
           (o (extract rs overflow))
           (add-imm (with a64 arm-add-imm)) (ldr (with a64 arm-ldr)) (ldur (with a64 arm-ldur))
           (movz (with a64 arm-movz)) (blr (with a64 arm-blr)) (b (with a64 arm-b))
           (b-cond (with a64 arm-b-cond)) (cmp (with a64 arm-cmp)) (lo 3) (sp 31))
      (list
        ((with a64 arm-sub-imm) sp sp size)                             ;  0  the frame
        ((with a64 arm-stp) fp lr sp pair-at)
        (add-imm fp sp (- 0 (extract fr header)))
        (add-imm 16 sp 0)                                               ;  3  past the limit?
        (cmp 16 (extract rg stack-limit))
        (b-cond lo 27)                                                  ;  5  to 32
        ((with a64 arm-str) a1 fp slot0)                                ;  6  x
        (movz 17 (modulo map 65536) 0)                                  ;  7  the map
        ((with a64 arm-movk) 17 (quotient map 281474976710656) 3)
        ((with a64 arm-str) 17 fp (extract fr map))
        ((with a64 arm-subs-imm) (extract rg fuel) (extract rg fuel)    ; 10  fuel
                                 (extract (extract c fuel) subtract))
        (b-cond lo 18)                                                  ; 11  to 29
        (ldr a1 fp slot0)                                               ; 12  (* x x)
        ((with a64 arm-mov) a2 a1)
        ((with a64 arm-ldr-lit) cl -18)                                 ; 14  field 0
        (ldur 16 cl code-at)
        (ldr 17 s (extract (extract c closures) native-when-code-at-least)) ; 16  native?
        (cmp 16 17)
        (b-cond lo 7)                                                   ; 18  to 25
        ((with a64 arm-add) 16 16 (extract rg code-distance))
        (movz n 2 0)
        (blr 16)
        ((with a64 arm-ldp) fp lr sp pair-at)                           ; 22  returned
        (add-imm sp sp size)
        (with a64 arm-ret)
        (movz n 2 0)                                                    ; 25  `foreign`
        (ldr 16 s (extract (extract rs foreign) entry))
        (blr 16)
        (b -6)                                                          ; 28  to 22
        (ldr 16 s (extract (extract rs poll) entry))                    ; 29  `poll`
        (blr 16)
        (b -19)                                                         ; 31  to 12
        (ldur (extract o code) cl code-at)                              ; 32  `overflow`
        (movz (extract o info) (+ (arithmetic-shift 1 (extract o held-at))
                                  (arithmetic-shift 1 (extract o closure-read))) 0)
        (ldr lr s (extract o entry))
        (blr lr)
        (b -30)))))                                                     ; 36  to 6

;; The instructions from byte `at` of `b`'s suffix, little-endian.
(define* put-all (subr (maxeff (write @heap) (read @heap) spin)
                      ((bloblet (fields (subr pure (int int) int)) @heap) int (listof int @heap))
                      unit)
  (lambda (b at ws)
    (if (null? ws)
        #u
        (let ((w (car ws)))
          (begin (bloblet-set-byte! b at (modulo w 256))
                 (bloblet-set-byte! b (+ at 1) (modulo (quotient w 256) 256))
                 (bloblet-set-byte! b (+ at 2) (modulo (quotient w 65536) 256))
                 (bloblet-set-byte! b (+ at 3) (quotient w 16777216))
                 (put-all b (+ at 4) (cdr ws)))))))

(define-type squarer (subr (conv arm64-native) spin (int) int))

;; The code, field 0 the procedure `f` it calls.
(define* square (subr (maxeff (read @globals) (alloc @heap) (write @heap) (read @heap) spin
                             (io native))
                     (convention (subr pure (int int) int)) squarer)
  (lambda (c f)
    (let* ((ws (square-code c))
           (b (the (bloblet (fields (subr pure (int int) int)) @heap)
                   (make-bloblet (* 4 (list-length ws)) f))))
      (begin (put-all b 0 ws)
             (the squarer (native-procedure (seal-code b)))))))

;; Many calls, so that fuel runs out and `poll` is called with `x` held.
(define* sum-squares (subr spin (squarer int int) int)
  (lambda (sq k acc) (if (= k 0) acc (sum-squares sq (- k 1) (+ acc (sq k))))))

(define conv convention
  (tagcase ((with cv cv-native)) (ok c c) (refused why (error why))))
;; `*`, the standard operation, as the made code's field; then a procedure
;; of the program's own, which is no primitive.
(if (native-code?) ((square conv *) 7) 49)
(if (native-code?) (sum-squares (square conv *) 100000 0) 333338333350000)
(if (native-code?) ((square conv (lambda (a b) (- (* a b) 1))) 7) 48)
