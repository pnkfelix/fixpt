;;; Code a program makes that is not a leaf (`TODO.md` §97, `docs/research/
;;; declared-conventions.md`, step 5): a procedure with a frame, its stack
;;; map, the stack's limit, pairs made by `cons` across collections, fuel
;;; and `poll`, and a call of a procedure it is given, native or not, to the
;;; convention it declares. Where this machine runs no native code, the
;;; answer it would give.
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

;; `(build n f)`, a procedure of the native convention with a frame: its
;; four value slots `i`, `f`, the list so far and its own code bloblet,
;; all live (its stack map, stored once); the stack's limit checked when
;; the frame is made (`overflow`); `n` pairs made by `cons`, fuel counted
;; on the loop's back edge (`poll` when it runs out); then `(f list)`,
;; native code called directly, anything else by `foreign`. The offsets
;; of the state's fields are the declaration's, above. Encoded by the
;; arm64 encoder written in FX-26 (`fx26:arm64.fx`, as `(arm-sub-imm 31 31
;; 64)` and so on: the instruction beside each word, in its terms, `sp`
;; 31 and `lo` 3).
(define* build-code (subr (alloc @heap) () (listof int @heap))
  (lambda ()
    (list
      3506504703 ;  0  (sub-imm sp sp 64)                     the frame: 64 bytes
      2835414013 ;  1  (stp 29 30 sp 8)
      2432705533 ;  2  (add-imm 29 sp 8)
      2432697328 ;  3  (add-imm 16 sp 0)                      past the stack's limit?
      3944415775 ;  4  (cmp 16 27)
      1409287459 ;  5  (b-cond lo 41)                         to 46
      4166959440 ;  6  (ldur 16 10 -20)                       its code: the closure's field 2
      4177530785 ;  7  (str 1 29 24)                          i
      4177531810 ;  8  (str 2 29 32)                          f
      3531604593 ;  9  (movz 17 19 0)                         '()
      4177532849 ; 10  (str 17 29 40)                         the list
      4177533872 ; 11  (str 16 29 48)                         its code
      3531607825 ; 12  (movz 17 120 0)                        the map: four slots live, seven fields
      4074768145 ; 13  (movk 17 56 3)
      4177529777 ; 14  (str 17 29 16)
      4043311004 ; 15  (subs-imm 28 28 1)                     fuel
      1409287011 ; 16  (b-cond lo 27)                         to 43
      4181725089 ; 17  (ldr 1 29 24)                          i
      3019899169 ; 18  (cbz 1 9)                              to 27 when 0
      4181727138 ; 19  (ldr 2 29 40)
      4181794576 ; 20  (ldr 16 24 568)                        (cons i list)
      3594453504 ; 21  (blr 16)
      4177532832 ; 22  (str 0 29 40)
      4181725089 ; 23  (ldr 1 29 24)
      3506446369 ; 24  (sub-imm 1 1 8)                        i - 1
      4177530785 ; 25  (str 1 29 24)
      402653173  ; 26  (b -11)                                to 15
      4181726122 ; 27  (ldr 10 29 32)                         (f list)
      4181727137 ; 28  (ldr 1 29 40)
      4166959440 ; 29  (ldur 16 10 -20)
      4181749521 ; 30  (ldr 17 24 216)                        native code?
      3943760415 ; 31  (cmp 16 17)
      1409286371 ; 32  (b-cond lo 7)                          to 39
      2333737488 ; 33  (add 16 16 26)
      3531604009 ; 34  (movz 9 1 0)
      3594453504 ; 35  (blr 16)
      2839608317 ; 36  (ldp 29 30 sp 8)                       its value, returned
      2432762879 ; 37  (add-imm sp sp 64)
      3596551104 ; 38  ret
      3531604009 ; 39  (movz 9 1 0)                           `foreign`
      4181758736 ; 40  (ldr 16 24 288)
      3594453504 ; 41  (blr 16)
      402653178  ; 42  (b -6)                                 to 36
      4181793552 ; 43  (ldr 16 24 560)                        `poll`
      3594453504 ; 44  (blr 16)
      402653156  ; 45  (b -28)                                to 17
      4166959440 ; 46  (ldur 16 10 -20)                       `overflow`: its code in x16,
      3531612241 ; 47  (movz 17 258 0)                        x1 and x2 held, the closure read
      4181783326 ; 48  (ldr 30 24 480)
      3594453952 ; 49  (blr 30)
      402653140)))  ; 50  (b -44)                             to 6

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

(define-type summer
  (subr (conv fx) (maxeff (read @heap) (read @globals) spin) ((listof int @heap)) int))
(define-type builder
  (subr (conv arm64-native) (maxeff (alloc @heap) (read @heap) (read @globals) spin)
        (int summer) int))

(define* build (subr (maxeff (read @globals) (alloc @heap) (write @heap) (read @heap) spin
                            (io native))
                    () builder)
  (lambda ()
    (let* ((ws (build-code))
           (b (the (bloblet (fields) @heap) (make-bloblet (* 4 (list-length ws))))))
      (begin (put-all b 0 ws)
             (the builder (native-procedure (seal-code b)))))))

(define* total (subr (maxeff (read @heap) spin) ((listof int @heap) int) int)
  (lambda (xs acc) (if (null? xs) acc (total (cdr xs) (+ acc (car xs))))))

;; Made at every depth of a recursion 3000 deep, so that, the stack cache
;; small, the made code's own frame is at times the one past its limit
;; (`overflow`): the sum of 1 … 10, 3001 times.
(define* deep (subr (maxeff (alloc @heap) (read @heap) (read @globals) spin) (builder int) int)
  (lambda (b k)
    (+ (b 10 (lambda (xs) (total xs 0))) (if (= k 0) 0 (deep b (- k 1))))))

;; A million pairs, collections among them, and the sum of 1 … n.
(if (native-code?) ((build) 1000000 (lambda (xs) (total xs 0))) 500000500000)
(if (native-code?) (deep (build) 3000) 165055)
