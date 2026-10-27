;;; Every procedure's code runs (`docs/research/code-stubs.md`): a
;;; convention declared with `(code-always-runs)`, on x86_64, and code made
;;; to it that calls the procedure it is given with no test of what it is,
;;; its code at its closure's field 2 plus the code distance: native code,
;;; or a stub that enters `foreign`. Given a primitive, a continuation, and
;;; a closure kept cellular. Where this machine runs no native code, the
;;; answers it would give. `made-code/stubs.fx` is this on arm64.
(define-convention x86_64-native
  (target x86_64)
  (registers
    (arguments rdi rsi r8 (state reg4) (state reg5) (state reg6) (state reg7) (state reg8))
    (rest-in (state reg8)) (count r10) (result rax) (closure rbx) (link pushed) (frame rbp)
    (pinned
      (state r15) (fuel (state fuel)) (stack-limit (state stack-limit))
      (code-distance (state delta)))
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
  (code (runs-at reference plus (state delta)) (field-k-before-code 8))
  (frames
    (align 16) (header rbp -8) (link rbp 0) (return rbp 8)
    (map rbp 16 (live-slots-below 48) (fields-above 48 link return map values) (all-live negative))
    (values-from rbp 24) (raw-after-values) (keeps-its-code)
    (map-stored-before calls routines-that-collect)
    (made pop return sub rsp store rbp rsp 8 store return rsp 16 lea rbp rsp 8) (stub 32))
  (state
    (fuel 24) (reserve 552) (trap 32) (pc 40) (args 48) (nargs 192) (aux 184) (callout 112)
    (rust-sp 0) (native-sp 136) (fp 144) (top 152) (words 160) (alloc-limit 168) (code 176)
    (clo 200) (delta 208) (code-lo 216) (trap-stub 280) (foreign 288) (closure 296) (cards 304)
    (stack-limit 16) (overflow 480) (poll 560) (cons 568) (bloblet 576) (reg4 616) (reg5 624)
    (reg6 632) (reg7 640) (reg8 648))
  (routines
    (foreign
      (entry state foreign)
      (in
        (closure rbx) (count r10)
        (arguments rdi rsi r8 (state reg4) (state reg5) (state reg6) (state reg7) (state reg8)))
      (out rax) (may-collect))
    (overflow
      (when rsp below (state stack-limit) after-frame-made) (entry state overflow by call)
      (in (code r9) (info r14 (arguments-held 0 8) (closure-read 8) (variadic 9)))
      (keeps rax rdi rsi r8
        (state reg4) (state reg5) (state reg6) (state reg7) (state reg8) r10 rbx))
    (poll (entry state poll) (in) (may-collect) (traps-when-spent 1))
    (cons (entry state cons) (in (car rdi) (cdr rsi)) (out rax) (may-collect))
    (bloblet
      (entry state bloblet) (in (bytes rdi) (fields rsi)) (out rax) (may-collect)
      (makes (kind bloblet) (trailer 1) zeroed) (traps-when-refused 3))
    (trap
      (entry state trap-stub) (in (kind r10))
      (kinds
        (1 evaluation-step-limit-exceeded) (2 stack-overflow) (3 a-primitive-failed)
        (4 car-or-cdr-of-a-non-pair) (5 division-by-zero))))
  (fuel (state fuel) (subtract 1) (on entry back-edge) (borrow poll))
  (barrier (cards state cards) (card-shift 9) (mark 1)))

;; `(call-it f x)`, a procedure of the native convention with a frame, as
;; `frames.fx`'s: its four value slots `f`, `x`, `'()` and its own code
;; bloblet, all live; the stack's limit checked when the frame is made
;; (`overflow`), fuel counted on entry (`poll`); then `(f x)`, with no test:
;; whatever `f` is, its code runs. Each instruction's bytes on its line,
;; the instruction beside them, offsets in decimal.
(define* call-code (subr (alloc @heap) () (listof int @heap))
  (lambda ()
    (list
      65 91                       ;  0  pop r11              the frame: 64 bytes
      72 131 236 64               ;  1  sub rsp, 64
      72 137 108 36 8             ;  2  mov [rsp+8], rbp
      76 137 92 36 16             ;  3  mov [rsp+16], r11
      72 141 108 36 8             ;  4  lea rbp, [rsp+8]
      73 59 103 16                ;  5  cmp rsp, [r15+16]    past the limit?
      15 130 106 0 0 0            ;  6  jb                   to 29
      76 139 75 236               ;  7  mov r9, [rbx-20]     its code: closure field 2
      72 137 125 24               ;  8  mov [rbp+24], rdi    f
      72 137 117 32               ;  9  mov [rbp+32], rsi    x
      72 199 69 40 19 0 0 0       ; 10  mov [rbp+40], 19     '()
      76 137 77 48                ; 11  mov [rbp+48], r9     its code
      73 190 120 0 0 0 0 0 56 0   ; 12  mov r14, the map     four slots live, 7 fields
      76 137 117 16               ; 13  mov [rbp+16], r14
      73 131 111 24 1             ; 14  sub [r15+24], 1      fuel
      15 130 45 0 0 0             ; 15  jb                   to 27
      72 139 93 24                ; 16  mov rbx, [rbp+24]    (f x)
      72 139 125 32               ; 17  mov rdi, [rbp+32]
      76 139 75 236               ; 18  mov r9, [rbx-20]     its code, whatever f is
      77 3 143 208 0 0 0          ; 19  add r9, [r15+208]
      65 186 1 0 0 0              ; 20  mov r10, 1           the count
      65 255 209                  ; 21  call r9
      76 139 93 8                 ; 22  mov r11, [rbp+8]     its value, returned
      72 139 109 0                ; 23  mov rbp, [rbp]
      72 131 196 56               ; 24  add rsp, 56
      76 137 28 36                ; 25  mov [rsp], r11
      195                         ; 26  ret
      65 255 151 48 2 0 0         ; 27  call [r15+560]       `poll`
      233 199 255 255 255         ; 28  jmp                  to 16
      76 139 75 236               ; 29  mov r9, [rbx-20]     `overflow`: code in r9,
      65 190 2 1 0 0              ; 30  mov r14, 258         rdi, rsi held, closure read
      65 255 151 224 1 0 0        ; 31  call [r15+480]
      233 128 255 255 255)))      ; 32  jmp                  to 7

;; The bytes from byte `at` of `b`'s suffix.
(define* put-all (subr (maxeff (write @heap) (read @heap) spin)
                      ((bloblet (fields) @heap) int (listof int @heap)) unit)
  (lambda (b at bs)
    (if (null? bs) #u (begin (bloblet-set-byte! b at (car bs)) (put-all b (+ at 1) (cdr bs))))))

;; The code, sealed: made code.
(define* sealed (subr (maxeff (alloc @heap) (write @heap) (read @heap) spin (io native))
                     () (bloblet (fields) @heap))
  (lambda ()
    (let* ((bs (call-code)) (b (the (bloblet (fields) @heap) (make-bloblet (list-length bs)))))
      (begin (put-all b 0 bs) (seal-code b)))))

;; It, as a procedure given a procedure; and as one given a continuation.
(define-type caller
  (subr (conv x86_64-native) (maxeff (read @heap) (read @globals) spin)
        ((subr (conv fx) (maxeff (read @heap) (read @globals) spin) (int) int) int) int))
(define-type k-caller
  (subr (conv x86_64-native) (maxeff (goto @k) spin) ((subr (conv fx) (goto @k) (int) void) int)
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
