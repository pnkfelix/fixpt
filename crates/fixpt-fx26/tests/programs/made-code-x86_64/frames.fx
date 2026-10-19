;;; Code a program makes that is not a leaf (`TODO.md` §97, `docs/research/
;;; declared-conventions.md`, step 5), on x86_64: a procedure with a frame,
;;; its stack map, the stack's limit, pairs made by `cons` across
;;; collections, fuel and `poll`, and a call of a procedure it is given,
;;; native or not, to the convention it declares. Where this machine runs
;;; no native code, the answer it would give. `made-code/frames.fx` is this
;;; on arm64.
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
  (closures (kind 41) (code-field 2) (first-free-field 3) (native-when-code-at-least code-lo))
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

;; `(build n f)`, a procedure of the native convention with a frame: its
;; four value slots `i`, `f`, the list so far and its own code bloblet,
;; all live (its stack map, stored once); the stack's limit checked when
;; the frame is made (`overflow`); `n` pairs made by `cons`, fuel counted
;; on the loop's back edge (`poll` when it runs out); then `(f list)`,
;; native code called directly, anything else by `foreign`. The return
;; address the `call` pushed is popped into the frame as it is made, and
;; pushed again for `ret`. The offsets of the state's fields are the
;; declaration's, above. Encoded by the x86_64 encoder written in FX-26
;; (`fx26:x86_64.fx`, as `generated.fx` does): each instruction's bytes on
;; its line, the instruction beside them, offsets in decimal.
(define* build-code (subr (alloc @heap) () (listof int @heap))
  (lambda ()
    (list
      65 91                       ;  0  pop r11              the frame: 64 bytes
      72 131 236 64               ;  1  sub rsp, 64
      72 137 108 36 8             ;  2  mov [rsp+8], rbp
      76 137 92 36 16             ;  3  mov [rsp+16], r11
      72 141 108 36 8             ;  4  lea rbp, [rsp+8]
      73 59 103 16                ;  5  cmp rsp, [r15+16]    past the limit?
      15 130 182 0 0 0            ;  6  jb                   to 44
      76 139 75 236               ;  7  mov r9, [rbx-20]     its code: closure field 2
      72 137 125 24               ;  8  mov [rbp+24], rdi    i
      72 137 117 32               ;  9  mov [rbp+32], rsi    f
      72 199 69 40 19 0 0 0       ; 10  mov [rbp+40], 19     '()
      76 137 77 48                ; 11  mov [rbp+48], r9     its code
      73 190 120 0 0 0 0 0 56 0   ; 12  mov r14, the map     four slots live, 7 fields
      76 137 117 16               ; 13  mov [rbp+16], r14
      73 131 111 24 1             ; 14  sub [r15+24], 1      fuel
      15 130 121 0 0 0            ; 15  jb                   to 42
      72 139 125 24               ; 16  mov rdi, [rbp+24]    i
      72 133 255                  ; 17  test rdi, rdi
      15 132 32 0 0 0             ; 18  je                   to 26 when 0
      72 139 117 40               ; 19  mov rsi, [rbp+40]
      65 255 151 56 2 0 0         ; 20  call [r15+568]       (cons i list)
      72 137 69 40                ; 21  mov [rbp+40], rax
      72 139 125 24               ; 22  mov rdi, [rbp+24]
      72 131 239 8                ; 23  sub rdi, 8           i - 1
      72 137 125 24               ; 24  mov [rbp+24], rdi
      233 200 255 255 255         ; 25  jmp                  to 14
      72 139 93 32                ; 26  mov rbx, [rbp+32]    (f list)
      72 139 125 40               ; 27  mov rdi, [rbp+40]
      76 139 75 236               ; 28  mov r9, [rbx-20]
      77 59 143 216 0 0 0         ; 29  cmp r9, [r15+216]    native code?
      15 130 33 0 0 0             ; 30  jb                   to 39
      77 3 143 208 0 0 0          ; 31  add r9, [r15+208]
      65 186 1 0 0 0              ; 32  mov r10, 1           the count
      65 255 209                  ; 33  call r9
      76 139 93 8                 ; 34  mov r11, [rbp+8]     its value, returned
      72 139 109 0                ; 35  mov rbp, [rbp]
      72 131 196 56               ; 36  add rsp, 56
      76 137 28 36                ; 37  mov [rsp], r11
      195                         ; 38  ret
      65 186 1 0 0 0              ; 39  mov r10, 1           `foreign`
      65 255 151 32 1 0 0         ; 40  call [r15+288]
      233 221 255 255 255         ; 41  jmp                  to 34
      65 255 151 48 2 0 0         ; 42  call [r15+560]       `poll`
      233 123 255 255 255         ; 43  jmp                  to 16
      76 139 75 236               ; 44  mov r9, [rbx-20]     `overflow`: code in r9,
      65 190 2 1 0 0              ; 45  mov r14, 258         rdi, rsi held, closure read
      65 255 151 224 1 0 0        ; 46  call [r15+480]
      233 52 255 255 255)))       ; 47  jmp                  to 7

;; The bytes from byte `at` of `b`'s suffix.
(define* put-all (subr (maxeff (write @heap) (read @heap) spin)
                      ((bloblet (fields) @heap) int (listof int @heap)) unit)
  (lambda (b at bs)
    (if (null? bs) #u (begin (bloblet-set-byte! b at (car bs)) (put-all b (+ at 1) (cdr bs))))))

(define-type summer
  (subr (conv fx) (maxeff (read @heap) (read @globals) spin) ((listof int @heap)) int))
(define-type builder
  (subr (conv x86_64-native) (maxeff (alloc @heap) (read @heap) (read @globals) spin)
        (int summer) int))

(define* build (subr (maxeff (read @globals) (alloc @heap) (write @heap) (read @heap) spin
                            (io native))
                    () builder)
  (lambda ()
    (let* ((bs (build-code))
           (b (the (bloblet (fields) @heap) (make-bloblet (list-length bs)))))
      (begin (put-all b 0 bs)
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
