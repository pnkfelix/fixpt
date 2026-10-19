;;; Code made by a generator that reads the convention it makes code to
;;; (`TODO.md` §97, `docs/research/declared-conventions.md`, step 6), on
;;; x86_64: the procedure of `frames.fx`, its registers, offsets, tags and
;;; routines' entries each taken from the declaration, read as a
;;; `convention` (`fx26:convention.fx`), rather than written in; encoded by
;;; the x86_64 encoder written in FX-26 (`fx26:x86_64.fx`), each jump's
;;; displacement from where a first pass put the instructions. Then run as
;;; `frames.fx` runs it. Where this machine runs no native code, the answer
;;; it would give. `made-code/generated.fx` is this on arm64.
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

(define cv (load-input "fx26:convention.fx"))
(define cvt (load-module "fx26:convention-types.fx"))
(define-type convention (select cvt convention))
(define x86 (load-input "fx26:x86_64.fx"))
;; An instruction's bytes, as the encoder makes them.
(define-type ins (listof int @k))
(define-effect makes (maxeff (read @k) (read @globals) (alloc @k) (alloc @heap) (read @heap) spin))

;; The register a routine takes `role` in; -1 if it takes none.
(define* role-reg (subr (maxeff (read @globals) spin)
                       ((listof (productof (name string) (registers (listof int acyclic))) acyclic)
                        string)
                       int)
  (lambda (in role)
    (cond ((null? in) -1)
          ((string=? (extract (car in) name) role) (car (extract (car in) registers)))
          (else (role-reg (cdr in) role)))))
;; The number `name` has in `ns`; -1 if none.
(define* number-of (subr (maxeff (read @globals) spin)
                        ((listof (productof (name string) (number int)) acyclic) string) int)
  (lambda (ns name)
    (cond ((null? ns) -1)
          ((string=? (extract (car ns) name) name) (extract (car ns) number))
          (else (number-of (cdr ns) name)))))
;; The `k`th of `xs`, from 0; 0 past the end (a first pass's, which has none).
(define* nth (subr (maxeff (read @heap) spin) ((listof int @heap) int) int)
  (lambda (xs k) (cond ((null? xs) 0) ((= k 0) (car xs)) (else (nth (cdr xs) (- k 1))))))

;; `(build n f)` of `frames.fx`, for convention `c`, its instructions
;; placed at `at` (none, the first pass): a frame of four value slots (`i`,
;; `f`, the list so far, its own code bloblet), all live; the stack's limit
;; checked once it is made (`overflow`); `n` pairs by `cons`, fuel counted
;; on the loop's back edge (`poll` when it runs out); then `(f list)`,
;; native code called directly, anything else by `foreign`. Scratch:
;; `r11`, `r9` and `r14`, which no call keeps. A word of the state is a
;; place past `cv-in-state`; so are the fuel, the stack's limit and the
;; code distance, on x86_64.
(define* build-code (subr makes (convention (listof int @heap)) (listof ins @heap))
  (lambda (c at)
    (let* ((rg (extract c registers)) (vs (extract c values)) (fr (extract c frames))
           (rs (extract c routines)) (in-state (with cv cv-in-state))
           (fp (extract rg frame)) (s (extract rg state))
           (cl (extract rg closure)) (a1 (car (extract rg arguments)))
           (a2 (car (cdr (extract rg arguments)))) (n (extract rg count))
           (out (extract (extract rs cons) out))
           (car-r (role-reg (extract (extract rs cons) in) "car"))
           (cdr-r (role-reg (extract (extract rs cons) in) "cdr"))
           (fixnum (lambda ((k int)) (arithmetic-shift k (extract vs fixnum-shift))))
           ;; Value slot `k`, from the frame's register; the frame's size.
           (slot (lambda ((k int)) (+ (extract fr values-from) (* 8 k))))
           (size (let ((a (extract fr align)) (b (- (slot 4) (extract fr header))))
                   (* a (quotient (+ b (- a 1)) a))))
           (code-at (- 0 (+ (* (extract vs field-k-before-suffix)
                               (extract (extract c closures) code-field))
                            (extract vs bloblet-past-suffix))))
           (fields (quotient (- (slot 4) (extract fr link)) 8))
           (map (fixnum (+ (arithmetic-shift fields (extract fr fields-above)) 15)))
           (o (extract rs overflow))
           ;; The frame's link and return, from the stack's top once it is made.
           (link-at (- (extract fr link) (extract fr header)))
           (return-at (- (extract fr return) (extract fr header)))
           (load (with x86 x86-load)) (store (with x86 x86-store))
           (call-m (with x86 x86-call-m)) (jcc (with x86 x86-jcc)) (jmp (with x86 x86-jmp))
           (sub 5) (add 0) (cmp 7) (b 2) (e 4) (sp 4) (r11 11) (r9 9) (r14 14)
           ;; From instruction `j`'s end to instruction `t`'s start.
           (to (lambda ((j int) (t int)) (- (nth at t) (nth at (+ j 1)))))
           ;; `op` of `r` and a place: a register, or a word of the state.
           (with-place (lambda ((op int) (r int) (p int))
                         (if (>= p in-state)
                             ((with x86 x86-alu-rm) op r s (- p in-state))
                             ((with x86 x86-alu) op r p)))))
      (list
        ((with x86 x86-pop) r11)                                        ;  0  the frame
        ((with x86 x86-alu-imm) sub sp size)
        (store sp link-at fp)
        (store sp return-at r11)
        ((with x86 x86-lea) fp sp (- 0 (extract fr header)))
        (with-place cmp sp (extract rg stack-limit))                    ;  5  past the limit?
        (jcc b (to 6 44))
        (load r9 cl code-at)                                            ;  7  its code
        (store fp (slot 0) a1)                                          ;  8  i
        (store fp (slot 1) a2)                                          ;  9  f
        ((with x86 x86-store-imm) fp -1 1 (slot 2)                      ; 10  '()
                                  (number-of (extract vs immediates) "null"))
        (store fp (slot 3) r9)                                          ; 11  its code
        ((with x86 x86-mov-imm) r14 map)                                ; 12  the map
        (store fp (extract fr map) r14)
        (let ((f (extract rg fuel)) (k (extract (extract c fuel) subtract)))
          (if (>= f in-state)                                           ; 14  fuel
              ((with x86 x86-alu-mi) sub s (- f in-state) k)
              ((with x86 x86-alu-imm) sub f k)))
        (jcc b (to 15 42))
        (load car-r fp (slot 0))                                        ; 16  i
        ((with x86 x86-test) car-r car-r)
        (jcc e (to 18 26))
        (load cdr-r fp (slot 2))
        (call-m s (extract (extract rs cons) entry))                    ; 20  (cons i list)
        (store fp (slot 2) out)
        (load a1 fp (slot 0))
        ((with x86 x86-alu-imm) sub a1 (fixnum 1))                      ; 23  i - 1
        (store fp (slot 0) a1)
        (jmp (to 25 14))
        (load cl fp (slot 1))                                           ; 26  (f list)
        (load a1 fp (slot 2))
        (load r9 cl code-at)
        ((with x86 x86-alu-rm) cmp r9 s                                 ; 29  native code?
                               (extract (extract c closures) native-when-code-at-least))
        (jcc b (to 30 39))
        (with-place add r9 (extract rg code-distance))
        ((with x86 x86-mov-imm) n 1)
        ((with x86 x86-call-r) r9)
        (load r11 fp (extract fr return))                               ; 34  its value, returned
        (load fp fp (extract fr link))
        ((with x86 x86-alu-imm) add sp (- size 8))
        (store sp 0 r11)
        ((with x86 x86-ret))
        ((with x86 x86-mov-imm) n 1)                                    ; 39  `foreign`
        (call-m s (extract (extract rs foreign) entry))
        (jmp (to 41 34))
        (call-m s (extract (extract rs poll) entry))                    ; 42  `poll`
        (jmp (to 43 16))
        (load (extract o code) cl code-at)                              ; 44  `overflow`
        ((with x86 x86-mov-imm) (extract o info) (+ (arithmetic-shift 2 (extract o held-at))
                                                    (arithmetic-shift 1 (extract o closure-read))))
        (call-m s (extract o entry))
        (jmp (to 47 7))))))                                             ; 47  to 7

;; Where each of `is` starts, from `at`, and where the last ends.
(define* offsets (subr (maxeff (read @k) (read @heap) (alloc @heap) spin)
                       ((listof ins @heap) int) (listof int @heap))
  (lambda (is at)
    (cons at (if (null? is) nil (offsets (cdr is) (+ at (list-length (car is))))))))
;; `i`'s bytes, then `rest`.
(define* copy (subr (maxeff (read @k) (alloc @heap) spin) (ins (listof int @heap))
                    (listof int @heap))
  (lambda (i rest) (if (null? i) rest (cons (car i) (copy (cdr i) rest)))))
(define* flat (subr (maxeff (read @k) (read @heap) (alloc @heap) spin) ((listof ins @heap))
                    (listof int @heap))
  (lambda (is) (if (null? is) nil (copy (car is) (flat (cdr is))))))
;; The code's bytes: placed, then made again with each jump's displacement.
(define* code-bytes (subr makes (convention) (listof int @heap))
  (lambda (c) (flat (build-code c (offsets (build-code c nil) 0)))))

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

(define* build (subr (maxeff makes (write @heap) (io native)) (convention) builder)
  (lambda (c)
    (let* ((bs (code-bytes c))
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

;; fixpt's convention, read; the code made for it, run: a million pairs,
;; collections among them, and the sum of 1 … n; and made at every depth.
(define conv convention
  (tagcase ((with cv cv-native)) (ok c c) (refused why (error why))))
(if (native-code?) ((build conv) 1000000 (lambda (xs) (total xs 0))) 500000500000)
(if (native-code?) (deep (build conv) 3000) 165055)
