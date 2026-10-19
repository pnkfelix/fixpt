;;; A bloblet made by made code (`TODO.md` §97, `docs/research/
;;; declared-conventions.md`, routines), on x86_64: `(pack s k)` calls the
;;; convention's `bloblet` routine for a plain bloblet of `k` suffix bytes
;;; and two fields, which may collect, then stores `s` and `k` in its
;;; fields, each store marking its card. A size the routine refuses, the
;;; trap. Made from the convention read as data (`fx26:convention.fx`) by
;;; the x86_64 encoder written in FX-26. Where this machine runs no native
;;; code, the answer it would give. `made-code/allocated.fx` is this on
;;; arm64.
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

;; The register `role` is in, of a routine's inputs; -1 if none.
(define* role-reg (subr (maxeff (read @globals) spin)
                       ((listof (productof (name string) (registers (listof int acyclic))) acyclic)
                        string)
                       int)
  (lambda (in role)
    (cond ((null? in) -1)
          ((string=? (extract (car in) name) role) (car (extract (car in) registers)))
          (else (role-reg (cdr in) role)))))
;; The `k`th of `xs`, from 0; 0 past the end (a first pass's, which has none).
(define* nth (subr (maxeff (read @heap) spin) ((listof int @heap) int) int)
  (lambda (xs k) (cond ((null? xs) 0) ((= k 0) (car xs)) (else (nth (cdr xs) (- k 1))))))

;; `(pack s k)` for convention `c`, its instructions placed at `at` (none,
;; the first pass): a frame of three value slots (`s`, `k`, its own code
;; bloblet), all live; the stack's limit checked once it is made
;; (`overflow`); fuel (`poll` when it runs out); the bloblet made by the
;; `bloblet` routine; `s` and `k` stored in its fields 0 and 1, each store
;; marking its card. Scratch: `r11`, `r9` and `r14`, which no call keeps.
(define* pack-code (subr makes (convention (listof int @heap)) (listof ins @heap))
  (lambda (c at)
    (let* ((rg (extract c registers)) (vs (extract c values)) (fr (extract c frames))
           (rs (extract c routines)) (bl (extract rs bloblet)) (ba (extract c barrier))
           (in-state (with cv cv-in-state))
           (fp (extract rg frame)) (s (extract rg state))
           (cl (extract rg closure)) (a1 (car (extract rg arguments)))
           (a2 (car (cdr (extract rg arguments)))) (out (extract bl out))
           (fixnum (lambda ((k int)) (arithmetic-shift k (extract vs fixnum-shift))))
           ;; Value slot `k`, from the frame's register; the frame's size.
           (slot (lambda ((k int)) (+ (extract fr values-from) (* 8 k))))
           (size (let ((a (extract fr align)) (b (- (slot 3) (extract fr header))))
                   (* a (quotient (+ b (- a 1)) a))))
           ;; Field `k` of a bloblet the program numbers, from its reference
           ;; (the object model's `k + 2`, after the trailer).
           (field (lambda ((k int)) (- 0 (+ (* (extract vs field-k-before-suffix) (+ k 2))
                                            (extract vs bloblet-past-suffix)))))
           (code-at (- 0 (+ (* (extract vs field-k-before-suffix)
                               (extract (extract c closures) code-field))
                            (extract vs bloblet-past-suffix))))
           (fields (quotient (- (slot 3) (extract fr link)) 8))
           (map (fixnum (+ (arithmetic-shift fields (extract fr fields-above)) 7)))
           (o (extract rs overflow))
           (link-at (- (extract fr link) (extract fr header)))
           (return-at (- (extract fr return) (extract fr header)))
           (load (with x86 x86-load)) (store (with x86 x86-store))
           (call-m (with x86 x86-call-m)) (jcc (with x86 x86-jcc)) (jmp (with x86 x86-jmp))
           (sub 5) (add 0) (cmp 7) (b 2) (shr 5) (sp 4) (r11 11) (r9 9) (r14 14)
           (to (lambda ((j int) (t int)) (- (nth at t) (nth at (+ j 1)))))
           (with-place (lambda ((op int) (r int) (p int))
                         (if (>= p in-state)
                             ((with x86 x86-alu-rm) op r s (- p in-state))
                             ((with x86 x86-alu) op r p))))
           ;; The card of the field `off` from the bloblet marked: four
           ;; instructions, as the machine's own `card_mark`.
           (mark (lambda ((off int))
                   (the (listof ins @heap)
                        (list ((with x86 x86-lea) r9 out off)
                              ((with x86 x86-shift-imm) shr r9 (extract ba card-shift))
                              (load r14 s (extract ba cards))
                              ((with x86 x86-store8-imm) r14 r9 1 0 (extract ba mark)))))))
      (append
        (list
          ((with x86 x86-pop) r11)                                      ;  0  the frame
          ((with x86 x86-alu-imm) sub sp size)
          (store sp link-at fp)
          (store sp return-at r11)
          ((with x86 x86-lea) fp sp (- 0 (extract fr header)))
          (with-place cmp sp (extract rg stack-limit))                  ;  5  past the limit?
          (jcc b (to 6 39))
          (load r9 cl code-at)                                          ;  7  its code
          (store fp (slot 0) a1)                                        ;  8  s
          (store fp (slot 1) a2)                                        ;  9  k
          (store fp (slot 2) r9)                                        ; 10  its code
          ((with x86 x86-mov-imm) r14 map)                              ; 11  the map
          (store fp (extract fr map) r14)
          (let ((f (extract rg fuel)) (k (extract (extract c fuel) subtract)))
            (if (>= f in-state)                                         ; 13  fuel
                ((with x86 x86-alu-mi) sub s (- f in-state) k)
                ((with x86 x86-alu-imm) sub f k)))
          (jcc b (to 14 37))
          (load (role-reg (extract bl in) "bytes") fp (slot 1))         ; 15  k bytes
          ((with x86 x86-mov-imm) (role-reg (extract bl in) "fields") (fixnum 2)) ; two fields
          (call-m s (extract bl entry))                                 ; 17  the bloblet
          (load r9 fp (slot 0))
          (store out (field 0) r9))                                     ; 19  s
        (mark (field 0))
        (list
          (load r9 fp (slot 1))                                         ; 24  k
          (store out (field 1) r9))
        (mark (field 1))
        (list
          (load r11 fp (extract fr return))                             ; 30  returned
          (load fp fp (extract fr link))
          ((with x86 x86-alu-imm) add sp (- size 8))
          (store sp 0 r11)
          ((with x86 x86-ret))
          (call-m s (extract (extract rs poll) entry))                  ; 35  `poll`
          (jmp (to 36 15))
          (load (extract o code) cl code-at)                            ; 37  `overflow`
          ((with x86 x86-mov-imm) (extract o info)
                                  (+ (arithmetic-shift 2 (extract o held-at))
                                     (arithmetic-shift 1 (extract o closure-read))))
          (call-m s (extract o entry))
          (jmp (to 40 7)))))))                                          ; 40  to 7

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
;; The code's bytes: placed, then made again with each displacement.
(define* code-bytes (subr makes (convention) (listof int @heap))
  (lambda (c) (flat (pack-code c (offsets (pack-code c nil) 0)))))

;; The bytes from byte `at` of `b`'s suffix.
(define* put-all (subr (maxeff (write @heap) (read @heap) spin)
                      ((bloblet (fields) @heap) int (listof int @heap)) unit)
  (lambda (b at bs)
    (if (null? bs) #u (begin (bloblet-set-byte! b at (car bs)) (put-all b (+ at 1) (cdr bs))))))

(define-type packed (bloblet (fields string int) @heap))
(define-type packer
  (subr (conv x86_64-native) (maxeff (alloc @heap) (read @globals) spin) (string int) packed))

(define* pack (subr (maxeff makes (write @heap) (io native)) (convention) packer)
  (lambda (c)
    (let* ((bs (code-bytes c))
           (b (the (bloblet (fields) @heap) (make-bloblet (list-length bs)))))
      (begin (put-all b 0 bs)
             (the packer (native-procedure (seal-code b)))))))
;; What a bloblet made holds: its fields and its suffix's size.
(define* shown (subr (read @heap) (packed) string)
  (lambda (b)
    (string-append (bloblet-ref b 0) " " (int->string (bloblet-ref b 1)) " "
                   (int->string (bloblet-bytes b)))))

;; `n` made, `(pack (int->string (modulo i 10)) (modulo i 50))` for `i`
;; from `n` down, each string new, kept in a list across the collections
;; their making makes; then each one's fields and size summed.
(define* many (subr (maxeff (alloc @heap) (read @globals) spin) (packer int (listof packed @heap))
                    (listof packed @heap))
  (lambda (pk i acc)
    (if (= i 0)
        acc
        (many pk (- i 1) (cons (pk (int->string (modulo i 10)) (modulo i 50)) acc)))))
(define* total (subr (maxeff (read @heap) spin) ((listof packed @heap) int) int)
  (lambda (bs acc)
    (if (null? bs)
        acc
        (let ((b (car bs)))
          (total (cdr bs) (+ (+ acc (string-length (bloblet-ref b 0)))
                             (+ (bloblet-ref b 1) (bloblet-bytes b))))))))

(define conv convention
  (tagcase ((with cv cv-native)) (ok c c) (refused why (error why))))
(if (native-code?) (shown ((pack conv) "made" 24)) "made 24 24")
(if (native-code?) (total (many (pack conv) 20000 nil) 0) 1000000)
(if (native-code?)
    (shown ((pack conv) "x" -1))
    (error "bloblet: no bloblet of -1 bytes and 2 fields"))
