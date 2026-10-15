;;; Code made by a generator that reads the convention it makes code to
;;; (`TODO.md` §97, `docs/research/declared-conventions.md`, step 6): the
;;; procedure of `frames.fx`, its registers, offsets, tags and routines'
;;; entries each taken from the declaration, read as a `convention`
;;; (`fx26:convention.fx`), rather than written in; encoded by the arm64
;;; encoder written in FX-26 (`fx26:arm64.fx`). Then run as `frames.fx`
;;; runs it. Where this machine runs no native code, the answer it would
;;; give.
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

;; `(build n f)` of `frames.fx`, for convention `c`: a frame of four value
;; slots (`i`, `f`, the list so far, its own code bloblet), all live; the
;; stack's limit checked once it is made (`overflow`); `n` pairs by `cons`,
;; fuel counted on the loop's back edge (`poll` when it runs out); then
;; `(f list)`, native code called directly, anything else by `foreign`.
;; Scratch: `x16` and `x17`, which no call keeps.
(define* build-code
         (subr (maxeff (read @globals) (alloc @heap) spin) (convention) (listof int @heap))
  (lambda (c)
    (let* ((rg (extract c registers)) (vs (extract c values)) (fr (extract c frames))
           (st (extract c state)) (rs (extract c routines))
           (fp (extract rg frame)) (lr (extract rg link)) (s (extract rg state))
           (cl (extract rg closure)) (a1 (car (extract rg arguments)))
           (a2 (car (cdr (extract rg arguments)))) (n (extract rg count))
           (car-r (role-reg (extract (extract rs cons) in) "car"))
           (cdr-r (role-reg (extract (extract rs cons) in) "cdr"))
           (fixnum (lambda ((k int)) (arithmetic-shift k (extract vs fixnum-shift))))
           ;; Value slot `k`, from the frame's register; the frame's size.
           (slot (lambda ((k int)) (+ (extract fr values-from) (* 8 k))))
           (size (let ((a (extract fr align)) (b (- (slot 4) (extract fr header))))
                   (* a (quotient (+ b (- a 1)) a))))
           ;; The closure's code bloblet: field `code-field` of its reference.
           (code-at (- 0 (+ (* (extract vs field-k-before-suffix)
                               (extract (extract c closures) code-field))
                            (extract vs bloblet-past-suffix))))
           ;; The map, a fixnum: four value slots live; above `fields-above`,
           ;; the count of the frame's fields, from its link to its last slot.
           (fields (quotient (- (slot 4) (extract fr link)) 8))
           (map (fixnum (+ (arithmetic-shift fields (extract fr fields-above)) 15)))
           (o (extract rs overflow))
           (sub-imm (with a64 arm-sub-imm)) (add-imm (with a64 arm-add-imm))
           (ldr (with a64 arm-ldr)) (str (with a64 arm-str)) (ldur (with a64 arm-ldur))
           (movz (with a64 arm-movz)) (movk (with a64 arm-movk)) (blr (with a64 arm-blr))
           (b (with a64 arm-b)) (b-cond (with a64 arm-b-cond)) (cmp (with a64 arm-cmp))
           (lo 3) (sp 31))
      (list
        (sub-imm sp sp size)                                            ;  0  the frame
        ((with a64 arm-stp) fp lr sp (- (extract fr link) (extract fr header)))
        (add-imm fp sp (- 0 (extract fr header)))
        (add-imm 16 sp 0)                                               ;  3  past the limit?
        (cmp 16 (extract rg stack-limit))
        (b-cond lo 41)                                                  ;  5  to 46
        (ldur 16 cl code-at)                                            ;  6  its code
        (str a1 fp (slot 0))                                            ;  7  i
        (str a2 fp (slot 1))                                            ;  8  f
        (movz 17 (number-of (extract vs immediates) "null") 0)          ;  9  '()
        (str 17 fp (slot 2))                                            ; 10  the list
        (str 16 fp (slot 3))                                            ; 11  its code
        (movz 17 (modulo map 65536) 0)                                  ; 12  the map
        (movk 17 (quotient map 281474976710656) 3)
        (str 17 fp (extract fr map))
        ((with a64 arm-subs-imm) (extract rg fuel) (extract rg fuel)
                                 (extract (extract c fuel) subtract))
        (b-cond lo 27)                                                  ; 16  to 43
        (ldr car-r fp (slot 0))                                         ; 17  i
        ((with a64 arm-cbz) car-r 9)                                    ; 18  to 27 when 0
        (ldr cdr-r fp (slot 2))
        (ldr 16 s (extract (extract rs cons) entry))                    ; 20  (cons i list)
        (blr 16)
        (str (extract (extract rs cons) out) fp (slot 2))
        (ldr a1 fp (slot 0))
        (sub-imm a1 a1 (fixnum 1))                                      ; 24  i - 1
        (str a1 fp (slot 0))
        (b -11)                                                         ; 26  to 15
        (ldr cl fp (slot 1))                                            ; 27  (f list)
        (ldr a1 fp (slot 2))
        (ldur 16 cl code-at)
        (ldr 17 s (extract (extract c closures) native-when-code-at-least)) ; 30  native code?
        (cmp 16 17)
        (b-cond lo 7)                                                   ; 32  to 39
        ((with a64 arm-add) 16 16 (extract rg code-distance))
        (movz n 1 0)
        (blr 16)
        ((with a64 arm-ldp) fp lr sp (- (extract fr link) (extract fr header))) ; 36  returned
        (add-imm sp sp size)
        (with a64 arm-ret)
        (movz n 1 0)                                                    ; 39  `foreign`
        (ldr 16 s (extract (extract rs foreign) entry))
        (blr 16)
        (b -6)                                                          ; 42  to 36
        (ldr 16 s (extract (extract rs poll) entry))                    ; 43  `poll`
        (blr 16)
        (b -28)                                                         ; 45  to 17
        (ldur (extract o code) cl code-at)                              ; 46  `overflow`
        (movz (extract o info) (+ (arithmetic-shift 2 (extract o held-at))
                                  (arithmetic-shift 1 (extract o closure-read))) 0)
        (ldr lr s (extract o entry))
        (blr lr)
        (b -44)))))                                                     ; 50  to 6
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
                    (convention) builder)
  (lambda (c)
    (let* ((ws (build-code c))
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

;; fixpt's convention, read; the code made for it, run: a million pairs,
;; collections among them, and the sum of 1 … n; and made at every depth.
(define conv convention
  (tagcase ((with cv cv-native)) (ok c c) (refused why (error why))))
(if (native-code?) ((build conv) 1000000 (lambda (xs) (total xs 0))) 500000500000)
(if (native-code?) (deep (build conv) 3000) 165055)
