;;; MD5 -- the MD5 message digest of 10000-byte blocks, a quick and dirty
;;; transliteration of the RSA reference C code.
;;;
;;; Copyright (C) 2001 Daniel Wang. All rights reserved. Derived from the
;;; RSA Data Security, Inc. MD5 Message-Digest Algorithm.
;;; From MLton's benchmark suite (benchmark/tests/md5.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): 1 run of Test.time_test, with BLOCK_COUNT 20, not
;;; the original's 100000.
;;; Answer: "59ebddd335d8defbcaf5b76c08c64278", the digest's hex string,
;;; which Python's hashlib also gives for these bytes (for 100000 blocks,
;;; the original checks for "766a2bb5d24bddae466c572bcabca3ee", which
;;; hashlib gives too).
;;;
;;; Word32 is `u32`, whose arithmetic wraps as Word32's does: `W32.+`,
;;; `andb`, `orb`, `xorb`, `notb`, `<<`, `>>` and `<` are `u32+`, `u32-and`,
;;; `u32-or`, `u32-xor`, `u32-not`, `u32-shl`, `u32-shr` and `u32<`. FX-26
;;; has no literals of type u32, so each constant is `int->u32` of an int;
;;; shift counts are ints. (Until FX-26 had `u32`, this port did the same
;;; with ints masked to 32 bits, `andb`, `orb` and `xorb` a byte at a time
;;; through tables; that emulation was most of what it measured, and is
;;; why the block count is 20.)
;;; Word8Vector.vector is an array of ints, each a byte; the functions of
;;; W8V that the code uses are written here, and so are SML's records
;;; (products). Test.do_tests is left out (it only prints), and so is
;;; time_test's check of the digest (the answer is the digest).
;;; transform's 64 steps are split into four functions, one per round (the
;;; compiler makes a native frame too large for one `stp` of the whole, and
;;; runs such a function as cellular code); its 16 words go to them in an
;;; array (a product of 16 has no native code either).

;; ---- Word8Vector, as arrays of bytes.

(define-type bytes (arrayof int @v))
(define-effect bv (maxeff (read @v) (write @v) (alloc @v) spin))

(define* w8v-tabulate (subr bv (int (subr pure (int) int)) bytes)
  (lambda (n f)
    (let ((v (the bytes (make-array n 0))))
      (letrec ((fill (subr (maxeff (write @v) spin) (int) unit)
                 (lambda (i) (if (< i n) (begin (array-set! v i (f i)) (fill (+ i 1))) #u))))
        (begin (fill 0) v)))))

;; W8V.extract (vec, s, SOME l), by tabulate as the original's.
(define* w8v-extract (subr bv (bytes int int) bytes)
  (lambda (vec s l)
    (let ((v (the bytes (make-array l 0))))
      (letrec ((fill (subr bv (int) unit)
                 (lambda (i)
                   (if (< i l)
                       (begin (array-set! v i (array-ref vec (+ s i))) (fill (+ i 1)))
                       #u))))
        (begin (fill 0) v)))))

;; W8V.concat [a, b]: the original only ever concatenates two.
(define* w8v-concat2 (subr bv (bytes bytes) bytes)
  (lambda (a b)
    (let* ((na (array-length a))
           (v (the bytes (make-array (+ na (array-length b)) 0))))
      (letrec ((fill (subr bv (int) unit)
                 (lambda (i)
                   (if (< i (array-length v))
                       (begin (array-set! v i (if (< i na) (array-ref a i) (array-ref b (- i na))))
                              (fill (+ i 1)))
                       #u))))
        (begin (fill 0) v)))))

(define-type ints (listof int @l))

(define* w8v-from-list (subr (maxeff bv (read @l)) (ints) bytes)
  (lambda (l)
    (letrec ((len (subr (maxeff (read @l) spin) (ints int) int)
               (lambda (l n) (if (null? l) n (len (cdr l) (+ n 1))))))
      (let ((v (the bytes (make-array (len l 0) 0))))
        (letrec ((fill (subr (maxeff (write @v) (read @l) spin) (int ints) unit)
                   (lambda (i l)
                     (if (null? l) #u (begin (array-set! v i (car l)) (fill (+ i 1) (cdr l)))))))
          (begin (fill 0 l) v))))))

;; PackWord32Little.subVec (buf, i): the ith 32-bit word, little-endian.
(define* sub-vec (subr (read @v) (bytes int) u32)
  (lambda (buf i)
    (let ((at (* i 4)))
      (u32-or (u32-or (int->u32 (array-ref buf at))
                      (u32-shl (int->u32 (array-ref buf (+ at 1))) 8))
              (u32-or (u32-shl (int->u32 (array-ref buf (+ at 2))) 16)
                      (u32-shl (int->u32 (array-ref buf (+ at 3))) 24))))))

;; ---- structure MD5

(define-type word64 (productof (hi u32) (lo u32)))
(define-type word128 (productof (A u32) (B u32) (C u32) (D u32)))
(define-type md5state (productof (digest word128) (mlen word64) (buf bytes)))

(define w64-zero word64 (product (hi (int->u32 0)) (lo (int->u32 0))))

(define* mul8add (subr pure (word64 int) word64)
  (lambda (w n)
    (let* ((mul8lo (u32-shl (int->u32 n) 3))
           (mul8hi (u32-shr (int->u32 n) 29))
           (lo (u32+ (extract w lo) mul8lo))
           (cout (int->u32 (if (u32< lo mul8lo) 1 0)))
           (hi (u32+ mul8hi (u32+ (extract w hi) cout))))
      (product (hi hi) (lo lo)))))

;; Word8.fromLarge (W32.toLarge w): w's low byte.
(define* low-byte (subr pure (u32) int) (lambda (w) (u32->int (u32-and w (int->u32 255)))))

(define-type words (listof u32 @l))

(define* pack-little (subr (maxeff bv (read @l) (alloc @l)) (words) bytes)
  (lambda (wrds)
    (letrec ((loop (subr (maxeff (read @l) (alloc @l) spin (read (globals low-byte))) (words) ints)
               (lambda (ws)
                 (if (null? ws)
                     nil
                     (let* ((w (car ws))
                            (b0 (low-byte w))
                            (b1 (low-byte (u32-shr w 8)))
                            (b2 (low-byte (u32-shr w 16)))
                            (b3 (low-byte (u32-shr w 24))))
                       (cons b0 (cons b1 (cons b2 (cons b3 (loop (cdr ws)))))))))))
      (w8v-from-list (loop wrds)))))

(define S11 int 7)
(define S12 int 12)
(define S13 int 17)
(define S14 int 22)
(define S21 int 5)
(define S22 int 9)
(define S23 int 14)
(define S24 int 20)
(define S31 int 4)
(define S32 int 11)
(define S33 int 16)
(define S34 int 23)
(define S41 int 6)
(define S42 int 10)
(define S43 int 15)
(define S44 int 21)

(define* PADDING (subr bv (int) bytes)
  (lambda (i) (w8v-tabulate i (lambda (k) (if (= k 0) 128 0)))))

(define* F (subr pure (u32 u32 u32) u32)
  (lambda (x y z) (u32-or (u32-and x y) (u32-and (u32-not x) z))))
(define* G (subr pure (u32 u32 u32) u32)
  (lambda (x y z) (u32-or (u32-and x z) (u32-and y (u32-not z)))))
(define* H (subr pure (u32 u32 u32) u32) (lambda (x y z) (u32-xor x (u32-xor y z))))
(define* I (subr pure (u32 u32 u32) u32) (lambda (x y z) (u32-xor y (u32-or x (u32-not z)))))
(define* ROTATE-LEFT (subr pure (u32 int) u32)
  (lambda (x n) (u32-or (u32-shl x n) (u32-shr x (- 32 n)))))

(define-type fn3 (subr pure (u32 u32 u32) u32))
(define-type step (subr (read (globals ROTATE-LEFT)) (u32 u32 u32 u32 u32 int u32) u32))

(define XX (subr pure (fn3) step)
  (lambda (f)
    (lambda (a b c d x s ac)
      (let* ((a (u32+ a (u32+ (u32+ (f b c d) x) ac)))
             (a (ROTATE-LEFT a s)))
        (u32+ a b)))))

(define FF step (XX F))
(define GG step (XX G))
(define HH step (XX H))
(define II step (XX I))

(define empty-buf bytes (w8v-tabulate 0 (lambda (x) 0)))
(define init md5state
  (product (digest (product (A (int->u32 1732584193)) (B (int->u32 4023233417))
                            (C (int->u32 2562383102)) (D (int->u32 271733878))))
           (mlen w64-zero)
           (buf empty-buf)))

;; The sixteen words of a block, fetched once (the original fetches them
;; into sixteen variables "to avoid range checks"). Changed: the original's
;; transform is one function of 64 steps; here each round of 16 is a
;; function of its own, taking the block's words in an array, since one
;; function of all 64 makes a native frame too large (see the header).
(define-type xwords (arrayof u32 @v))

;; Round 1
(define* round1 (subr (read @v) (word128 xwords) word128)
  (lambda (dg xs)
    (let* ((a (extract dg A)) (b (extract dg B)) (c (extract dg C)) (d (extract dg D))
           (a (FF a b c d (array-ref xs 0) S11 (int->u32 3614090360))) ; 1
           (d (FF d a b c (array-ref xs 1) S12 (int->u32 3905402710))) ; 2
           (c (FF c d a b (array-ref xs 2) S13 (int->u32 606105819))) ; 3
           (b (FF b c d a (array-ref xs 3) S14 (int->u32 3250441966))) ; 4
           (a (FF a b c d (array-ref xs 4) S11 (int->u32 4118548399))) ; 5
           (d (FF d a b c (array-ref xs 5) S12 (int->u32 1200080426))) ; 6
           (c (FF c d a b (array-ref xs 6) S13 (int->u32 2821735955))) ; 7
           (b (FF b c d a (array-ref xs 7) S14 (int->u32 4249261313))) ; 8
           (a (FF a b c d (array-ref xs 8) S11 (int->u32 1770035416))) ; 9
           (d (FF d a b c (array-ref xs 9) S12 (int->u32 2336552879))) ; 10
           (c (FF c d a b (array-ref xs 10) S13 (int->u32 4294925233))) ; 11
           (b (FF b c d a (array-ref xs 11) S14 (int->u32 2304563134))) ; 12
           (a (FF a b c d (array-ref xs 12) S11 (int->u32 1804603682))) ; 13
           (d (FF d a b c (array-ref xs 13) S12 (int->u32 4254626195))) ; 14
           (c (FF c d a b (array-ref xs 14) S13 (int->u32 2792965006))) ; 15
           (b (FF b c d a (array-ref xs 15) S14 (int->u32 1236535329))) ; 16
           )
      (product (A a) (B b) (C c) (D d)))))

;; Round 2
(define* round2 (subr (read @v) (word128 xwords) word128)
  (lambda (dg xs)
    (let* ((a (extract dg A)) (b (extract dg B)) (c (extract dg C)) (d (extract dg D))
           (a (GG a b c d (array-ref xs 1) S21 (int->u32 4129170786))) ; 17
           (d (GG d a b c (array-ref xs 6) S22 (int->u32 3225465664))) ; 18
           (c (GG c d a b (array-ref xs 11) S23 (int->u32 643717713))) ; 19
           (b (GG b c d a (array-ref xs 0) S24 (int->u32 3921069994))) ; 20
           (a (GG a b c d (array-ref xs 5) S21 (int->u32 3593408605))) ; 21
           (d (GG d a b c (array-ref xs 10) S22 (int->u32 38016083))) ; 22
           (c (GG c d a b (array-ref xs 15) S23 (int->u32 3634488961))) ; 23
           (b (GG b c d a (array-ref xs 4) S24 (int->u32 3889429448))) ; 24
           (a (GG a b c d (array-ref xs 9) S21 (int->u32 568446438))) ; 25
           (d (GG d a b c (array-ref xs 14) S22 (int->u32 3275163606))) ; 26
           (c (GG c d a b (array-ref xs 3) S23 (int->u32 4107603335))) ; 27
           (b (GG b c d a (array-ref xs 8) S24 (int->u32 1163531501))) ; 28
           (a (GG a b c d (array-ref xs 13) S21 (int->u32 2850285829))) ; 29
           (d (GG d a b c (array-ref xs 2) S22 (int->u32 4243563512))) ; 30
           (c (GG c d a b (array-ref xs 7) S23 (int->u32 1735328473))) ; 31
           (b (GG b c d a (array-ref xs 12) S24 (int->u32 2368359562))) ; 32
           )
      (product (A a) (B b) (C c) (D d)))))

;; Round 3
(define* round3 (subr (read @v) (word128 xwords) word128)
  (lambda (dg xs)
    (let* ((a (extract dg A)) (b (extract dg B)) (c (extract dg C)) (d (extract dg D))
           (a (HH a b c d (array-ref xs 5) S31 (int->u32 4294588738))) ; 33
           (d (HH d a b c (array-ref xs 8) S32 (int->u32 2272392833))) ; 34
           (c (HH c d a b (array-ref xs 11) S33 (int->u32 1839030562))) ; 35
           (b (HH b c d a (array-ref xs 14) S34 (int->u32 4259657740))) ; 36
           (a (HH a b c d (array-ref xs 1) S31 (int->u32 2763975236))) ; 37
           (d (HH d a b c (array-ref xs 4) S32 (int->u32 1272893353))) ; 38
           (c (HH c d a b (array-ref xs 7) S33 (int->u32 4139469664))) ; 39
           (b (HH b c d a (array-ref xs 10) S34 (int->u32 3200236656))) ; 40
           (a (HH a b c d (array-ref xs 13) S31 (int->u32 681279174))) ; 41
           (d (HH d a b c (array-ref xs 0) S32 (int->u32 3936430074))) ; 42
           (c (HH c d a b (array-ref xs 3) S33 (int->u32 3572445317))) ; 43
           (b (HH b c d a (array-ref xs 6) S34 (int->u32 76029189))) ; 44
           (a (HH a b c d (array-ref xs 9) S31 (int->u32 3654602809))) ; 45
           (d (HH d a b c (array-ref xs 12) S32 (int->u32 3873151461))) ; 46
           (c (HH c d a b (array-ref xs 15) S33 (int->u32 530742520))) ; 47
           (b (HH b c d a (array-ref xs 2) S34 (int->u32 3299628645))) ; 48
           )
      (product (A a) (B b) (C c) (D d)))))

;; Round 4
(define* round4 (subr (read @v) (word128 xwords) word128)
  (lambda (dg xs)
    (let* ((a (extract dg A)) (b (extract dg B)) (c (extract dg C)) (d (extract dg D))
           (a (II a b c d (array-ref xs 0) S41 (int->u32 4096336452))) ; 49
           (d (II d a b c (array-ref xs 7) S42 (int->u32 1126891415))) ; 50
           (c (II c d a b (array-ref xs 14) S43 (int->u32 2878612391))) ; 51
           (b (II b c d a (array-ref xs 5) S44 (int->u32 4237533241))) ; 52
           (a (II a b c d (array-ref xs 12) S41 (int->u32 1700485571))) ; 53
           (d (II d a b c (array-ref xs 3) S42 (int->u32 2399980690))) ; 54
           (c (II c d a b (array-ref xs 10) S43 (int->u32 4293915773))) ; 55
           (b (II b c d a (array-ref xs 1) S44 (int->u32 2240044497))) ; 56
           (a (II a b c d (array-ref xs 8) S41 (int->u32 1873313359))) ; 57
           (d (II d a b c (array-ref xs 15) S42 (int->u32 4264355552))) ; 58
           (c (II c d a b (array-ref xs 6) S43 (int->u32 2734768916))) ; 59
           (b (II b c d a (array-ref xs 13) S44 (int->u32 1309151649))) ; 60
           (a (II a b c d (array-ref xs 4) S41 (int->u32 4149444226))) ; 61
           (d (II d a b c (array-ref xs 11) S42 (int->u32 3174756917))) ; 62
           (c (II c d a b (array-ref xs 2) S43 (int->u32 718787259))) ; 63
           (b (II b c d a (array-ref xs 9) S44 (int->u32 3951481745))) ; 64
           )
      (product (A a) (B b) (C c) (D d)))))

;; What transforming a block does, and reads.
(define-effect tf
  (maxeff bv (read (globals FF GG HH II ROTATE-LEFT S11 S12 S13 S14 S21 S22 S23 S24
                            S31 S32 S33 S34 S41 S42 S43 S44 round1 round2 round3 round4
                            sub-vec transform))))

(define* transform (subr bv (word128 int bytes) word128)
  (lambda (dg i buf)
    (let* ((off (quotient i 4))
           (xs (the xwords (make-array 16 (int->u32 0))))
           (fetch (letrec ((fetch (subr (maxeff (read @v) (write @v) spin (read (globals sub-vec)))
                                        (int) unit)
                             (lambda (n)
                               (if (< n 16)
                                   (begin (array-set! xs n (sub-vec buf (+ n off))) (fetch (+ n 1)))
                                   #u))))
                    (fetch 0)))
           (r (round4 (round3 (round2 (round1 dg xs) xs) xs) xs)))
      (product (A (u32+ (extract dg A) (extract r A)))
               (B (u32+ (extract dg B) (extract r B)))
               (C (u32+ (extract dg C) (extract r C)))
               (D (u32+ (extract dg D) (extract r D)))))))

(define-type progress (productof (i int) (digest word128)))

(define* update (subr bv (md5state bytes) md5state)
  (lambda (st input)
    (let* ((buf (extract st buf))
           (digest (extract st digest))
           (mlen (extract st mlen))
           (input-len (array-length input))
           (need-bytes (- 64 (array-length buf))))
      (letrec ((loop (subr tf (int word128) progress)
                 (lambda (i digest)
                   (if (< (+ i 63) input-len)
                       (loop (+ i 64) (transform digest i input))
                       (product (i i) (digest digest))))))
        (let* ((r (if (>= input-len need-bytes)
                      (let* ((buf (w8v-concat2 buf (w8v-extract input 0 need-bytes)))
                             (digest (transform digest 0 buf)))
                        (product (buf empty-buf) (id (loop need-bytes digest))))
                      (product (buf buf) (id (product (i 0) (digest digest))))))
               (i (extract (extract r id) i))
               (digest (extract (extract r id) digest))
               (buf (w8v-concat2 (extract r buf) (w8v-extract input i (- input-len i))))
               (mlen (mul8add mlen input-len)))
          (product (digest digest) (mlen mlen) (buf buf)))))))

(define* final (subr (maxeff bv (read @l) (alloc @l)) (md5state) bytes)
  (lambda (state)
    (let* ((lo (extract (extract state mlen) lo))
           (hi (extract (extract state mlen) hi))
           (bits (pack-little (list lo hi)))
           (index (array-length (extract state buf)))
           (pad-len (if (< index 56) (- 56 index) (- 120 index)))
           (state (update state (PADDING pad-len)))
           (dg (extract (update state bits) digest)))
      (pack-little (list (extract dg A) (extract dg B) (extract dg C) (extract dg D))))))

(define hxd string "0123456789abcdef")

(define-type chars (listof char @l))

(define* to-hex-string (subr (maxeff (read @v) (alloc @l) (read @l) spin) (bytes) string)
  (lambda (v)
    (let ((hxd hxd))
      (letrec ((foldr (subr (maxeff (read @v) (alloc @l) spin) (int chars) chars)
                 (lambda (i acc)
                   (if (< i 0)
                       acc
                       (let ((b (array-ref v i)))
                         (foldr (- i 1)
                                (cons (string-ref hxd (quotient b 16))
                                      (cons (string-ref hxd (modulo b 16)) acc))))))))
        (list->string (foldr (- (array-length v) 1) nil))))))

;; ---- structure Test

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define BLOCK-LEN int 10000)
(define BLOCK-COUNT int 20)

(define* time-loop (subr bv (bytes int md5state) md5state)
  (lambda (block n s)
    (if (< n BLOCK-COUNT)
        (time-loop block (+ n 1) (update s block))
        s)))

(define* time-test (subr (maxeff bv (read @l) (alloc @l)) () string)
  (lambda ()
    (let* ((block (w8v-tabulate BLOCK-LEN (lambda (i) (modulo i 256))))
           (s (time-loop block 0 init))
           (hash (final s)))
      (to-hex-string hash))))

(time-test)
