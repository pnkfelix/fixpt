;;; MD5 -- the MD5 message digest of 10000-byte blocks, a quick and dirty
;;; transliteration of the RSA reference C code.
;;;
;;; Copyright (C) 2001 Daniel Wang. All rights reserved. Derived from the
;;; RSA Data Security, Inc. MD5 Message-Digest Algorithm.
;;; From MLton's benchmark suite (benchmark/tests/md5.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): 1 run of Test.time_test, with BLOCK_COUNT 20, not
;;; the original's 100000 (100000 blocks of 10000 bytes would take hours
;;; here, see below).
;;; Answer: "59ebddd335d8defbcaf5b76c08c64278", the digest's hex string,
;;; which Python's hashlib also gives for these bytes (for 100000 blocks,
;;; the original checks for "766a2bb5d24bddae466c572bcabca3ee", which
;;; hashlib gives too).
;;;
;;; Word32 arithmetic is int arithmetic masked to 32 bits: `+` is taken
;;; (modulo _ 4294967296), `<<` multiplies by a power of 2 and masks, `>>`
;;; is `quotient`, `notb` is 4294967295 - w, and ROTATE_LEFT's `orb` of two
;;; disjoint parts is `+`. FX-26 has no bitwise operations, so `andb`, `orb`
;;; and `xorb` are written here: a byte at a time, through 256 x 256 tables
;;; made once. That emulation, some 20 divisions and table reads for each,
;;; is most of what this port spends its time on; hence the block count.
;;; Word8Vector.vector is an array of ints, each a byte; the functions of
;;; W8V that the code uses are written here, and so are SML's records
;;; (products) and Test.do_tests is left out (it only prints).
;;; transform's 64 steps are split into four functions, one per round (the
;;; compiler makes a native frame too large for one `stp` of the whole, and
;;; runs such a function as cellular code); its 16 words go to them in an
;;; array (a product of 16 has no native code either).

;; ---- Word32 helpers (FX-26 has no bitwise operations).

(define word32 int 4294967296)

;; A bit at a time, by division: used only to fill the tables.
;; op 0 is and, 1 is or, 2 is xor.
(define* slow-bitop8 (subr spin (int int int int) int)
  (lambda (op a b k)
    (if (= k 8)
        0
        (let ((x (modulo a 2)) (y (modulo b 2)))
          (+ (cond ((= op 0) (* x y))
                   ((= op 1) (if (= (+ x y) 0) 0 1))
                   (else (if (= x y) 0 1)))
             (* 2 (slow-bitop8 op (quotient a 2) (quotient b 2) (+ k 1))))))))

;; A table [a][b] of bytes a op b.
(define-type table (arrayof (arrayof int @w) @w))
(define* make-table8 (subr (maxeff (alloc @w) (write @w) (read @w) spin) (int) table)
  (lambda (op)
    (let ((t (the table (make-array 256 (the (arrayof int @w) (make-array 0 0))))))
      (letrec ((row (subr (maxeff (alloc @w) (write @w) spin (read (globals slow-bitop8))) (int) unit)
                 (lambda (a)
                   (if (< a 256)
                       (let ((r (the (arrayof int @w) (make-array 256 0))))
                         (letrec ((col (subr (maxeff (write @w) spin (read (globals slow-bitop8))) (int) unit)
                                    (lambda (b)
                                      (if (< b 256)
                                          (begin (array-set! r b (slow-bitop8 op a b 0)) (col (+ b 1)))
                                          #u))))
                           (begin (col 0) (array-set! t a r) (row (+ a 1)))))
                       #u))))
        (begin (row 0) t)))))
(define and8 table (make-table8 0))
(define or8 table (make-table8 1))
(define xor8 table (make-table8 2))

;; x op y on 32-bit words, a byte at a time.
(define* bitop32 (subr (read @w) (table int int) int)
  (lambda (t x y)
    (let* ((x1 (quotient x 256)) (y1 (quotient y 256))
           (x2 (quotient x1 256)) (y2 (quotient y1 256))
           (x3 (quotient x2 256)) (y3 (quotient y2 256)))
      (+ (array-ref (array-ref t (modulo x 256)) (modulo y 256))
         (* 256 (+ (array-ref (array-ref t (modulo x1 256)) (modulo y1 256))
                   (* 256 (+ (array-ref (array-ref t (modulo x2 256)) (modulo y2 256))
                             (* 256 (array-ref (array-ref t x3) y3))))))))))
(define* andb (subr (read @w) (int int) int) (lambda (x y) (bitop32 and8 x y)))
(define* orb (subr (read @w) (int int) int) (lambda (x y) (bitop32 or8 x y)))
(define* xorb (subr (read @w) (int int) int) (lambda (x y) (bitop32 xor8 x y)))
(define* notb (subr pure (int) int) (lambda (x) (- 4294967295 x)))
(define* add32 (subr pure (int int) int) (lambda (x y) (modulo (+ x y) word32)))

;; 2^n, for shifts.
(define* pow2 (subr spin (int) int) (lambda (n) (if (= n 0) 1 (* 2 (pow2 (- n 1))))))
(define* shl (subr spin (int int) int) (lambda (x n) (modulo (* x (pow2 n)) word32)))
(define* shr (subr spin (int int) int) (lambda (x n) (quotient x (pow2 n))))

;; ---- Word8Vector, as arrays of bytes.

(define-type bytes (arrayof int @v))

(define* w8v-tabulate (subr (maxeff (alloc @v) (write @v) spin) (int (subr pure (int) int)) bytes)
  (lambda (n f)
    (let ((v (the bytes (make-array n 0))))
      (letrec ((fill (subr (maxeff (write @v) spin) (int) unit)
                 (lambda (i) (if (< i n) (begin (array-set! v i (f i)) (fill (+ i 1))) #u))))
        (begin (fill 0) v)))))

;; W8V.extract (vec, s, SOME l), by tabulate as the original's.
(define* w8v-extract (subr (maxeff (alloc @v) (write @v) (read @v) spin) (bytes int int) bytes)
  (lambda (vec s l)
    (let ((v (the bytes (make-array l 0))))
      (letrec ((fill (subr (maxeff (write @v) (read @v) spin) (int) unit)
                 (lambda (i) (if (< i l) (begin (array-set! v i (array-ref vec (+ s i))) (fill (+ i 1))) #u))))
        (begin (fill 0) v)))))

;; W8V.concat [a, b]: the original only ever concatenates two.
(define* w8v-concat2 (subr (maxeff (alloc @v) (write @v) (read @v) spin) (bytes bytes) bytes)
  (lambda (a b)
    (let* ((na (array-length a))
           (v (the bytes (make-array (+ na (array-length b)) 0))))
      (letrec ((fill (subr (maxeff (write @v) (read @v) spin) (int) unit)
                 (lambda (i)
                   (if (< i (array-length v))
                       (begin (array-set! v i (if (< i na) (array-ref a i) (array-ref b (- i na))))
                              (fill (+ i 1)))
                       #u))))
        (begin (fill 0) v)))))

(define* w8v-from-list (subr (maxeff (alloc @v) (write @v) (read @l) spin) ((listof int @l)) bytes)
  (lambda (l)
    (letrec ((len (subr (maxeff (read @l) spin) ((listof int @l) int) int)
               (lambda (l n) (if (null? l) n (len (cdr l) (+ n 1))))))
      (let ((v (the bytes (make-array (len l 0) 0))))
        (letrec ((fill (subr (maxeff (write @v) (read @l) spin) (int (listof int @l)) unit)
                   (lambda (i l) (if (null? l) #u (begin (array-set! v i (car l)) (fill (+ i 1) (cdr l)))))))
          (begin (fill 0 l) v))))))

;; PackWord32Little.subVec (buf, i): the ith 32-bit word, little-endian.
(define* sub-vec (subr (read @v) (bytes int) int)
  (lambda (buf i)
    (let ((at (* i 4)))
      (+ (array-ref buf at)
         (* 256 (+ (array-ref buf (+ at 1))
                   (* 256 (+ (array-ref buf (+ at 2))
                             (* 256 (array-ref buf (+ at 3)))))))))))

;; ---- structure MD5

(define-type word64 (productof (hi int) (lo int)))
(define-type word128 (productof (A int) (B int) (C int) (D int)))
(define-type md5state (productof (digest word128) (mlen word64) (buf bytes)))

(define w64-zero word64 (product (hi 0) (lo 0)))

(define* mul8add (subr spin (word64 int) word64)
  (lambda (w n)
    (let* ((mul8lo (shl n 3))
           (mul8hi (shr n 29))
           (lo (add32 (extract w lo) mul8lo))
           (cout (if (< lo mul8lo) 1 0))
           (hi (add32 mul8hi (add32 (extract w hi) cout))))
      (product (hi hi) (lo lo)))))

(define* pack-little (subr (maxeff (read @l) (alloc @l) (alloc @v) (write @v) spin) ((listof int @l)) bytes)
  (lambda (wrds)
    (letrec ((loop (subr (maxeff (read @l) (alloc @l) spin (read (globals pow2 shr word32))) ((listof int @l)) (listof int @l))
               (lambda (ws)
                 (if (null? ws)
                     nil
                     (let* ((w (car ws))
                            (b0 (modulo w 256))
                            (b1 (modulo (shr w 8) 256))
                            (b2 (modulo (shr w 16) 256))
                            (b3 (modulo (shr w 24) 256)))
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

(define* PADDING (subr (maxeff (alloc @v) (write @v) spin) (int) bytes)
  (lambda (i) (w8v-tabulate i (lambda (k) (if (= k 0) 128 0)))))

(define* F (subr (read @w) (int int int) int) (lambda (x y z) (orb (andb x y) (andb (notb x) z))))
(define* G (subr (read @w) (int int int) int) (lambda (x y z) (orb (andb x z) (andb y (notb z)))))
(define* H (subr (read @w) (int int int) int) (lambda (x y z) (xorb x (xorb y z))))
(define* I (subr (read @w) (int int int) int) (lambda (x y z) (xorb y (orb x (notb z)))))
(define* ROTATE-LEFT (subr spin (int int) int)
  (lambda (x n) (+ (shl x n) (shr x (- 32 n)))))

(define-type fn3 (subr (maxeff (read @w) (read @globals)) (int int int) int))
(define-type step (subr (maxeff (read @w) spin (read @globals)) (int int int int int int int) int))

(define XX (subr pure (fn3) step)
  (lambda (f)
    (lambda (a b c d x s ac)
      (let* ((a (add32 a (add32 (add32 (f b c d) x) ac)))
             (a (ROTATE-LEFT a s)))
        (add32 a b)))))

(define FF step (XX F))
(define GG step (XX G))
(define HH step (XX H))
(define II step (XX I))

(define empty-buf bytes (w8v-tabulate 0 (lambda (x) 0)))
(define init md5state
  (product (digest (product (A 1732584193) (B 4023233417) (C 2562383102) (D 271733878)))
           (mlen w64-zero)
           (buf empty-buf)))

;; The sixteen words of a block, fetched once (the original fetches them
;; into sixteen variables "to avoid range checks"). Changed: the original's
;; transform is one function of 64 steps; here each round of 16 is a
;; function of its own, taking the block's words in an array, since one
;; function of all 64 makes a native frame too large (see the header).
(define-type xwords (arrayof int @v))

;; Round 1
(define* round1 (subr (maxeff (read @w) (read @v) spin (read @globals)) (word128 xwords) word128)
  (lambda (dg xs)
    (let* ((a (extract dg A)) (b (extract dg B)) (c (extract dg C)) (d (extract dg D))
           (a (FF a b c d (array-ref xs 0) S11 3614090360)) ; 1
           (d (FF d a b c (array-ref xs 1) S12 3905402710)) ; 2
           (c (FF c d a b (array-ref xs 2) S13 606105819)) ; 3
           (b (FF b c d a (array-ref xs 3) S14 3250441966)) ; 4
           (a (FF a b c d (array-ref xs 4) S11 4118548399)) ; 5
           (d (FF d a b c (array-ref xs 5) S12 1200080426)) ; 6
           (c (FF c d a b (array-ref xs 6) S13 2821735955)) ; 7
           (b (FF b c d a (array-ref xs 7) S14 4249261313)) ; 8
           (a (FF a b c d (array-ref xs 8) S11 1770035416)) ; 9
           (d (FF d a b c (array-ref xs 9) S12 2336552879)) ; 10
           (c (FF c d a b (array-ref xs 10) S13 4294925233)) ; 11
           (b (FF b c d a (array-ref xs 11) S14 2304563134)) ; 12
           (a (FF a b c d (array-ref xs 12) S11 1804603682)) ; 13
           (d (FF d a b c (array-ref xs 13) S12 4254626195)) ; 14
           (c (FF c d a b (array-ref xs 14) S13 2792965006)) ; 15
           (b (FF b c d a (array-ref xs 15) S14 1236535329)) ; 16
           )
      (product (A a) (B b) (C c) (D d)))))

;; Round 2
(define* round2 (subr (maxeff (read @w) (read @v) spin (read @globals)) (word128 xwords) word128)
  (lambda (dg xs)
    (let* ((a (extract dg A)) (b (extract dg B)) (c (extract dg C)) (d (extract dg D))
           (a (GG a b c d (array-ref xs 1) S21 4129170786)) ; 17
           (d (GG d a b c (array-ref xs 6) S22 3225465664)) ; 18
           (c (GG c d a b (array-ref xs 11) S23 643717713)) ; 19
           (b (GG b c d a (array-ref xs 0) S24 3921069994)) ; 20
           (a (GG a b c d (array-ref xs 5) S21 3593408605)) ; 21
           (d (GG d a b c (array-ref xs 10) S22 38016083)) ; 22
           (c (GG c d a b (array-ref xs 15) S23 3634488961)) ; 23
           (b (GG b c d a (array-ref xs 4) S24 3889429448)) ; 24
           (a (GG a b c d (array-ref xs 9) S21 568446438)) ; 25
           (d (GG d a b c (array-ref xs 14) S22 3275163606)) ; 26
           (c (GG c d a b (array-ref xs 3) S23 4107603335)) ; 27
           (b (GG b c d a (array-ref xs 8) S24 1163531501)) ; 28
           (a (GG a b c d (array-ref xs 13) S21 2850285829)) ; 29
           (d (GG d a b c (array-ref xs 2) S22 4243563512)) ; 30
           (c (GG c d a b (array-ref xs 7) S23 1735328473)) ; 31
           (b (GG b c d a (array-ref xs 12) S24 2368359562)) ; 32
           )
      (product (A a) (B b) (C c) (D d)))))

;; Round 3
(define* round3 (subr (maxeff (read @w) (read @v) spin (read @globals)) (word128 xwords) word128)
  (lambda (dg xs)
    (let* ((a (extract dg A)) (b (extract dg B)) (c (extract dg C)) (d (extract dg D))
           (a (HH a b c d (array-ref xs 5) S31 4294588738)) ; 33
           (d (HH d a b c (array-ref xs 8) S32 2272392833)) ; 34
           (c (HH c d a b (array-ref xs 11) S33 1839030562)) ; 35
           (b (HH b c d a (array-ref xs 14) S34 4259657740)) ; 36
           (a (HH a b c d (array-ref xs 1) S31 2763975236)) ; 37
           (d (HH d a b c (array-ref xs 4) S32 1272893353)) ; 38
           (c (HH c d a b (array-ref xs 7) S33 4139469664)) ; 39
           (b (HH b c d a (array-ref xs 10) S34 3200236656)) ; 40
           (a (HH a b c d (array-ref xs 13) S31 681279174)) ; 41
           (d (HH d a b c (array-ref xs 0) S32 3936430074)) ; 42
           (c (HH c d a b (array-ref xs 3) S33 3572445317)) ; 43
           (b (HH b c d a (array-ref xs 6) S34 76029189)) ; 44
           (a (HH a b c d (array-ref xs 9) S31 3654602809)) ; 45
           (d (HH d a b c (array-ref xs 12) S32 3873151461)) ; 46
           (c (HH c d a b (array-ref xs 15) S33 530742520)) ; 47
           (b (HH b c d a (array-ref xs 2) S34 3299628645)) ; 48
           )
      (product (A a) (B b) (C c) (D d)))))

;; Round 4
(define* round4 (subr (maxeff (read @w) (read @v) spin (read @globals)) (word128 xwords) word128)
  (lambda (dg xs)
    (let* ((a (extract dg A)) (b (extract dg B)) (c (extract dg C)) (d (extract dg D))
           (a (II a b c d (array-ref xs 0) S41 4096336452)) ; 49
           (d (II d a b c (array-ref xs 7) S42 1126891415)) ; 50
           (c (II c d a b (array-ref xs 14) S43 2878612391)) ; 51
           (b (II b c d a (array-ref xs 5) S44 4237533241)) ; 52
           (a (II a b c d (array-ref xs 12) S41 1700485571)) ; 53
           (d (II d a b c (array-ref xs 3) S42 2399980690)) ; 54
           (c (II c d a b (array-ref xs 10) S43 4293915773)) ; 55
           (b (II b c d a (array-ref xs 1) S44 2240044497)) ; 56
           (a (II a b c d (array-ref xs 8) S41 1873313359)) ; 57
           (d (II d a b c (array-ref xs 15) S42 4264355552)) ; 58
           (c (II c d a b (array-ref xs 6) S43 2734768916)) ; 59
           (b (II b c d a (array-ref xs 13) S44 1309151649)) ; 60
           (a (II a b c d (array-ref xs 4) S41 4149444226)) ; 61
           (d (II d a b c (array-ref xs 11) S42 3174756917)) ; 62
           (c (II c d a b (array-ref xs 2) S43 718787259)) ; 63
           (b (II b c d a (array-ref xs 9) S44 3951481745)) ; 64
           )
      (product (A a) (B b) (C c) (D d)))))

(define* transform (subr (maxeff (read @w) (read @v) (alloc @v) (write @v) spin (read @globals)) (word128 int bytes) word128)
  (lambda (dg i buf)
    (let* ((off (quotient i 4))
           (x (lambda ((n int)) (sub-vec buf (+ n off))))
           (xs (the xwords (make-array 16 0)))
           (fetch (letrec ((fetch (subr (maxeff (read @v) (write @v) spin (read (globals sub-vec))) (int) unit)
                             (lambda (n) (if (< n 16) (begin (array-set! xs n (x n)) (fetch (+ n 1))) #u))))
                    (fetch 0)))
           (r (round4 (round3 (round2 (round1 dg xs) xs) xs) xs)))
      (product (A (add32 (extract dg A) (extract r A)))
               (B (add32 (extract dg B) (extract r B)))
               (C (add32 (extract dg C) (extract r C)))
               (D (add32 (extract dg D) (extract r D)))))))

(define* update (subr (maxeff (read @w) (read @v) (alloc @v) (write @v) spin (read @globals)) (md5state bytes) md5state)
  (lambda (st input)
    (let* ((buf (extract st buf))
           (digest (extract st digest))
           (mlen (extract st mlen))
           (input-len (array-length input))
           (need-bytes (- 64 (array-length buf))))
      (letrec ((loop (subr (maxeff (read @w) (read @v) (alloc @v) (write @v) spin (read @globals)) (int word128) (productof (i int) (digest word128)))
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

(define* final (subr (maxeff (read @w) (read @v) (alloc @v) (write @v) (read @l) (alloc @l) spin (read @globals)) (md5state) bytes)
  (lambda (state)
    (let* ((lo (extract (extract state mlen) lo))
           (hi (extract (extract state mlen) hi))
           (bits (pack-little (the (listof int @l) (cons lo (cons hi nil)))))
           (index (array-length (extract state buf)))
           (pad-len (if (< index 56) (- 56 index) (- 120 index)))
           (state (update state (PADDING pad-len)))
           (dg (extract (update state bits) digest)))
      (pack-little (the (listof int @l) (cons (extract dg A) (cons (extract dg B) (cons (extract dg C) (cons (extract dg D) nil)))))))))

(define hxd string "0123456789abcdef")

(define* to-hex-string (subr (maxeff (read @v) (alloc @l) (read @l) spin) (bytes) string)
  (lambda (v)
    (let ((hxd hxd))
      (letrec ((foldr (subr (maxeff (read @v) (alloc @l) spin) (int (listof char @l)) (listof char @l))
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

(define* time-test (subr (maxeff (read @w) (read @v) (alloc @v) (write @v) (read @l) (alloc @l) spin (read @globals)) () string)
  (lambda ()
    (let ((block (w8v-tabulate BLOCK-LEN (lambda (i) (modulo i 256)))))
      (letrec ((loop (subr (maxeff (read @w) (read @v) (alloc @v) (write @v) spin (read @globals)) (int md5state) md5state)
                 (lambda (n s)
                   (if (< n BLOCK-COUNT)
                       (loop (+ n 1) (update s block))
                       s))))
        (let* ((s (loop 0 init))
               (hash (final s)))
          (to-hex-string hash))))))

(time-test)
