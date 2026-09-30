;;; PSDES-RANDOM -- a pseudo-DES hash as a random number generator
;;; (Numerical Recipes in C, page 302), summing the words it makes.
;;;
;;; Written by Stephen Weeks (sweeks@sweeks.com).
;;; From MLton's benchmark suite (benchmark/tests/psdes-random.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched, and the file itself ends with `Main.doit 2`): 1 call of
;;; `once`, whose loop makes 300000 words, not the original's 150000000.
;;; Answer: 2419669511 (0wx90393A07), the sum of the words modulo 2^32 (for 150000000 words
;;; the original checks for 0wx132B1B67 = 321592167; this count's sum was
;;; computed by a Python transcription of the same code, which also gives
;;; 0wx132B1B67 for 150000000).
;;;
;;; Word32 arithmetic is int arithmetic masked to 32 bits: `+` and `*` are
;;; taken (modulo _ 4294967296), `>> (w, 0w16)` is (quotient w 65536),
;;; `<< (w, 0w16)` is (* (modulo w 65536) 65536), `notb` is 4294967295 - w.
;;; FX-26 has no bitwise operations, so `andb (w, 0wxffff)` is
;;; (modulo w 65536), `orb` of the two disjoint halves in `reverse` is `+`,
;;; and `xorb` is written here: a byte at a time, through a 256 x 256 table
;;; made once. That emulation, some 20 divisions and table reads for each
;;; xorb, is most of what this port spends its time on; hence the count.

;; ---- Word32 helpers (FX-26 has no bitwise operations).

(define word32 int 4294967296)

;; Bit k of xor, and the rest, by division: used only to fill the table.
(define* slow-xor8 (subr spin (int int int) int)
  (lambda (a b k)
    (if (= k 8)
        0
        (+ (if (= (modulo a 2) (modulo b 2)) 0 1)
           (* 2 (slow-xor8 (quotient a 2) (quotient b 2) (+ k 1)))))))

;; xor8[a][b] is the exclusive or of bytes a and b.
(define-type table (arrayof (arrayof int @w) @w))
(define* make-xor8 (subr (maxeff (alloc @w) (write @w) (read @w) spin) () table)
  (lambda ()
    (let ((t (the table (make-array 256 (the (arrayof int @w) (make-array 0 0))))))
      (letrec ((row (subr (maxeff (alloc @w) (write @w) spin (read (globals slow-xor8))) (int) unit)
                 (lambda (a)
                   (if (< a 256)
                       (let ((r (the (arrayof int @w) (make-array 256 0))))
                         (letrec ((col (subr (maxeff (write @w) spin (read (globals slow-xor8))) (int) unit)
                                    (lambda (b)
                                      (if (< b 256)
                                          (begin (array-set! r b (slow-xor8 a b 0)) (col (+ b 1)))
                                          #u))))
                           (begin (col 0) (array-set! t a r) (row (+ a 1)))))
                       #u))))
        (begin (row 0) t)))))
(define xor8 table (make-xor8))

;; Word32.xorb, a byte at a time.
(define* xorb (subr (read @w) (int int) int)
  (lambda (x y)
    (let* ((x1 (quotient x 256)) (y1 (quotient y 256))
           (x2 (quotient x1 256)) (y2 (quotient y1 256))
           (x3 (quotient x2 256)) (y3 (quotient y2 256)))
      (+ (array-ref (array-ref xor8 (modulo x 256)) (modulo y 256))
         (* 256 (+ (array-ref (array-ref xor8 (modulo x1 256)) (modulo y1 256))
                   (* 256 (+ (array-ref (array-ref xor8 (modulo x2 256)) (modulo y2 256))
                             (* 256 (array-ref (array-ref xor8 x3) y3))))))))))

;; ---- The benchmark.

;; Its input, where no compiler can fold it: a global, which a later
;; definition may replace. The original's 150000000.
(define count int 300000)

(define* once (subr (maxeff (read @w) (alloc @h) (read @h) (write @h) spin) () int)
  (lambda ()
    (letrec ((nat-fold (subr (maxeff (read @w) (alloc @h) (read @h) spin (read (globals word32 xorb xor8)))
                             (int int (productof (l int) (r int))
                                  (subr (maxeff (read @w) (alloc @h) (read @h) (read (globals word32 xorb xor8)))
                                        (int (productof (l int) (r int))) (productof (l int) (r int))))
                             (productof (l int) (r int)))
               (lambda (start stop ac f)
                 (letrec ((loop (subr (maxeff (read @w) (alloc @h) (read @h) spin (read (globals word32 xorb xor8)))
                                      (int (productof (l int) (r int))) (productof (l int) (r int)))
                            (lambda (i ac) (if (= i stop) ac (loop (+ i 1) (f i ac))))))
                   (loop start ac)))))
      (let* ((niter 4)
             (make (lambda ((l (listof int @h)))
                     (let ((a (the (arrayof int @h) (make-array 4 0))))
                       (letrec ((fill (subr (maxeff (read @h) (write @h) spin) (int (listof int @h)) unit)
                                  (lambda (i l) (if (null? l) #u (begin (array-set! a i (car l)) (fill (+ i 1) (cdr l)))))))
                         (begin (fill 0 l) (lambda ((i int)) (array-ref a i)))))))
             (c1 (make (list 3131664519 504877868 62770492 255054258)))
             (c2 (make (list 1259289432 3899977923 1767228838 1437059654)))
             (half 65536)
             (reverse (lambda ((w int)) (+ (quotient w half) (* (modulo w half) half))))
             (psdes (lambda ((lword int) (irword int))
                      (nat-fold 0 niter (product (l lword) (r irword))
                        (lambda (i p)
                          (let* ((lword (extract p l))
                                 (irword (extract p r))
                                 (ia (xorb irword (c1 i)))
                                 (itmpl (modulo ia 65536))
                                 (itmph (quotient ia half))
                                 (ib (modulo (+ (modulo (* itmpl itmpl) word32)
                                                (- 4294967295 (modulo (* itmph itmph) word32)))
                                             word32)))
                            (product (l irword)
                                     (r (xorb lword (modulo (+ (modulo (* itmpl itmph) word32)
                                                               (xorb (c2 i) (reverse ib)))
                                                            word32)))))))))
             (lword (the (ref int @h) (new 13)))
             (irword (the (ref int @h) (new 14)))
             (need-to (the (ref bool @h) (new #t)))
             (word (lambda ()
                     (if (get need-to)
                         (let ((p (psdes (get lword) (get irword))))
                           (begin
                             (set lword (extract p l))
                             (set irword (extract p r))
                             (set need-to #f)
                             (extract p l)))
                         (begin (set need-to #t) (get irword))))))
        (letrec ((loop (subr (maxeff (read @w) (alloc @h) (read @h) (write @h) spin (read (globals word32 xorb xor8))) (int int) int)
                   (lambda (i w)
                     (if (= i 0)
                         w
                         (loop (- i 1) (modulo (+ w (word)) word32))))))
          (loop count 0))))))

(once)
