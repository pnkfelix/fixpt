;;; PSDES-RANDOM -- a pseudo-DES hash as a random number generator
;;; (Numerical Recipes in C, page 302), summing the words it makes.
;;;
;;; Written by Stephen Weeks (sweeks@sweeks.com).
;;; From MLton's benchmark suite (benchmark/tests/psdes-random.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched, and the file itself ends with `Main.doit 2`): 1 call of
;;; `once`, whose loop makes 300000 words, not the original's 150000000.
;;; Answer: 2419669511 (0wx90393A07), the sum of the words modulo 2^32 (for
;;; 150000000 words the original checks for 0wx132B1B67 = 321592167; this
;;; count's sum was computed by a Python transcription of the same code,
;;; which also gives 0wx132B1B67 for 150000000).
;;;
;;; Word32 is `u32`, whose arithmetic wraps as Word32's does: `+`, `*`,
;;; `xorb`, `andb`, `orb`, `notb`, `>>` and `<<` are `u32+`, `u32*`,
;;; `u32-xor`, `u32-and`, `u32-or`, `u32-not`, `u32-shr` and `u32-shl`.
;;; FX-26 has no literals of type u32, so each constant is `int->u32` of
;;; an int. The answer is the sum's `u32->int`. (Until FX-26 had `u32`,
;;; this port did the same with ints masked to 32 bits, `xorb` a byte at a
;;; time through a table; that emulation was most of what it measured.)
;;; `once`'s loop does not check the sum (the original raises Fail "bug"
;;; if it differs); it returns it.

(define-type words (productof (l u32) (r u32)))
(define-type ints (listof int acyclic))
(define-type lookup (subr (read @h) (int) u32))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace. The original's 150000000.
(define count int 300000)

;; What the words' closures do.
(define-effect ps (maxeff (read @h) (write @h) (alloc @h) spin))

(define* nat-fold (subr ps (int int words (subr ps (int words) words)) words)
  (lambda (start stop ac f)
    (letrec ((loop (subr ps (int words) words)
               (lambda (i ac) (if (= i stop) ac (loop (+ i 1) (f i ac))))))
      (loop start ac))))

(define* fill (subr (maxeff (write @h) spin) ((arrayof u32 @h) int ints) unit)
  (lambda (a i l)
    (if (null? l) #u (begin (array-set! a i (int->u32 (car l))) (fill a (+ i 1) (cdr l))))))

;; `make`: the list's elements, in an array, looked up by index.
(define* make (subr (maxeff (alloc @h) (write @h) spin) (ints) lookup)
  (lambda (l)
    (let ((a (the (arrayof u32 @h) (make-array 4 (int->u32 0)))))
      (begin (fill a 0 l) (lambda (i) (array-ref a i))))))

(define* once (subr ps () int)
  (lambda ()
    (let* ((niter 4)
           (c1 (make (list 3131664519 504877868 62770492 255054258)))
           (c2 (make (list 1259289432 3899977923 1767228838 1437059654)))
           (half 16)
           (reverse (lambda ((w u32)) (u32-or (u32-shr w half) (u32-shl w half))))
           (mask (int->u32 65535))
           (psdes (lambda ((lword u32) (irword u32))
                    (nat-fold 0 niter (product (l lword) (r irword))
                      (lambda (i p)
                        (let* ((lword (extract p l))
                               (irword (extract p r))
                               (ia (u32-xor irword (c1 i)))
                               (itmpl (u32-and ia mask))
                               (itmph (u32-shr ia half))
                               (ib (u32+ (u32* itmpl itmpl) (u32-not (u32* itmph itmph)))))
                          (product (l irword)
                                   (r (u32-xor lword
                                               (u32+ (u32* itmpl itmph)
                                                     (u32-xor (c2 i) (reverse ib)))))))))))
           (lword (the (ref u32 @h) (new (int->u32 13))))
           (irword (the (ref u32 @h) (new (int->u32 14))))
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
      (letrec ((loop (subr (maxeff ps (read (globals nat-fold))) (int u32) u32)
                 (lambda (i w) (if (= i 0) w (loop (- i 1) (u32+ w (word)))))))
        (u32->int (loop count (int->u32 0)))))))

(once)
