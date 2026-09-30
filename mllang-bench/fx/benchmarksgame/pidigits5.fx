;;; PIDIGITS5 -- the first N digits of pi, by the unbounded spigot on a
;;; numerator, denominator and accumulator, printed ten to a line.
;;;
;;; The Computer Language Benchmarks Game; contributed by Christophe
;;; Troestler, modified by Matías Giovannini, using Zarith with changes
;;; inspired by Tony Tavener's C program.
;;; From Sandmark's Benchmarks Game programs (benchmarks/benchmarksgame/
;;; pidigits5.ml), ported to FX-26. Count: N = 3000 digits (ours: the
;;; original takes N from the command line, 27 without one).
;;; Where the original prints, the port hashes: each character printed
;;; updates h := (h * 131 + code) mod 1000000007, from h = 0.
;;; Answer: 112361924, that hash of the 3000 digits' 4992 characters of
;;; output, which a Python transcription of the same program also gives
;;; (for N = 27 both hash the Benchmarks Game's expected output,
;;; "3141592653\t:10\n5897932384\t:20\n6264338   \t:27\n", to 644232395).
;;;
;;; What changed:
;;; - Zarith's Z.t is `int`, exact at any size; `Z.(/)` truncates, as
;;;   `quotient` does, and `to_int` is the identity.
;;; - The triple (num, den, acc) is a product; curried functions take
;;;   their arguments together.
;;; - Printing is hashing, the hash passed along `digit`'s loop; `%*s` of
;;;   "" is that many spaces, and `%i` is `int->string`.

(define-type state (productof (num int) (den int) (acc int)))

(define init state (product (num 1) (den 1) (acc 0)))

(define* extract-digit (subr pure (state int) int)
  (lambda (z nth) (quotient (+ (* nth (extract z num)) (extract z acc)) (extract z den))))

(define* next (subr pure (state) int) (lambda (z) (extract-digit z 3)))

(define* safe (subr pure (state int) bool) (lambda (z n) (= (extract-digit z 4) n)))

(define* prod (subr pure (state int) state)
  (lambda (z d)
    (product (num (* 10 (extract z num)))
             (den (extract z den))
             (acc (* 10 (- (extract z acc) (* (extract z den) d)))))))

(define* cons-lft (subr pure (state int) state)
  (lambda (z k)
    (let ((k2 (+ (* k 2) 1)) (num (extract z num)))
      (product (num (* k num))
               (den (* k2 (extract z den)))
               (acc (* k2 (+ (+ (extract z acc) num) num)))))))

(define columns int 10)

;; ---- Printing, hashed.

(define* hash-char (subr pure (int char) int)
  (lambda (h c) (modulo (+ (* h 131) (char->integer c)) 1000000007)))

(define* hash-string (subr spin (int string) int)
  (lambda (h s)
    (letrec ((loop (subr (maxeff spin (read (globals hash-char))) (int int) int)
               (lambda (h i)
                 (if (< i (string-length s)) (loop (hash-char h (string-ref s i)) (+ i 1)) h))))
      (loop h 0))))

(define* hash-spaces (subr spin (int int) int)
  (lambda (h n) (if (<= n 0) h (hash-spaces (hash-char h #\space) (- n 1)))))

;; Printf "\t:%i\n" row.
(define* hash-row-end (subr spin (int int) int)
  (lambda (h row) (hash-string (hash-string h (string-append "\t:" (int->string row))) "\n")))

;; ---- The spigot.

(define* digit (subr spin (int state int int int int) int)
  (lambda (k z n row col h)
    (if (= n 0)
        (hash-row-end (hash-spaces h (- columns col)) (+ row col))
        (let ((d (next z)))
          (if (safe z d)
              (if (= col columns)
                  (let ((row (+ row col)))
                    (digit k (prod z d) (- n 1) row 1
                           (hash-string (hash-row-end h row) (int->string d))))
                  (digit k (prod z d) (- n 1) row (+ col 1) (hash-string h (int->string d))))
              (digit (+ k 1) (cons-lft z k) n row col h))))))

(define* digits (subr spin (int) int) (lambda (n) (digit 1 init n 0 0 0)))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define input int 3000)

(digits input)
