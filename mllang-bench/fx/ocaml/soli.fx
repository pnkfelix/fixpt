;;; SOLI -- peg solitaire on the English board, by depth-first search.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc-unsafe/
;;; soli.ml, ocaml commit 7da997d28b1a), ported to FX-26. The original
;;; solves the board once, printing the count of positions tried at every
;;; 500th, then the solved board. The port solves it `iterations` = 100
;;; times, each from a fresh board, and prints nothing: its value is the
;;; count of positions tried by the last solve, provided the solved board,
;;; as `print_board` would print it, is the reference's last nine lines
;;; (else 0). Answer: 20277; the reference's counts end at 20000, so the
;;; count is between 20000 and 20499, as it is.
;;;
;;; What the port changes:
;;; - The pegs are a `define-datatype`, and its three values are made once,
;;;   as globals, where OCaml's constant constructors are immediates.
;;; - The board is built from strings, a row each, by a small builder, in
;;;   `print_peg`'s characters; records are products.
;;; - `for` loops are local recursive procedures.
;;; - `exception Found`, raised within a `solve` and caught by the same
;;;   `solve`, is a prompt tag; each `solve` has its prompt, and the loops
;;;   that abort to it are bound inside that prompt, so their types, which
;;;   mention its region, do not stop it delimiting.
;;; - The count is printed every 500 in the original; the port drops that.
;;;   The counter is a global ref, reset for each solve.

(define-datatype peg (out) (empty) (peg))
(define the-out peg (out))
(define the-empty peg (empty))
(define the-peg peg (peg))

(define-type row (arrayof peg @heap))
(define-type board-type (arrayof row @heap))

(define is-peg? (subr pure (peg) bool)
  (lambda (p) (tagcase p (peg () #t) (else x #f))))
(define is-empty? (subr pure (peg) bool)
  (lambda (p) (tagcase p (empty () #t) (else x #f))))

;; A row of the board, from how `print_peg` shows it.
(define* row-of (subr (maxeff (alloc @heap) (write @heap) spin) (string) row)
  (lambda (s)
    (let ((r (the row (make-array 9 the-out))))
      (letrec ((fill (subr (maxeff (write @heap) spin (read (globals the-out the-empty the-peg))) (int) row)
                 (lambda (j)
                   (if (= j 9)
                       r
                       (let ((c (string-ref s j)))
                         (begin
                           (array-set! r j (cond ((char=? c #\.) the-out)
                                                 ((char=? c #\space) the-empty)
                                                 (else the-peg)))
                           (fill (+ j 1))))))))
        (fill 0)))))

(define* make-board (subr (maxeff (alloc @heap) (write @heap) spin) () board-type)
  (lambda ()
    (let ((b (the board-type (make-array 9 (the row (make-array 0 the-out))))))
      (begin
        (array-set! b 0 (row-of "........."))
        (array-set! b 1 (row-of "...$$$..."))
        (array-set! b 2 (row-of "...$$$..."))
        (array-set! b 3 (row-of ".$$$$$$$."))
        (array-set! b 4 (row-of ".$$$ $$$."))
        (array-set! b 5 (row-of ".$$$$$$$."))
        (array-set! b 6 (row-of "...$$$..."))
        (array-set! b 7 (row-of "...$$$..."))
        (array-set! b 8 (row-of "........."))
        b))))

(define board (ref board-type @heap) (new (make-board)))

(define print-peg (subr pure (peg) string)
  (lambda (p) (tagcase p (out () ".") (empty () " ") (peg () "$"))))

;; The board as `print_board` prints it, a newline after each row.
(define* print-board (subr (maxeff (read @heap) spin) (board-type) string)
  (lambda (b)
    (letrec ((rows (subr (maxeff (read @heap) spin (read (globals print-peg))) (int int string) string)
               (lambda (i j acc)
                 (cond ((= i 9) acc)
                       ((= j 9) (rows (+ i 1) 0 (string-append acc "\n")))
                       (else (rows i (+ j 1) (string-append acc (print-peg (array-ref (array-ref b i) j)))))))))
      (rows 0 0 ""))))

(define-type direction (productof (dx int) (dy int)))

(define dir (arrayof direction @heap)
  (let ((d (the (arrayof direction @heap) (make-array 4 (product (dx 0) (dy 1))))))
    (begin
      (array-set! d 1 (product (dx 1) (dy 0)))
      (array-set! d 2 (product (dx 0) (dy -1)))
      (array-set! d 3 (product (dx -1) (dy 0)))
      d)))

(define-type move (productof (x1 int) (y1 int) (x2 int) (y2 int)))

(define moves (arrayof move @heap) (make-array 31 (product (x1 0) (y1 0) (x2 0) (y2 0))))

(define counter (ref int @heap) (new 0))

;; exception Found
(define found (prompt-tag bool unit (maxeff (read @heap) (write @heap) spin (read @globals)) @f)
  (make-continuation-prompt-tag))

(define* solve (subr (maxeff (read @heap) (write @heap) spin (read @globals)) (int) bool)
  (lambda (m)
    (let ((board (get board)))
      (begin
        (set counter (+ (get counter) 1))
        (if (= m 31)
            (is-peg? (array-ref (array-ref board 4) 4))
            (prompt found
              (letrec ((loop-k (subr (maxeff (read @heap) (write @heap) spin (goto @f) (read @globals)) (int int int) unit)
                         (lambda (i j k)
                           (if (<= k 3)
                               (let* ((d1 (extract (array-ref dir k) dx))
                                      (d2 (extract (array-ref dir k) dy))
                                      (i1 (+ i d1))
                                      (i2 (+ i1 d1))
                                      (j1 (+ j d2))
                                      (j2 (+ j1 d2)))
                                 (begin
                                   (if (and (is-peg? (array-ref (array-ref board i1) j1))
                                            (is-empty? (array-ref (array-ref board i2) j2)))
                                       (begin
                                         (array-set! (array-ref board i) j the-empty)
                                         (array-set! (array-ref board i1) j1 the-empty)
                                         (array-set! (array-ref board i2) j2 the-peg)
                                         (if (solve (+ m 1))
                                             (begin
                                               (array-set! moves m (product (x1 i) (y1 j) (x2 i2) (y2 j2)))
                                               (abort-current-continuation found #u))
                                             #u)
                                         (array-set! (array-ref board i) j the-peg)
                                         (array-set! (array-ref board i1) j1 the-peg)
                                         (array-set! (array-ref board i2) j2 the-empty))
                                       #u)
                                   (loop-k i j (+ k 1))))
                               #u)))
                       (loop-j (subr (maxeff (read @heap) (write @heap) spin (goto @f) (read @globals)) (int int) unit)
                         (lambda (i j)
                           (if (<= j 7)
                               (begin
                                 (if (is-peg? (array-ref (array-ref board i) j)) (loop-k i j 0) #u)
                                 (loop-j i (+ j 1)))
                               #u)))
                       (loop-i (subr (maxeff (read @heap) (write @heap) spin (goto @f) (read @globals)) (int) unit)
                         (lambda (i)
                           (if (<= i 7)
                               (begin (loop-j i 1) (loop-i (+ i 1)))
                               #u))))
                (begin (loop-i 1) #f))
              (lambda (u) #t)))))))

;; The reference output's last nine lines: the solved board.
(define solved string
  (string-append ".........\n...   ...\n...   ...\n.       .\n.   $   .\n"
                 ".       .\n...   ...\n...   ...\n.........\n"))

;; The input, where no compiler can fold it: a global.
(define iterations int 100)

(define* main (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) () int)
  (lambda ()
    (begin
      (set board (make-board))
      (set counter 0)
      (if (and (solve 0) (string=? (print-board (get board)) solved))
          (get counter)
          0))))

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (main)))))
(run iterations 0)
