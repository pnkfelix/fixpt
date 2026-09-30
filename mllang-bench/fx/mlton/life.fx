;;; LIFE -- Conway's game of life, on lists of coordinates, 25000
;;; generations of a glider gun, then plotted as lines of text.
;;;
;;; From the SML/NJ benchmark suite, by way of MLton's benchmark suite
;;; (benchmark/tests/life.sml, commit aa2fd1ad9b91), ported to FX-26.
;;; Iteration count (ours; MLton's driver was not fetched): (doit 1), each
;;; running 25000 generations of `gun` and plotting the last.
;;; Answer: 205, the number of characters the plot comes to, newlines
;;; included (the last generation has 28 live cells, 14 lines plotted).
;;; The original's `doit` shows the plot with a `pr` that does nothing; here
;;; `pr` adds the length of what it is given to a counter, which is the
;;; answer (`testit` prints the same lines to a stream).
;;;
;;; Changed, as FX-26 needs:
;;; - SML's curried functions take their arguments together; partial
;;;   applications (`member living`, `filter (lexless a)`, `C cons`) become
;;;   lambdas, and `o` is written out as the calls it makes.
;;; - Coordinates (int * int) are pairs, `cons`, `car` and `cdr` (as
;;;   products, a procedure that extracts a field, inlined into its caller,
;;;   leaves the caller with no native code); `accumulate`, used at two
;;;   result types, is a `poly`; `@` is `append2`; SML's `concat` is
;;;   written here.
;;; - `repeat`'s check of a negative count, which would raise ex_undefined,
;;;   is left out: `copy` is only ever given a count that is not negative.
;;; - The abstype `generation` is its list of coordinates.
;;; - Procedures passed as arguments read globals at large, `(read @globals)`.

(define-type coord (pairof int int @l))
(define-type coords (listof coord @l))
(define-type strings (listof string @l))

(define* map (subr (maxeff (read @l) (alloc @l) spin (read @globals)) ((subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coord) coord) coords) coords)
  (lambda (f l) (if (null? l) nil (cons (f (car l)) (map f (cdr l))))))

(define accumulate (poly ((t type)) (subr (maxeff (read @l) (alloc @l) spin (read @globals)) ((subr (maxeff (read @l) (alloc @l) spin (read @globals)) (t coord) t) t coords) t))
  (plambda ((t type))
    (lambda (f a l)
      (letrec ((foldf (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (t coords) t)
                 (lambda (a l) (if (null? l) a (foldf (f a (car l)) (cdr l))))))
        (foldf a l)))))

(define* filter (subr (maxeff (read @l) (alloc @l) spin (read @globals)) ((subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coord) bool) coords) coords)
  (lambda (p l)
    (reverse ((proj accumulate coords) (lambda (x a) (if (p a) (cons a x) x)) nil l))))

(define* exists (subr (maxeff (read @l) (alloc @l) spin (read @globals)) ((subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coord) bool) coords) bool)
  (lambda (p l) (if (null? l) #f (if (p (car l)) #t (exists p (cdr l))))))

(define* equal (subr (read @l) (coord coord) bool)
  (lambda (a b) (and (= (car a) (car b)) (= (cdr a) (cdr b)))))

(define* member (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords coord) bool)
  (lambda (x a) (exists (lambda (b) (equal a b)) x)))

(define* revonto (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords coords) coords)
  (lambda (x l) ((proj accumulate coords) (lambda (acc b) (cons b acc)) x l)))

(define* length (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords) int)
  (lambda (x) ((proj accumulate int) (lambda (n a) (+ n 1)) 0 x)))

(define* repeat (subr (maxeff (read @l) (alloc @l) spin (read @globals)) ((subr (maxeff (read @l) (alloc @l) spin (read @globals)) (strings) strings) int strings) strings)
  (lambda (f n x)
    (letrec ((rptf (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (int strings) strings)
               (lambda (n x) (if (= n 0) x (rptf (- n 1) (f x))))))
      (rptf n x))))

(define* copy (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (int string) strings)
  (lambda (n x) (repeat (lambda (l) (cons x l)) n nil)))

(define* concat (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (strings) string)
  (lambda (ss) (if (null? ss) "" (string-append (car ss) (concat (cdr ss))))))

(define* spaces (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (int) string) (lambda (n) (concat (copy n " "))))

(define* append2 (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords coords) coords)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append2 (cdr xs) ys)))))

(define* lexless (subr (read @l) (coord coord) bool)
  (lambda (p1 p2)
    (let ((a1 (car p1)) (b1 (cdr p1)) (a2 (car p2)) (b2 (cdr p2)))
      (if (< a2 a1) #t (if (= a2 a1) (< b2 b1) #f)))))

(define* lexgreater (subr (read @l) (coord coord) bool)
  (lambda (pr1 pr2) (lexless pr2 pr1)))

(define* lexordset (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords) coords)
  (lambda (l)
    (if (null? l)
        nil
        (let ((a (car l)) (x (cdr l)))
          (append2 (lexordset (filter (lambda (b) (lexless a b)) x))
                   (append2 (cons a nil)
                            (lexordset (filter (lambda (b) (lexgreater a b)) x))))))))

(define* collect (subr (maxeff (read @l) (alloc @l) spin (read @globals)) ((subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coord) coords) coords) coords)
  (lambda (f list)
    (letrec ((accumf (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords coords) coords)
               (lambda (sofar l) (if (null? l) sofar (accumf (revonto sofar (f (car l))) (cdr l))))))
      (accumf nil list))))

;; Finds coords which occur exactly 3 times in coordlist x.
(define* occurs3 (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords) coords)
  (lambda (x)
    (letrec ((diff (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords coords) coords)
               (lambda (x y) (filter (lambda (a) (not (member y a))) x)))
             (f (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords coords coords coords coords) coords)
               (lambda (xover x3 x2 x1 l)
                 (if (null? l)
                     (diff x3 xover)
                     (let ((a (car l)) (x (cdr l)))
                       (cond ((member xover a) (f xover x3 x2 x1 x))
                             ((member x3 a) (f (cons a xover) x3 x2 x1 x))
                             ((member x2 a) (f xover (cons a x3) x2 x1 x))
                             ((member x1 a) (f xover x3 (cons a x2) x1 x))
                             (else (f xover x3 x2 (cons a x1) x))))))))
      (f nil nil nil nil x))))

(define* alive (subr pure (coords) coords) (lambda (livecoords) livecoords))
(define* mkgen (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords) coords) (lambda (coordlist) (lexordset coordlist)))

(define* mk-nextgen-fn (subr (maxeff (read @l) (alloc @l) spin (read @globals)) ((subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coord) coords) coords) coords)
  (lambda (neighbours gen)
    (let* ((living (alive gen))
           (isalive (lambda ((a coord)) (member living a)))
           (liveneighbours (lambda ((a coord)) (length (filter isalive (neighbours a)))))
           (twoorthree (lambda ((n int)) (or (= n 2) (= n 3))))
           (survivors (filter (lambda (a) (twoorthree (liveneighbours a))) living))
           (newnbrlist (collect (lambda (a) (filter (lambda (b) (not (isalive b))) (neighbours a))) living))
           (newborn (occurs3 newnbrlist)))
      (mkgen (append2 survivors newborn)))))

(define* pt (subr (alloc @l) (int int) coord) (lambda (i j) (cons i j)))

(define* neighbours (subr (maxeff (read @l) (alloc @l)) (coord) coords)
  (lambda (c)
    (let ((i (car c)) (j (cdr c)))
      (list (pt (- i 1) (- j 1)) (pt (- i 1) j) (pt (- i 1) (+ j 1))
            (pt i (- j 1)) (pt i (+ j 1))
            (pt (+ i 1) (- j 1)) (pt (+ i 1) j) (pt (+ i 1) (+ j 1))))))

(define xstart int 0)
(define ystart int 0)

(define* markafter (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (int string) string)
  (lambda (n string) (string-append (string-append string (spaces n)) "0")))

(define* plotfrom (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (int int string coords) strings)
  (lambda (x y str l)
    (if (null? l)
        (cons str nil)
        (let ((x1 (car (car l))) (y1 (cdr (car l))) (more (cdr l)))
          (if (= x x1)
              ;; same line so extend str and continue from y1+1
              (plotfrom x (+ y1 1) (markafter (- y1 y) str) more)
              ;; flush current line and start a new line
              (cons str (plotfrom (+ x 1) ystart "" l)))))))

(define* good (subr (read @l) (coord) bool)
  (lambda (c) (and (>= (car c) xstart) (>= (cdr c) ystart))))

(define* plot (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords) strings)
  (lambda (coordlist) (plotfrom xstart ystart "" (filter good coordlist))))

(define* at (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords coord) coords)
  (lambda (coordlist p)
    (let ((x (car p)) (y (cdr p)))
      (map (lambda (c) (pt (+ (car c) x) (+ (cdr c) y))) coordlist))))

(define* rotate (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords) coords)
  (lambda (l) (map (lambda (c) (pt (cdr c) (- 0 (car c)))) l)))

;; Builds a literal list of coordinates from a list of ints, x y x y ...
(define* coords-of (subr (maxeff (read @l) (alloc @l) spin (read (globals pt))) ((listof int @l)) coords)
  (lambda (l) (if (null? l) nil (cons (pt (car l) (car (cdr l))) (coords-of (cdr (cdr l)))))))

(define glider coords (coords-of (list 0 0 0 2 1 1 1 2 2 1)))
(define bail coords (coords-of (list 0 0 0 1 1 0 1 1)))

(define* barberpole (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (int) coords)
  (lambda (n)
    (letrec ((f (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (int) coords)
               (lambda (i)
                 (if (= i n)
                     (list (pt (- (+ n n) 1) (+ n n)) (pt (+ n n) (+ n n)))
                     (cons (pt (+ i i) (+ (+ i i) 1)) (cons (pt (+ (+ i i) 2) (+ (+ i i) 1)) (f (+ i 1))))))))
      (the coords (cons (pt 0 0) (cons (pt 1 0) (f 0)))))))

(define genB coords
  (mkgen (append2 (at glider (pt 2 2))
                  (append2 (at bail (pt 2 12))
                           (at (rotate (barberpole 4)) (pt 5 20))))))

(define* nthgen (subr (maxeff (read @l) (alloc @l) spin (read @globals)) (coords int) coords)
  (lambda (g i) (if (= i 0) g (nthgen (mk-nextgen-fn neighbours g) (- i 1)))))

(define gun coords
  (mkgen (coords-of (list 2 20 3 19 3 21 4 18 4 22 4 23 4 32 5 7 5 8 5 18
                          5 22 5 23 5 29 5 30 5 31 5 32 5 36 6 7 6 8 6 18
                          6 22 6 23 6 28 6 29 6 30 6 31 6 36 7 19 7 21 7 28
                          7 31 7 40 7 41 8 20 8 28 8 29 8 30 8 31 8 40 8 41
                          9 29 9 30 9 31 9 32))))

(define* app (subr (maxeff (read @l) (alloc @l) spin (read @globals) (read @c) (write @c)) ((subr (maxeff (read @c) (write @c)) (string) unit) strings) unit)
  (lambda (f l) (if (null? l) #u (begin (f (car l)) (app f (cdr l))))))

(define* show (subr (maxeff (read @l) (alloc @l) spin (read @globals) (read @c) (write @c)) ((subr (maxeff (read @c) (write @c)) (string) unit) coords) unit)
  (lambda (pr g) (app (lambda (s) (begin (pr s) (pr "\n"))) (plot (alive g)))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define generations int 25000)
(define iterations int 1)

(define* doit (subr (maxeff (read @l) (alloc @l) spin (read @globals) (read @c) (write @c) (alloc @c)) (int) int)
  (lambda (size)
    (let ((printed (the (ref int @c) (new 0))))
      (letrec ((loop (subr (maxeff (read @l) (alloc @l) spin (read @globals) (read @c) (write @c)) (int) unit)
                 (lambda (n)
                   (if (= n 0)
                       #u
                       (begin
                         (set printed 0)
                         (show (lambda (s) (set printed (+ (get printed) (string-length s))))
                               (nthgen gun generations))
                         (loop (- n 1)))))))
        (begin (loop size) (get printed))))))
(doit iterations)
