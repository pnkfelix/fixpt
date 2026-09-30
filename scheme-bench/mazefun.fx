;;; MAZEFUN -- Constructs a maze in a purely functional way,
;;; written by Marc Feeley.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/mazefun.scm),
;;; ported to FX-26. Larceny's input: 10000 iterations of (make-maze 11 11).
;;; Answer: ((_ * _ _ _ _ _ _ _ _ _)
;;;          (_ * * * * * * * _ * *)
;;;          (_ _ _ * _ _ _ * _ _ _)
;;;          (_ * _ * _ * _ * _ * _)
;;;          (_ * _ _ _ * _ * _ * _)
;;;          (* * _ * * * * * _ * _)
;;;          (_ * _ _ _ _ _ _ _ * _)
;;;          (_ * _ * _ * * * * * *)
;;;          (_ _ _ * _ _ _ _ _ _ _)
;;;          (_ * * * * * * * _ * *)
;;;          (_ * _ _ _ _ _ _ _ _ _))
;;;
;;; A cell of the cave is `#f` (a wall) or a pair `(i . j)` naming its
;;; cavity; here a `(pairof int int @heap)`, whose `nil` stands for `#f`,
;;; so a test of a cell is `null?`, and `equal?` of two cells is
;;; `cell=?`, which compares the pairs' fields as `equal?` does. The
;;; higher-order procedures (`foldr`, `foldl`, `for`, `map`) and the list
;;; procedures used at more than one type (`list-read`, `list-write`,
;;; `list-remove-pos`) are polymorphic; `append` is `append2`, of two
;;; lists of positions, nested where the original gives four. `length`,
;;; `member` (as `cell-member`), `even?` and `odd?` are written out. The
;;; definitions are in the order FX-26 needs, each after what it calls.
;;; `make-maze` of even sizes, `'error` in the original, is `nil` here.
;;; Larceny checks the result with `equal?` against its input file; here
;;; the maze is the program's value, printed as Scheme prints it.

(define-type pos (pairof int int @heap))
(define-type cave (listof (listof pos @heap) @heap))

;; What the maze's procedures do: read and build lists, recurse, and call
;; each other.
(define-effect mz
  (maxeff (read @heap) (alloc @heap) spin
          (read (globals foldr foldl for concat append2 length list-read list-write
                         list-remove-pos cell=? cell-member duplicates? make-matrix
                         matrix-read matrix-write matrix-size matrix-map map even? odd?
                         initial-random next-random shuffle-aux shuffle
                         neighboring-cavities change-cavity-aux change-cavity pierce
                         try-to-pierce pierce-randomly cave-to-maze))))

(define foldr
  (poly ((a type) (b type) (e effect))
    (subr (maxeff e (read @heap) spin) ((subr e (a b) b) b (listof a @heap)) b))
  (plambda ((a type) (b type) (e effect))
    (lambda (f base lst)
      (letrec ((foldr-aux (subr (maxeff e (read @heap) spin) ((listof a @heap)) b)
                 (lambda (lst)
                   (if (null? lst)
                       base
                       (f (car lst) (foldr-aux (cdr lst)))))))
        (foldr-aux lst)))))

(define foldl
  (poly ((a type) (b type) (e effect))
    (subr (maxeff e (read @heap) spin) ((subr e (a b) a) a (listof b @heap)) a))
  (plambda ((a type) (b type) (e effect))
    (lambda (f base lst)
      (letrec ((foldl-aux (subr (maxeff e (read @heap) spin) (a (listof b @heap)) a)
                 (lambda (base lst)
                   (if (null? lst)
                       base
                       (foldl-aux (f base (car lst)) (cdr lst))))))
        (foldl-aux base lst)))))

(define for
  (poly ((a type) (e effect))
    (subr (maxeff e (alloc @heap) spin) (int int (subr e (int) a)) (listof a @heap)))
  (plambda ((a type) (e effect))
    (lambda (lo hi f)
      (letrec ((for-aux (subr (maxeff e (alloc @heap) spin) (int) (listof a @heap))
                 (lambda (lo)
                   (if (< lo hi)
                       (cons (f lo) (for-aux (+ lo 1)))
                       nil))))
        (for-aux lo)))))

(define map
  (poly ((a type) (b type) (e effect))
    (subr (maxeff e (read @heap) (alloc @heap) spin) ((subr e (a) b) (listof a @heap)) (listof b @heap)))
  (plambda ((a type) (b type) (e effect))
    (lambda (f lst)
      (letrec ((map-aux (subr (maxeff e (read @heap) (alloc @heap) spin) ((listof a @heap)) (listof b @heap))
                 (lambda (lst)
                   (if (null? lst)
                       nil
                       (cons (f (car lst)) (map-aux (cdr lst)))))))
        (map-aux lst)))))

(define* append2 (subr (maxeff (read @heap) (alloc @heap) spin) ((listof pos @heap) (listof pos @heap)) (listof pos @heap))
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append2 (cdr xs) ys)))))

(define* concat (subr mz ((listof (listof pos @heap) @heap)) (listof pos @heap))
  (lambda (lists)
    (foldr append2 nil lists)))

(define length
  (poly ((a type)) (subr (maxeff (read @heap) spin) ((listof a @heap)) int))
  (plambda ((a type))
    (lambda (l)
      (letrec ((loop (subr (maxeff (read @heap) spin) ((listof a @heap) int) int)
                 (lambda (l n) (if (null? l) n (loop (cdr l) (+ n 1))))))
        (loop l 0)))))

(define list-read
  (poly ((a type)) (subr (maxeff (read @heap) spin (read (globals list-read))) ((listof a @heap) int) a))
  (plambda ((a type))
    (lambda (lst i)
      (if (= i 0)
          (car lst)
          (list-read (cdr lst) (- i 1))))))

(define list-write
  (poly ((a type)) (subr (maxeff (read @heap) (alloc @heap) spin (read (globals list-write))) ((listof a @heap) int a) (listof a @heap)))
  (plambda ((a type))
    (lambda (lst i val)
      (if (= i 0)
          (cons val (cdr lst))
          (cons (car lst) (list-write (cdr lst) (- i 1) val))))))

(define list-remove-pos
  (poly ((a type)) (subr (maxeff (read @heap) (alloc @heap) spin (read (globals list-remove-pos))) ((listof a @heap) int) (listof a @heap)))
  (plambda ((a type))
    (lambda (lst i)
      (if (= i 0)
          (cdr lst)
          (cons (car lst) (list-remove-pos (cdr lst) (- i 1)))))))

;; `equal?` of two cells: both `#f`, or pairs of equal numbers.
(define* cell=? (subr (read @heap) (pos pos) bool)
  (lambda (x y)
    (if (null? x)
        (null? y)
        (and (not (null? y))
             (= (car x) (car y))
             (= (cdr x) (cdr y))))))

;; `member`, of cells: only whether the cell is there counts.
(define* cell-member (subr mz (pos (listof pos @heap)) bool)
  (lambda (x lst)
    (if (null? lst)
        #f
        (or (cell=? x (car lst))
            (cell-member x (cdr lst))))))

(define* duplicates? (subr mz ((listof pos @heap)) bool)
  (lambda (lst)
    (if (null? lst)
        #f
        (or (cell-member (car lst) (cdr lst))
            (duplicates? (cdr lst))))))

(define* make-matrix (subr mz (int int (subr mz (int int) pos)) cave)
  (lambda (n m init)
    (for 0 n (lambda (i) (for 0 m (lambda (j) (init i j)))))))

(define* matrix-read (subr mz (cave int int) pos)
  (lambda (mat i j)
    (list-read (list-read mat i) j)))

(define* matrix-write (subr mz (cave int int pos) cave)
  (lambda (mat i j val)
    (list-write mat i (list-write (list-read mat i) j val))))

(define* matrix-size (subr mz (cave) (pairof int int @heap))
  (lambda (mat)
    (cons (length mat) (length (car mat)))))

(define* matrix-map (subr mz ((subr mz (pos) symbol) cave) (listof (listof symbol @heap) @heap))
  (lambda (f mat)
    (map (lambda (lst) (map f lst)) mat)))

(define initial-random int 0)

(define* next-random (subr pure (int) int)
  (lambda (current-random)
    (modulo (+ (* current-random 3581) 12751) 131072)))

(define* shuffle-aux (subr mz ((listof pos @heap) int) (listof pos @heap))
  (lambda (lst current-random)
    (if (null? lst)
        nil
        (let ((new-random (next-random current-random)))
          (let ((i (modulo new-random (length lst))))
            (cons (list-read lst i)
                  (shuffle-aux (list-remove-pos lst i)
                               new-random)))))))

(define* shuffle (subr mz ((listof pos @heap)) (listof pos @heap))
  (lambda (lst)
    (shuffle-aux lst initial-random)))

(define* even? (subr pure (int) bool) (lambda (i) (= (modulo i 2) 0)))
(define* odd? (subr pure (int) bool) (lambda (i) (= (modulo i 2) 1)))

(define* cave-to-maze (subr mz (cave) (listof (listof symbol @heap) @heap))
  (lambda (cave)
    (matrix-map (lambda (x) (if (not (null? x)) '_ '*)) cave)))

(define* pierce (subr mz (pos cave) cave)
  (lambda (pos cave)
    (let ((i (car pos)) (j (cdr pos)))
      (matrix-write cave i j pos))))

(define* neighboring-cavities (subr mz (pos cave) (listof pos @heap))
  (lambda (pos cave)
    (let ((size (matrix-size cave)))
      (let ((n (car size)) (m (cdr size)))
        (let ((i (car pos)) (j (cdr pos)))
          (append2 (if (and (> i 0) (not (null? (matrix-read cave (- i 1) j))))
                       (cons (cons (- i 1) j) nil)
                       nil)
                   (append2 (if (and (< i (- n 1)) (not (null? (matrix-read cave (+ i 1) j))))
                                (cons (cons (+ i 1) j) nil)
                                nil)
                            (append2 (if (and (> j 0) (not (null? (matrix-read cave i (- j 1)))))
                                         (cons (cons i (- j 1)) nil)
                                         nil)
                                     (if (and (< j (- m 1)) (not (null? (matrix-read cave i (+ j 1)))))
                                         (cons (cons i (+ j 1)) nil)
                                         nil)))))))))

(define* change-cavity-aux (subr mz (cave pos pos pos) cave)
  (lambda (cave pos new-cavity-id old-cavity-id)
    (let ((i (car pos)) (j (cdr pos)))
      (let ((cavity-id (matrix-read cave i j)))
        (if (cell=? cavity-id old-cavity-id)
            (foldl (lambda (c nc)
                     (change-cavity-aux c nc new-cavity-id old-cavity-id))
                   (matrix-write cave i j new-cavity-id)
                   (neighboring-cavities pos cave))
            cave)))))

(define* change-cavity (subr mz (cave pos pos) cave)
  (lambda (cave pos new-cavity-id)
    (let ((i (car pos)) (j (cdr pos)))
      (change-cavity-aux cave pos new-cavity-id (matrix-read cave i j)))))

(define* try-to-pierce (subr mz (pos cave) cave)
  (lambda (pos cave)
    (let ((i (car pos)) (j (cdr pos)))
      (let ((ncs (neighboring-cavities pos cave)))
        (if (duplicates?
             (map (lambda (nc) (matrix-read cave (car nc) (cdr nc))) ncs))
            cave
            (pierce pos
                    (foldl (lambda (c nc) (change-cavity c nc pos))
                           cave
                           ncs)))))))

(define* pierce-randomly (subr mz ((listof pos @heap) cave) cave)
  (lambda (possible-holes cave)
    (if (null? possible-holes)
        cave
        (let ((hole (car possible-holes)))
          (pierce-randomly (cdr possible-holes)
                           (try-to-pierce hole cave))))))

(define* make-maze (subr mz (int int) (listof (listof symbol @heap) @heap))
  (lambda (n m) ; n and m must be odd
    (if (not (and (odd? n) (odd? m)))
        nil
        (let ((cave
               (make-matrix n m (lambda (i j)
                                  (if (and (even? i) (even? j))
                                      (cons i j)
                                      no-pair))))
              (possible-holes
               (concat
                (for 0 n (lambda (i)
                           (concat
                            (for 0 m (lambda (j)
                                       (if (if (even? i) (even? j) (not (even? j)))
                                           nil
                                           (cons (cons i j) nil))))))))))
          (cave-to-maze (pierce-randomly (shuffle possible-holes) cave))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 11)
(define input2 int 11)
(define iterations int 10000)

(define* run (subr (maxeff mz (read (globals make-maze input1 input2)))
                   (int (listof (listof symbol @heap) @heap)) (listof (listof symbol @heap) @heap))
  (lambda (i result) (if (= i 0) result (run (- i 1) (make-maze input1 input2)))))
(run iterations nil)
