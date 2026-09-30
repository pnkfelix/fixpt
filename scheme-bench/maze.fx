;;; MAZE -- Constructs a maze on a hexagonal grid, written by Olin Shivers.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/maze.scm),
;;; ported to FX-26. Larceny's input: 10000 iterations of (run 20 7).
;;; Answer: the list of characters of this picture, the maze printed
;;; (#\space #\space #\space #\_ … #\newline), trailing spaces not shown:
;;;
;;;    _   _   _
;;;  _/ \_/ \_/.\
;;; / \   \_ .  /.\
;;; \   \ /. _/.\ /
;;; / \_/. _/ \_ .\
;;; \ / \ /  _/ \_/
;;; /  _/.\ / \ / \
;;; \ / \ /  _/   /
;;; / \ /.\ /.\_/ \
;;; \_/ \ /. _ .\ /
;;; / \_ . _/ \   \
;;; \_  \_/  _/.\ /
;;; /  _/   / \ / \
;;; \_  \ / \_ .\_/
;;; / \_  \_  \_ .\
;;; \_  \_/  _/.\ /
;;; / \_  \ /.\  .\
;;; \ /.\_ .  /.\ /
;;; /    . _/.\ / \
;;; \ /.\_/.\_ .\ /
;;; / \_ .  /  _/ \
;;; \_  \_/.\_  \_/
;;; /  _/ \ / \_  \
;;; \_/  _/.\_  \_/
;;; / \ /  _ . _  \
;;; \ / \_/. _  \_/
;;; /  _  \   \_/ \
;;; \_/.\_ .\_/  _/
;;; / \  . _/   / \
;;; \ /.\_/ \_/.\ /
;;; / \_ . _/.    \
;;; \      .  /.\_/
;;; / \_/ \_/ \_ .\
;;; \_/   / \_/.  /
;;; /   /  _  \ / \
;;; \_/ \_/ \_/.\_/
;;; / \_/  _/ \_ .\
;;; \    _/.  /. _/
;;; / \ /.  / \_ .\
;;; \_/. _/.\_/.\ /
;;; /  _ .\_ . _ .\
;;; \_/ \ / \_/ \_/
;;;
;;; What the port changed, and why:
;;; - A cell's parent is a cell or #f. A cell here is a pair: its car the
;;;   record of its other fields (a bloblet), its cdr its parent, so that
;;;   `nil` is the cell that is not there, and a cell is a list of cells up
;;;   to the root. Larceny's cell is one six-slot vector (a tag and five
;;;   fields); this one is a pair and a four-field bloblet. Walls and hex
;;;   arrays are bloblets, the vectors' tag symbols left out. Cells, like
;;;   sets, are pairs at a writable region, so `eq?` of them is exact, as
;;;   Scheme's is of vectors and pairs.
;;; - `pick-entrances` starts entrance and exit at -1, where Larceny starts
;;;   them at #f; the first bottom cell always replaces them.
;;; - `dig-maze`'s continuation is given #u, where Larceny gives it #f; the
;;;   value is not used.
;;; - `harr` (which makes a hex array of unspecified elements) and
;;;   `harr-for-each`, never used, are left out, as are the wall setters.
;;; - Larceny's `run` is `run-maze` here, since `run` repeats it.
;;; - A definition sees only those before it, so `bit-test`,
;;;   `for-each-hex-child`, `dot/space`, `display-hexbottom` and `pmaze`
;;;   come earlier or later than in Larceny's file.

(define-effect rwa (maxeff (read @heap) (write @heap) (alloc @heap) spin))

;;; R6RS procedures needed by this benchmark.

(define bitwise-not (subr pure (int) int)
  (lambda (x) (- (- 0 x) 1)))

(define div (subr pure (int int) int)
  (lambda (x y)
    (cond ((>= x 0)
           (quotient x y))
          ((< y 0)
           ;; x < 0, y < 0
           (let* ((q (quotient x y))
                  (r (- x (* q y))))
             (if (= r 0) q (+ q 1))))
          (else
           ;; x < 0, y > 0
           (let* ((q (quotient x y))
                  (r (- x (* q y))))
             (if (= r 0) q (- q 1)))))))

(define* mod (subr pure (int int) int)
  (lambda (x y)
    (cond ((>= x 0)
           (remainder x y))
          ((< y 0)
           ;; x < 0, y < 0
           (let* ((q (quotient x y))
                  (r (- x (* q y))))
             (if (= r 0) 0 (- r y))))
          (else
           ;; x < 0, y > 0
           (let* ((q (quotient x y))
                  (r (- x (* q y))))
             (if (= r 0) 0 (+ r y)))))))

(define odd? (subr pure (int) bool)
  (lambda (x) (not (= (modulo x 2) 0))))

(define* bitwise-and (subr spin (int int) int)     ; two arguments are enough for this benchmark
  (lambda (x y)
    (cond ((= x 0) 0)
          ((= y 0) 0)
          ((= x -1) y)
          ((= y -1) x)
          (else
           (let ((z (bitwise-and (div x 2) (div y 2))))
             (if (and (odd? x) (odd? y))
                 (+ z (+ z 1))
                 (+ z z)))))))

;;; End of R6RS procedures.

;------------------------------------------------------------------------------
; Was file "rand.scm".

; Minimal Standard Random Number Generator
; Park & Miller, CACM 31(10), Oct 1988, 32 bit integer version.
; better constants, as proposed by Park.
; By Ozan Yigit

;;; Rehacked by Olin 4/1995.

(define-type rstate (pairof int bool @heap))

(define random-state (subr (alloc @heap) (int) rstate)
  (lambda (n) (cons n #f)))

(define* rand (subr (maxeff (read @heap) (write @heap)) (rstate) int)
  (lambda (state)
    (let ((seed (car state))
          (A 2813)                      ; 48271
          (M 8388607)                   ; 2147483647
          (Q 2787)                      ; 44488
          (R 2699))                     ; 3399
      (let* ((hi (div seed Q))
             (lo (mod seed Q))
             (test (- (* A lo) (* R hi)))
             (val (if (> test 0) test (+ test M))))
        (begin (set-car! state val)
               val)))))

(define* random-int (subr (maxeff (read @heap) (write @heap)) (int rstate) int)
  (lambda (n state) (mod (rand state) n)))

;------------------------------------------------------------------------------
; Was file "uf.scm".

;;; Tarjan's amortised union-find data structure.
;;; Copyright (c) 1995 by Olin Shivers.

;;; This data structure implements disjoint sets of elements.
;;; Four operations are supported. The implementation is extremely
;;; fast -- any sequence of N operations can be performed in time
;;; so close to linear it's laughable how close it is. See your
;;; intro data structures book for more. The operations are:
;;;
;;; - (base-set nelts) -> set
;;;   Returns a new set, of size NELTS.
;;;
;;; - (set-size s) -> integer
;;;   Returns the number of elements in set S.
;;;
;;; - (union! set1 set2)
;;;   Unions the two sets -- SET1 and SET2 are now considered the same set
;;;   by SET-EQUAL?.
;;;
;;; - (set-equal? set1 set2)
;;;   Returns true <==> the two sets are the same.

;;; Representation: a set is a cons cell. Every set has a "representative"
;;; cons cell, reached by chasing cdr links until we find the cons with
;;; cdr = (). Set equality is determined by comparing representatives using
;;; EQ?. A representative's car contains the number of elements in the set.

;;; The speed of the algorithm comes because when we chase links to find
;;; representatives, we collapse links by changing all the cells in the path
;;; we followed to point directly to the representative, so that next time
;;; we walk the cdr-chain, we'll go directly to the representative in one hop.

(define-type uset (listof int @heap))

(define base-set (subr (alloc @heap) (int) uset)
  (lambda (nelts) (cons nelts nil)))

;;; Sets are chained together through cdr links. Last guy in the chain
;;; is the root of the set.

(define* get-set-root (subr (maxeff (read @heap) (write @heap) spin) (uset) uset)
  (lambda (s)
    (letrec ((lp (subr (maxeff (read @heap) spin) (uset) uset)      ; Find the last pair
               (lambda (r)                                            ; in the list. That's
                 (let ((next (cdr r)))                                ; the root r.
                   (if (not (null? next)) (lp next) r))))
             (zip (subr (maxeff (read @heap) (write @heap) spin) (uset uset) unit)
               (lambda (r x)                    ; Now zip down the list again,
                 (let ((next (cdr x)))          ; changing everyone's cdr to r.
                   (if (not (eq? r next))
                       (begin (set-cdr! x r)
                              (zip r next))
                       #u)))))
      (let ((r (lp s)))
        (begin (if (not (eq? r s)) (zip r s) #u)
               r)))))                   ; Then return r.

(define* set-equal? (subr (maxeff (read @heap) (write @heap) spin) (uset uset) bool)
  (lambda (s1 s2) (eq? (get-set-root s1) (get-set-root s2))))

(define* set-size (subr (maxeff (read @heap) (write @heap) spin) (uset) int)
  (lambda (s) (car (get-set-root s))))

(define* union! (subr (maxeff (read @heap) (write @heap) spin) (uset uset) unit)
  (lambda (s1 s2)
    (let* ((r1 (get-set-root s1))
           (r2 (get-set-root s2))
           (n1 (set-size r1))
           (n2 (set-size r2))
           (n  (+ n1 n2)))
      (if (> n1 n2)
          (begin (set-cdr! r2 r1)
                 (set-car! r1 n))
          (begin (set-cdr! r1 r2)
                 (set-car! r2 n))))))

;------------------------------------------------------------------------------
; Was file "maze.scm".

;;; Building mazes with union/find disjoint sets.
;;; Copyright (c) 1995 by Olin Shivers.

;;; This is the algorithmic core of the maze constructor.
;;; External dependencies:
;;; - RANDOM-INT
;;; - Union/find code
;;; - bitwise logical functions

; (define-record wall
;   owner         ; Cell that owns this wall.
;   neighbor      ; The other cell bordering this wall.
;   bit)          ; Integer -- a bit identifying this wall in OWNER's cell.

; (define-record cell
;   reachable     ; Union/find set -- all reachable cells.
;   id            ; Identifying info (e.g., the coords of the cell).
;   (walls -1)    ; A bitset telling which walls are still standing.
;   (parent #f)   ; For DFS spanning tree construction.
;   (mark #f))    ; For marking the solution path.

;; A cell's fields but its parent: reachable, id, walls, mark.
(define-type cfields (bloblet (fields uset (pairof int int @heap) int bool) @heap))
;; A cell, its parent the cdr; nil is no cell (Larceny's #f).
(define-type cell (pairof cfields cell @heap))
(define-type wall (bloblet (fields cell cell int) @heap))

(define make-wall (subr (alloc @heap) (cell cell int) wall)
  (lambda (owner neighbor bit) (the wall (make-bloblet 0 owner neighbor bit))))

(define wall:owner (subr (read @heap) (wall) cell) (lambda (o) (bloblet-ref o 0)))
(define wall:neighbor (subr (read @heap) (wall) cell) (lambda (o) (bloblet-ref o 1)))
(define wall:bit (subr (read @heap) (wall) int) (lambda (o) (bloblet-ref o 2)))

(define make-cell (subr (alloc @heap) (uset (pairof int int @heap)) cell)
  (lambda (reachable id)
    (cons (the cfields (make-bloblet 0 reachable id -1 #f)) nil)))

(define cell:reachable (subr (read @heap) (cell) uset) (lambda (o) (bloblet-ref (car o) 0)))
(define cell:id (subr (read @heap) (cell) (pairof int int @heap)) (lambda (o) (bloblet-ref (car o) 1)))
(define cell:walls (subr (read @heap) (cell) int) (lambda (o) (bloblet-ref (car o) 2)))
(define set-cell:walls (subr (maxeff (read @heap) (write @heap)) (cell int) unit) (lambda (o v) (bloblet-set! (car o) 2 v)))
(define cell:parent (subr (read @heap) (cell) cell) (lambda (o) (cdr o)))
(define set-cell:parent (subr (write @heap) (cell cell) unit) (lambda (o v) (set-cdr! o v)))
(define cell:mark (subr (read @heap) (cell) bool) (lambda (o) (bloblet-ref (car o) 3)))
(define set-cell:mark (subr (maxeff (read @heap) (write @heap)) (cell bool) unit) (lambda (o v) (bloblet-set! (car o) 3 v)))

;;; Iterates in reverse order.

(define vector-for-each-rev
  (poly ((e effect)) (subr (maxeff e (read @heap) spin) ((subr e (wall) unit) (arrayof wall @heap)) unit))
  (plambda ((e effect))
    (lambda (proc v)
      (letrec ((lp (subr (maxeff e (read @heap) spin) (int) unit)
                 (lambda (i)
                   (if (>= i 0)
                       (begin (proc (array-ref v i))
                              (lp (- i 1)))
                       #u))))
        (lp (- (array-length v) 1))))))

;;; Randomly permute a vector.

(define* permute-vec! (subr (maxeff (read @heap) (write @heap) spin) ((arrayof wall @heap) rstate) (arrayof wall @heap))
  (lambda (v random-state)
    (letrec ((lp (subr (maxeff (read @heap) (write @heap) spin (read (globals random-int rand div mod))) (int) unit)
               (lambda (i)
                 (if (> i 1)
                     (let ((elt-i (array-ref v i))
                           (j (random-int i random-state)))     ; j in [0,i)
                       (begin (array-set! v i (array-ref v j))
                              (array-set! v j elt-i)
                              (lp (- i 1))))
                     #u))))
      (begin (lp (- (array-length v) 1))
             v))))

;;; This is the core of the algorithm.

(define-effect dig (maxeff (read @heap) (write @heap) spin (goto @k)
                           (read (globals wall:owner wall:neighbor wall:bit cell:reachable cell:walls set-cell:walls
                                          set-equal? get-set-root union! set-size bitwise-not bitwise-and div odd?))))

(define* dig-maze (subr (maxeff (read @heap) (write @heap) spin) ((arrayof wall @heap) int) unit)
  (lambda (walls ncells)
    ((proj (proj (proj cwcc @k) unit) (maxeff dig (read (globals vector-for-each-rev))))
     (lambda ((quit (subr (goto @k) (unit) void)))
       ((proj vector-for-each-rev dig)
        (lambda ((wall wall))                   ; For each wall,
          (let* ((c1   (wall:owner wall))       ; find the cells on
                 (set1 (cell:reachable c1))

                 (c2   (wall:neighbor wall))    ; each side of the wall
                 (set2 (cell:reachable c2)))

            ;; If there is no path from c1 to c2, knock down the
            ;; wall and union the two sets of reachable cells.
            ;; If the new set of reachable cells is the whole set
            ;; of cells, quit.
            (if (not (set-equal? set1 set2))
                (let ((walls (cell:walls c1))
                      (wall-mask (bitwise-not (wall:bit wall))))
                  (begin (union! set1 set2)
                         (set-cell:walls c1 (bitwise-and walls wall-mask))
                         (if (= (set-size set1) ncells) (quit #u) #u)))
                #u)))
        walls)))))


;;; Some simple DFS routines useful for determining path length
;;; through the maze.

;;; Build a DFS tree from ROOT.
;;; (DO-CHILDREN proc maze node) applies PROC to each of NODE's children.
;;; We assume there are no loops in the maze; if this is incorrect, the
;;; algorithm will diverge.

(define-effect hexes (maxeff (read @heap) (write @heap) spin
                             (read (globals cell:walls cell:id cell:mark set-cell:mark cell:parent set-cell:parent
                                            harr:nrows harr:ncols harr:elts href bit-test bitwise-and
                                            south-west south south-east div mod odd?))))

(define-type harr (bloblet (fields int int (arrayof cell @heap)) @heap))

(define* dfs-maze (subr hexes (harr cell (subr hexes ((subr hexes (cell) unit) harr cell) unit)) unit)
  (lambda (maze root do-children)
    (letrec ((search (subr hexes (cell cell) unit)
               (lambda (node parent)
                 (begin (set-cell:parent node parent)
                        (do-children (lambda ((child cell))
                                       (if (not (eq? child parent))
                                           (search child node)
                                           #u))
                                     maze node)))))
      (search root (the cell nil)))))

;;; Move the root to NEW-ROOT.

(define* reroot-maze (subr (maxeff (read @heap) (write @heap) spin) (cell) unit)
  (lambda (new-root)
    (letrec ((lp (subr (maxeff (read @heap) (write @heap) spin (read (globals cell:parent set-cell:parent))) (cell cell) unit)
               (lambda (node new-parent)
                 (let ((old-parent (cell:parent node)))
                   (begin (set-cell:parent node new-parent)
                          (if (not (null? old-parent)) (lp old-parent node) #u))))))
      (lp new-root (the cell nil)))))

;;; How far from CELL to the root?

(define* path-length (subr (maxeff (read @heap) spin) (cell) int)
  (lambda (cell)
    (letrec ((do-loop (subr (maxeff (read @heap) spin (read (globals cell:parent))) (int cell) int)
               (lambda (len node)
                 (if (null? node) len (do-loop (+ len 1) (cell:parent node))))))
      (do-loop 0 (cell:parent cell)))))

;;; Mark the nodes from NODE back to root. Used to mark the winning path.

(define* mark-path (subr (maxeff (read @heap) (write @heap) spin) (cell) unit)
  (lambda (node)
    (letrec ((lp (subr (maxeff (read @heap) (write @heap) spin (read (globals set-cell:mark cell:parent))) (cell) unit)
               (lambda (node)
                 (begin (set-cell:mark node #t)
                        (let ((p (cell:parent node)))
                          (if (not (null? p)) (lp p) #u))))))
      (lp node))))

;------------------------------------------------------------------------------
; Was file "harr.scm".

;;; Hex arrays
;;; Copyright (c) 1995 by Olin Shivers.

;;; External dependencies:
;;; - define-record

;;;        ___       ___       ___
;;;       /   \     /   \     /   \
;;;   ___/  A  \___/  A  \___/  A  \___
;;;  /   \     /   \     /   \     /   \
;;; /  A  \___/  A  \___/  A  \___/  A  \
;;; \     /   \     /   \     /   \     /
;;;  \___/     \___/     \___/     \___/
;;;  /   \     /   \     /   \     /   \
;;; /     \___/     \___/     \___/     \
;;; \     /   \     /   \     /   \     /
;;;  \___/     \___/     \___/     \___/
;;;  /   \     /   \     /   \     /   \
;;; /     \___/     \___/     \___/     \
;;; \     /   \     /   \     /   \     /
;;;  \___/     \___/     \___/     \___/

;;; Hex arrays are indexed by the (x,y) coord of the center of the hexagonal
;;; element. Hexes are three wide and two high; e.g., to get from the center
;;; of an elt to its {NW, N, NE} neighbors, add {(-3,1), (0,2), (3,1)}
;;; respectively.
;;;
;;; Hex arrays are represented with a matrix, essentially made by shoving the
;;; odd columns down a half-cell so things line up. The mapping is as follows:
;;;     Center coord      row/column
;;;     ------------      ----------
;;;     (x,  y)        -> (y/2, x/3)
;;;     (3c, 2r + c&1) <- (r,   c)


; (define-record harr
;   nrows
;   ncols
;   elts)

(define make-harr (subr (alloc @heap) (int int (arrayof cell @heap)) harr)
  (lambda (nrows ncols elts) (the harr (make-bloblet 0 nrows ncols elts))))

(define harr:nrows (subr (read @heap) (harr) int) (lambda (o) (bloblet-ref o 0)))
(define harr:ncols (subr (read @heap) (harr) int) (lambda (o) (bloblet-ref o 1)))
(define harr:elts (subr (read @heap) (harr) (arrayof cell @heap)) (lambda (o) (bloblet-ref o 2)))

(define* href (subr (read @heap) (harr int int) cell)
  (lambda (ha x y)
    (let ((r (div y 2))
          (c (div x 3)))
      (array-ref (harr:elts ha)
                 (+ (* (harr:ncols ha) r) c)))))

(define* href/rc (subr (read @heap) (harr int int) cell)
  (lambda (ha r c)
    (array-ref (harr:elts ha)
               (+ (* (harr:ncols ha) r) c))))

;;; Create a nrows x ncols hex array. The elt centered on coord (x, y)
;;; is the value returned by (PROC x y).

(define-effect tabulate (maxeff (read @heap) (write @heap) (alloc @heap) spin (read (globals bitwise-and make-cell base-set div odd?))))

(define* harr-tabulate (subr tabulate (int int (subr tabulate (int int) cell)) harr)
  (lambda (nrows ncols proc)
    (let ((v (the (arrayof cell @heap) (make-array (* nrows ncols) nil))))
      (letrec ((rows (subr tabulate (int) unit)
                 (lambda (r)
                   (if (< r 0)
                       #u
                       (begin (cols r 0 (* r ncols))
                              (rows (- r 1))))))
               (cols (subr tabulate (int int int) unit)
                 (lambda (r c i)
                   (if (= c ncols)
                       #u
                       (begin (array-set! v i (proc (* 3 c) (+ (* 2 r) (bitwise-and c 1))))
                              (cols r (+ c 1) (+ i 1)))))))
        (begin (rows (- nrows 1))
               (make-harr nrows ncols v))))))

;------------------------------------------------------------------------------
; Was file "hex.scm".

;;; Hexagonal hackery for maze generation.
;;; Copyright (c) 1995 by Olin Shivers.

;;; External dependencies:
;;; - cell and wall records
;;; - Functional Postscript for HEXES->PATH
;;; - logical functions for bit hacking
;;; - hex array code.

;;; To have the maze span (0,0) to (1,1):
;;; (scale (/ (+ 1 (* 3 ncols))) (/ (+ 1 (* 2 nrows)))
;;;        (translate (point 2 1) maze))

;;; Every elt of the hex array manages his SW, S, and SE wall.
;;; Terminology: - An even column is one whose column index is even. That
;;;                means the first, third, ... columns (indices 0, 2, ...).
;;;              - An odd column is one whose column index is odd. That
;;;                means the second, fourth... columns (indices 1, 3, ...).
;;;              The even/odd flip-flop is confusing; be careful to keep it
;;;              straight. The *even* columns are the low ones. The *odd*
;;;              columns are the high ones.
;;;    _   _
;;;  _/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/
;;;  0 1 2 3

(define south-west int 1)
(define south      int 2)
(define south-east int 4)

(define* gen-maze-array (subr tabulate (int int) harr)
  (lambda (r c)
    (harr-tabulate r c (lambda ((x int) (y int)) (make-cell (base-set 1) (cons x y))))))

(define-effect walling (maxeff (read @heap) (write @heap) (alloc @heap) spin
                               (read (globals href make-wall bitwise-and div odd? harr:elts harr:ncols south-west south south-east))))

;;; This could be made more efficient.
(define* make-wall-vec (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (harr) (arrayof wall @heap))
  (lambda (harr)
    (let* ((nrows (harr:nrows harr))
           (ncols (harr:ncols harr))
           (xmax (* 3 (- ncols 1)))

           ;; Accumulate walls.
           (walls (the (ref (listof wall @heap) @heap) (new nil)))
           (add-wall (lambda ((o cell) (n cell) (b int)) ; owner neighbor bit
                       (set walls (cons (make-wall o n b) (get walls))))))

      ;; Do everything but the bottom row.
      (letrec ((xs (subr walling (int) unit)
                 (lambda (x)
                   (if (< x 0)
                       #u
                       (begin (ys x (+ (* (- nrows 1) 2) (bitwise-and x 1)))
                              (xs (- x 3))))))
               (ys (subr walling (int int) unit)
                 (lambda (x y)
                   (if (<= y 1)         ; Don't do bottom row.
                       #u
                       (let ((hex (href harr x y)))
                         (begin (if (not (= x 0))
                                    (add-wall hex (href harr (- x 3) (- y 1)) south-west)
                                    #u)
                                (add-wall hex (href harr x (- y 2)) south)
                                (if (< x xmax)
                                    (add-wall hex (href harr (+ x 3) (- y 1)) south-east)
                                    #u)
                                (ys x (- y 2)))))))
               ;; Do the rest of the bottom row's odd cols.
               (odds (subr walling (int) unit)
                 (lambda (x)
                   (if (< x 3)          ; 3 is X coord of leftmost odd column.
                       #u
                       (begin (add-wall (href harr x 1) (href harr (- x 3) 0) south-west)
                              (add-wall (href harr x 1) (href harr (+ x 3) 0) south-east)
                              (odds (- x 6)))))))
        (begin
          (xs (* (- ncols 1) 3))

          ;; Do the SE and SW walls of the odd columns on the bottom row.
          ;; If the rightmost bottom hex lies in an odd column, however,
          ;; don't add it's SE wall -- it's a corner hex, and has no SE neighbor.
          (if (> ncols 1)
              (let ((rmoc-x (+ 3 (* 6 (div (- ncols 2) 2)))))
                ;; Do rightmost odd col.
                (let ((rmoc-hex (href harr rmoc-x 1)))
                  (begin (if (< rmoc-x xmax)  ; Not  a corner -- do E wall.
                             (add-wall rmoc-hex (href harr xmax 0) south-east)
                             #u)
                         (add-wall rmoc-hex (href harr (- rmoc-x 3) 0) south-west)
                         (odds (- rmoc-x 6)))))
              #u)

          (list->array (get walls)))))))

;;; A Scheme vector of ints, as `vector` makes it.
(define vector2 (subr (maxeff (alloc @heap) (write @heap)) (int int) (arrayof int @heap))
  (lambda (a b)
    (let ((v (the (arrayof int @heap) (make-array 2 a))))
      (begin (array-set! v 1 b) v))))
(define vector3 (subr (maxeff (alloc @heap) (write @heap)) (int int int) (arrayof int @heap))
  (lambda (a b c)
    (let ((v (the (arrayof int @heap) (make-array 3 a))))
      (begin (array-set! v 1 b) (array-set! v 2 c) v))))

(define* bit-test (subr spin (int int) bool)
  (lambda (j bit) (not (= 0 (bitwise-and j bit)))))

;;; Apply PROC to each node reachable from CELL.
(define* for-each-hex-child (subr hexes ((subr hexes (cell) unit) harr cell) unit)
  (lambda (proc harr cell)
    (let* ((walls (cell:walls cell))
           (id (cell:id cell))
           (x (car id))
           (y (cdr id))
           (nr (harr:nrows harr))
           (nc (harr:ncols harr))
           (maxy (* 2 (- nr 1)))
           (maxx (* 3 (- nc 1))))
      (begin
        (if (not (bit-test walls south-west)) (proc (href harr (- x 3) (- y 1))) #u)
        (if (not (bit-test walls south))      (proc (href harr x       (- y 2))) #u)
        (if (not (bit-test walls south-east)) (proc (href harr (+ x 3) (- y 1))) #u)

        ;; NW neighbor, if there is one (we may be in col 1, or top row/odd col)
        (if (and (> x 0)                ; Not in first column.
                 (or (<= y maxy)        ; Not on top row or
                     (= 0 (mod x 6))))  ; not in an odd column.
            (let ((nw (href harr (- x 3) (+ y 1))))
              (if (not (bit-test (cell:walls nw) south-east)) (proc nw) #u))
            #u)

        ;; N neighbor, if there is one (we may be on top row).
        (if (< y maxy)                  ; Not on top row
            (let ((n (href harr x (+ y 2))))
              (if (not (bit-test (cell:walls n) south)) (proc n) #u))
            #u)

        ;; NE neighbor, if there is one (we may be in last col, or top row/odd col)
        (if (and (< x maxx)             ; Not in last column.
                 (or (<= y maxy)        ; Not on top row or
                     (= 0 (mod x 6))))  ; not in an odd column.
            (let ((ne (href harr (+ x 3) (+ y 1))))
              (if (not (bit-test (cell:walls ne) south-west)) (proc ne) #u))
            #u)))))

;;; Find the cell ctop from the top row, and the cell cbot from the bottom
;;; row such that cbot is furthest from ctop.
;;; Return [ctop-x, ctop-y, cbot-x, cbot-y].

(define-effect entrances (maxeff (read @heap) (write @heap) (alloc @heap) spin
                                 (read (globals href/rc harr:elts harr:ncols reroot-maze path-length vector2 vector3
                                                cell:parent set-cell:parent))))

(define* pick-entrances (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (harr) (arrayof int @heap))
  (lambda (harr)
    (begin
      (dfs-maze harr (href/rc harr 0 0) for-each-hex-child)
      (let ((nrows (harr:nrows harr))
            (ncols (harr:ncols harr)))
        (letrec ((tp-lp (subr entrances (int int int int) (arrayof int @heap))
                   (lambda (max-len entrance exit tcol)
                     (if (< tcol 0)
                         (vector2 entrance exit)
                         (let ((top-cell (href/rc harr (- nrows 1) tcol)))
                           (begin
                             (reroot-maze top-cell)
                             (let ((result (bt-lp max-len entrance exit (- ncols 1) tcol)))
                               (let ((max-len (array-ref result 0))
                                     (entrance (array-ref result 1))
                                     (exit (array-ref result 2)))
                                 (tp-lp max-len entrance exit (- tcol 1)))))))))
                 (bt-lp (subr entrances (int int int int int) (arrayof int @heap))
                   (lambda (max-len entrance exit bcol tcol)
                     (if (< bcol 0)
                         (vector3 max-len entrance exit)
                         (let ((this-len (path-length (href/rc harr 0 bcol))))
                           (if (> this-len max-len)
                               (bt-lp this-len tcol bcol (- bcol 1) tcol)
                               (bt-lp max-len entrance exit (- bcol 1) tcol)))))))
          (tp-lp -1 -1 -1 (- ncols 1)))))))

;;; The top-level
(define-type maze (productof (cells harr) (entrance int) (exit int)))

(define* make-maze (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) maze)
  (lambda (nrows ncols)
    (let* ((cells (gen-maze-array nrows ncols))
           (walls (permute-vec! (make-wall-vec cells) (random-state 20))))
      (begin
        (dig-maze walls (* nrows ncols))
        (let ((result (pick-entrances cells)))
          (let ((entrance (array-ref result 0))
                (exit (array-ref result 1)))
            (let* ((exit-cell (href/rc cells 0 exit))
                   (walls (cell:walls exit-cell)))
              (begin
                (reroot-maze (href/rc cells (- nrows 1) entrance))
                (mark-path exit-cell)
                (set-cell:walls exit-cell (bitwise-and walls (bitwise-not south)))
                (product (cells cells) (entrance entrance) (exit exit))))))))))

;------------------------------------------------------------------------------
; Was file "hexprint.scm".

;;; Print out a hex array with characters.
;;; Copyright (c) 1995 by Olin Shivers.

;;; External dependencies:
;;; - hex array code
;;; - hex cell code

;;;    _   _
;;;  _/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/

;;; Top part of top row looks like this:
;;;    _   _  _   _
;;;  _/ \_/ \/ \_/ \
;;; /

;; the list of all characters written out, in reverse order.
(define output (ref (listof char @heap) @heap) (new (the (listof char @heap) nil)))

(define* write-ch (subr (maxeff (read @heap) (write @heap) (alloc @heap)) (char) unit)
  (lambda (c) (set output (cons c (get output)))))

;;; Return a . if harr[r,c] is marked, otherwise a space.
;;; We use the dot to mark the solution path.
(define* dot/space (subr (read @heap) (harr int int) char)
  (lambda (harr r c)
    (if (and (>= r 0) (cell:mark (href/rc harr r c))) #\. #\space)))

;;; Print a \_/ hex bottom.
(define* display-hexbottom (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) unit)
  (lambda (hexwalls)
    (begin (write-ch (if (bit-test hexwalls south-west) #\\ #\space))
           (write-ch (if (bit-test hexwalls south     ) #\_ #\space))
           (write-ch (if (bit-test hexwalls south-east) #\/ #\space)))))

(define-effect printing (maxeff (read @heap) (write @heap) (alloc @heap) spin
                                (read (globals write-ch output dot/space display-hexbottom href/rc harr:elts harr:ncols
                                               cell:mark cell:walls bit-test bitwise-and south-west south south-east div odd?))))

(define* print-hexmaze (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (harr int) unit)
  (lambda (harr entrance)
    (let* ((nrows  (harr:nrows harr))
           (ncols  (harr:ncols harr))
           (ncols2 (* 2 (div ncols 2))))
      (letrec (;; Print out the flat tops for the top row's odd cols.
               (tops (subr printing (int) unit)
                 (lambda (c)
                   (if (>= c ncols)
                       #u
                       (begin (write-ch #\space)
                              (write-ch #\space)
                              (write-ch #\space)
                              (write-ch (if (= c entrance) #\space #\_))
                              (tops (+ c 2))))))
               ;; Print out the slanted tops for the top row's odd cols
               ;; and the flat tops for the top row's even cols.
               (slants (subr printing (int) unit)
                 (lambda (c)
                   (if (>= c ncols2)
                       #u
                       (begin (write-ch (if (= c entrance) #\space #\_))
                              (write-ch #\/)
                              (write-ch (dot/space harr (- nrows 1) (+ c 1)))
                              (write-ch #\\)
                              (slants (+ c 2))))))
               (rows (subr printing (int) unit)
                 (lambda (r)
                   (if (< r 0)
                       #u
                       (begin
                         ;; Do the bottoms for row r's odd cols.
                         (write-ch #\/)
                         (odd-bottoms r 1)
                         (if (odd? ncols)
                             (begin (write-ch (dot/space harr r (- ncols 1)))
                                    (write-ch #\\))
                             #u)
                         (write-ch #\newline)

                         ;; Do the bottoms for row r's even cols.
                         (even-bottoms r 0)
                         (cond ((odd? ncols)
                                (display-hexbottom (cell:walls (href/rc harr r (- ncols 1)))))
                               ((not (= 0 r)) (write-ch #\\))
                               (else #u))
                         (write-ch #\newline)
                         (rows (- r 1))))))
               (odd-bottoms (subr printing (int int) unit)
                 (lambda (r c)
                   (if (>= c ncols2)
                       #u
                       (begin
                         ;; The dot/space for the even col just behind c.
                         (write-ch (dot/space harr r (- c 1)))
                         (display-hexbottom (cell:walls (href/rc harr r c)))
                         (odd-bottoms r (+ c 2))))))
               (even-bottoms (subr printing (int int) unit)
                 (lambda (r c)
                   (if (>= c ncols2)
                       #u
                       (begin
                         (display-hexbottom (cell:walls (href/rc harr r c)))
                         ;; The dot/space is for the odd col just after c, on row below.
                         (write-ch (dot/space harr (- r 1) (+ c 1)))
                         (even-bottoms r (+ c 2)))))))
        (begin
          (tops 1)
          (write-ch #\newline)
          (write-ch #\space)
          (slants 0)
          (if (odd? ncols)
              (write-ch (if (= entrance (- ncols 1)) #\space #\_))
              #u)
          (write-ch #\newline)
          (rows (- nrows 1)))))))

;;;    _   _
;;;  _/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \_/
;;; / \_/ \_/
;;; \_/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \
;;; / \_/ \_/
;;; \_/ \_/ \_/

;------------------------------------------------------------------------------

(define* pmaze (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) unit)
  (lambda (nrows ncols)
    (let ((result (make-maze nrows ncols)))
      (let ((cells (extract result cells))
            (entrance (extract result entrance))
            (exit (extract result exit)))
        (print-hexmaze cells entrance)))))

(define* run-maze (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) (listof char @heap))
  (lambda (nrows ncols)
    (begin (set output nil)
           (pmaze nrows ncols)
           (the (listof char @heap) (reverse (get output))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 20)
(define input2 int 7)
(define iterations int 10000)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int (listof char @heap)) (listof char @heap))
  (lambda (i result) (if (= i 0) result (run (- i 1) (run-maze input1 input2)))))
(run iterations (the (listof char @heap) nil))
