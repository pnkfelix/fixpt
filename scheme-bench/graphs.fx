;;; GRAPHS -- Obtained from Andrew Wright.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/graphs.scm),
;;; ported to FX-26. Larceny's input: 3 iterations of (length (run 7)).
;;; Answer: 213829.
;;;
;;; Changes from the original:
;;; - Vectors are arrays: the connection matrix `(arrayof (arrayof bool))`,
;;;   the permutation and out-degree vectors `(arrayof int)`, the edge lists
;;;   `(arrayof (listof int))`.
;;; - The generic helpers are given the one type they are used at here
;;;   (`fold` over lists of vertices, `there-exists?` over reachability
;;;   vectors, the fold states `bool`, `int` and lists of graphs), except
;;;   `proc->vector`, used at three types, which is polymorphic. Helpers of
;;;   util.ss the benchmark never calls (`vector-fold`, `gnatural-fold`,
;;;   `natural-there-exists?`) are left out.
;;; - `proc->vector`'s `(zero? size)` case, which returns `(vector)`, is left
;;;   out: an empty array needs an element to make it with, and every size
;;;   here is at least 1.
;;; - `case` on 'less / 'equal / 'more is a `cond` over `symbol=?`; the
;;;   unreachable `(error #f "???")` arms are dropped, the last symbol taking
;;;   the `else`.
;;; - `eq?` of two booleans is `bool=?`; `for-each` over an edge list is a
;;;   loop; `(length …)` of the result is `list-length`, since `length` takes
;;;   only finite (frozen) lists.
;;; - The benchmark's `run` is `run-graphs`; `run` is the driver below.
;;; - `cmp-next-vertex` and `make-reach?` come before their callers, since a
;;;   definition sees only those before it.
;;; - Every procedure that is passed around or kept in a closure has the one
;;;   latent effect `graphs-eff`, which names the globals those closures read.

(define-type ints (listof int @heap))
(define-type bvec (arrayof bool @heap))
(define-type gmat (arrayof bvec @heap))
(define-type perm (arrayof int @heap))
(define-type graph (arrayof ints @heap))
(define-type glist (listof graph @heap))

(define-effect graphs-eff
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals bool=? fold proc->vector giota gnatural-for-each natural-for-all? there-exists?
                         fold-over-perm-tree make-minimal? cmp-next-vertex make-reach?))))

(define-type accross (subr graphs-eff (bool) bool))
(define-type deeper (subr graphs-eff (int bool) bool))
(define-type bfolder (subr graphs-eff (int int bool deeper accross) bool))
(define-type tfolder (subr graphs-eff (int bool accross) bool))
(define-type mfolder (subr graphs-eff (perm bool accross) bool))
(define-type minimal (subr graphs-eff (int gmat mfolder bool) bool))
(define-type rdg-folder (subr (alloc @heap) (graph glist) glist))

 ;;; ==== util.ss ====

(define bool=? (subr pure (bool bool) bool) (lambda (a b) (if a b (not b))))

; Fold over list elements, associating to the left.
(define* fold (subr graphs-eff (ints (subr (alloc @heap) (int ints) ints) ints) ints)
  (lambda (lst folder state)
    (if (null? lst)
        state
        (fold (cdr lst) folder (folder (car lst) state)))))

; Given the size of a vector and a procedure which
; sends indicies to desired vector elements, create
; and return the vector.
(define proc->vector
  (poly ((t type)) (subr graphs-eff (int (subr graphs-eff (int) t)) (arrayof t @heap)))
  (plambda ((t type))
    (lambda (size f)
      (let ((x (the (arrayof t @heap) (make-array size (f 0)))))
        (letrec ((loop (subr graphs-eff (int) unit)
                   (lambda (i)
                     (if (< i size)
                         (begin (array-set! x i (f i))
                                (loop (+ i 1)))
                         #u))))
          (begin (loop 1) x))))))

; Given limit, return the list 0, 1, ..., limit-1.
(define giota (subr (maxeff (alloc @heap) spin) (int) ints)
  (lambda (limit)
    (letrec ((_-*- (subr (maxeff (alloc @heap) spin) (int ints) ints)
               (lambda (limit res)
                 (if (= limit 0)
                     res
                     (let ((limit (- limit 1)))
                       (_-*- limit (cons limit res)))))))
      (_-*- limit nil))))

; Iterate over the integers [0, limit).
(define* gnatural-for-each (subr graphs-eff (int (subr graphs-eff (int) unit)) unit)
  (lambda (limit proc!)
    (letrec ((loop (subr graphs-eff (int) unit)
               (lambda (i) (if (= i limit) #u (begin (proc! i) (loop (+ i 1)))))))
      (loop 0))))

(define* natural-for-all? (subr graphs-eff (int (subr graphs-eff (int) bool)) bool)
  (lambda (limit ok?)
    (letrec ((_-*- (subr graphs-eff (int) bool)
               (lambda (i) (or (= i limit) (and (ok? i) (_-*- (+ i 1)))))))
      (_-*- 0))))

(define* there-exists? (subr graphs-eff ((listof bvec @heap) (subr graphs-eff (bvec) bool)) bool)
  (lambda (lst ok?)
    (letrec ((_-*- (subr graphs-eff ((listof bvec @heap)) bool)
               (lambda (lst) (and (not (null? lst)) (or (ok? (car lst)) (_-*- (cdr lst)))))))
      (_-*- lst))))

(define* list-length (subr (maxeff (read @heap) spin) (glist int) int)
  (lambda (l n) (if (null? l) n (list-length (cdr l) (+ n 1)))))

;;; ==== ptfold.ss ====

; Fold over the tree of permutations of a universe.
; Each branch (from the root) is a permutation of universe.
; Each node at depth d corresponds to all permutations which pick the
; elements spelled out on the branch from the root to that node as
; the first d elements.
; Their are two components to the state:
;       The b-state is only a function of the branch from the root.
;       The t-state is a function of all nodes seen so far.
; At each node, b-folder is called via
;       (b-folder elem b-state t-state deeper accross)
; where elem is the next element of the universe picked.
; If b-folder can determine the result of the total tree fold at this stage,
; it should simply return the result.
; If b-folder can determine the result of folding over the sub-tree
; rooted at the resulting node, it should call accross via
;       (accross new-t-state)
; where new-t-state is that result.
; Otherwise, b-folder should call deeper via
;       (deeper new-b-state new-t-state)
; where new-b-state is the b-state for the new node and new-t-state is
; the new folded t-state.
; At the leaves of the tree, t-folder is called via
;       (t-folder b-state t-state accross)
; If t-folder can determine the result of the total tree fold at this stage,
; it should simply return that result.
; If not, it should call accross via
;       (accross new-t-state)
; Note, fold-over-perm-tree always calls b-folder in depth-first order.
; I.e., when b-folder is called at depth d, the branch leading to that
; node is the most recent calls to b-folder at all the depths less than d.
; This is a gross efficiency hack so that b-folder can use mutation to
; keep the current branch.
(define* fold-over-perm-tree (subr graphs-eff (ints bfolder int tfolder bool) bool)
  (lambda (universe b-folder b-state t-folder t-state)
    (letrec ((_-*- (subr graphs-eff (ints int bool accross) bool)
               (lambda (universe b-state t-state accross)
                 (if (null? universe)
                     (t-folder b-state t-state accross)
                     (letrec ((_-**- (subr graphs-eff (ints ints bool) bool)
                                (lambda (in out t-state)
                                  (let* ((first (car in))
                                         (rest (cdr in))
                                         (accross (if (null? rest)
                                                      accross
                                                      (the accross
                                                        (lambda ((new-t-state bool))
                                                          (_-**- rest (cons first out) new-t-state))))))
                                    (b-folder first
                                              b-state
                                              t-state
                                              (lambda ((new-b-state int) (new-t-state bool))
                                                (_-*- (fold out cons rest) new-b-state new-t-state accross))
                                              accross)))))
                       (_-**- universe nil t-state))))))
      (_-*- universe b-state t-state (lambda ((final-t-state bool)) final-t-state)))))

;;; ==== minimal.ss ====

; Given a graph, a partial permutation vector, the next input and the next
; output, return 'less, 'equal or 'more depending on the lexicographic
; comparison between the permuted and un-permuted graph.
(define* cmp-next-vertex (subr (maxeff (read @heap) spin) (gmat perm int int) symbol)
  (lambda (graph perm x perm-x)
    (let ((from-x (array-ref graph x))
          (from-perm-x (array-ref graph perm-x)))
      (letrec ((_-*- (subr (maxeff (read @heap) spin (read (globals bool=?))) (int) symbol)
                 (lambda (y)
                   (if (= x y)
                       'equal
                       (let ((x->y? (array-ref from-x y))
                             (perm-y (array-ref perm y)))
                         (cond ((bool=? x->y? (array-ref from-perm-x perm-y))
                                (let ((y->x? (array-ref (array-ref graph y) x)))
                                  (cond ((bool=? y->x? (array-ref (array-ref graph perm-y) perm-x))
                                         (_-*- (+ y 1)))
                                        (y->x? 'less)
                                        (else 'more))))
                               (x->y? 'less)
                               (else 'more)))))))
        (_-*- 0)))))
; A directed graph is stored as a connection matrix (vector-of-vectors)
; where the first index is the `from' vertex and the second is the `to'
; vertex.  Each entry is a bool indicating if the edge exists.
; The diagonal of the matrix is never examined.
; Make-minimal? returns a procedure which tests if a labelling
; of the verticies is such that the matrix is minimal.
; If it is, then the procedure returns the result of folding over
; the elements of the automoriphism group.  If not, it returns #f.
; The folding is done by calling folder via
;       (folder perm state accross)
; If the folder wants to continue, it should call accross via
;       (accross new-state)
; If it just wants the entire minimal? procedure to return something,
; it should return that.
; The ordering used is lexicographic (with #t > #f) and entries
; are examined in the following order:
;       1->0, 0->1
;
;       2->0, 0->2
;       2->1, 1->2
;
;       3->0, 0->3
;       3->1, 1->3
;       3->2, 2->3
;       ...
(define* make-minimal? (subr graphs-eff (int) minimal)
  (lambda (max-size)
    (let ((iotas (proc->vector (+ max-size 1) giota))
          (perm (the perm (make-array max-size 0))))
      (lambda ((size int) (graph gmat) (folder mfolder) (state bool))
        (fold-over-perm-tree (array-ref iotas size)
                             (lambda ((perm-x int) (x int) (state bool) (deeper deeper) (accross accross))
                               (let ((c (cmp-next-vertex graph perm x perm-x)))
                                 (cond ((symbol=? c 'less) #f)
                                       ((symbol=? c 'equal)
                                        (begin (array-set! perm x perm-x)
                                               (deeper (+ x 1) state)))
                                       (else ; 'more
                                        (accross state)))))
                             0
                             (lambda ((leaf-depth int) (state bool) (accross accross))
                               (folder perm state accross))
                             state)))))


;;; ==== rdg.ss ====

; Given a vector which maps vertex to out-going-edge list,
; return a vector  which gives reachability.
(define* make-reach? (subr graphs-eff (int graph) gmat)
  (lambda (size vertex->out)
    (let ((res (proc->vector size
                             (lambda ((v int))
                               (let ((from-v (the bvec (make-array size #f))))
                                 (letrec ((for-each (subr (maxeff (read @heap) (write @heap) spin) (ints) unit)
                                            (lambda (xs)
                                              (if (null? xs)
                                                  #u
                                                  (begin (array-set! from-v (car xs) #t)
                                                         (for-each (cdr xs)))))))
                                   (begin
                                     (array-set! from-v v #t)
                                     (for-each (array-ref vertex->out v))
                                     from-v)))))))
      (begin
        (gnatural-for-each size
                           (lambda ((m int))
                             (let ((from-m (array-ref res m)))
                               (gnatural-for-each size
                                                  (lambda ((f int))
                                                    (let ((from-f (array-ref res f)))
                                                      (if (array-ref from-f m)
                                                          (gnatural-for-each size
                                                                             (lambda ((t int))
                                                                               (if (array-ref from-m t)
                                                                                   (array-set! from-f t #t)
                                                                                   #u)))
                                                          #u)))))))
        res))))
; Fold over rooted directed graphs with bounded out-degree.
; Size is the number of verticies (including the root).  Max-out is the
; maximum out-degree for any vertex.  Folder is called via
;       (folder edges state)
; where edges is a list of length size.  The ith element of the list is
; a list of the verticies j for which there is an edge from i to j.
; The last vertex is the root.
(define* fold-over-rdg (subr graphs-eff (int int rdg-folder glist) glist)
  (lambda (size max-out folder state)
    (let* ((root (- size 1))
           (edge? (proc->vector size (lambda ((from int)) (the bvec (make-array size #f)))))
           (edges (the graph (make-array size nil)))
           (out-degrees (the perm (make-array size 0)))
           (minimal-folder (make-minimal? root))
           (non-root-minimal?
            (let ((cont (lambda ((perm perm) (state bool) (accross accross))
                          (accross #t))))
              (lambda ((size int))
                (minimal-folder size edge? cont #t))))
           (root-minimal?
            (let ((cont (lambda ((perm perm) (state bool) (accross accross))
                          (let ((c (cmp-next-vertex edge? perm root root)))
                            (cond ((symbol=? c 'less) #f)
                                  (else ; 'equal, 'more
                                   (accross #t)))))))
              (lambda ()
                (minimal-folder root edge? cont #t)))))
      (letrec ((_-*- (subr graphs-eff (int glist) glist)
                 (lambda (vertex state)
                   (cond ((not (non-root-minimal? vertex))
                          state)
                         ((= vertex root)
                          (let ((reach? (make-reach? root edges))
                                (from-root (array-ref edge? root)))
                            (letrec ((_-*- (subr graphs-eff (int int ints (listof bvec @heap) glist) glist)
                                       (lambda (v outs efr efrr state)
                                         (cond ((not (or (= v root)
                                                         (= outs max-out)))
                                                (begin
                                                  (array-set! from-root v #t)
                                                  (let ((state (_-*- (+ v 1)
                                                                     (+ outs 1)
                                                                     (cons v efr)
                                                                     (cons (array-ref reach? v) efrr)
                                                                     state)))
                                                    (begin
                                                      (array-set! from-root v #f)
                                                      (_-*- (+ v 1) outs efr efrr state)))))
                                               ((and (natural-for-all? root
                                                                       (lambda ((v int))
                                                                         (there-exists? efrr
                                                                                        (lambda ((r bvec))
                                                                                          (array-ref r v)))))
                                                     (root-minimal?))
                                                (begin
                                                  (array-set! edges root efr)
                                                  (folder (proc->vector size (lambda ((i int)) (array-ref edges i)))
                                                          state)))
                                               (else state)))))
                              (_-*- 0 0 nil nil state))))
                         (else
                          (let ((from-vertex (array-ref edge? vertex)))
                            (letrec ((_-**- (subr graphs-eff (int int glist) glist)
                                       (lambda (sv outs state)
                                         (if (= sv vertex)
                                             (begin
                                               (array-set! out-degrees vertex outs)
                                               (_-*- (+ vertex 1) state))
                                             (let* ((state
                                                     ; no sv->vertex, no vertex->sv
                                                     (_-**- (+ sv 1) outs state))
                                                    (from-sv (array-ref edge? sv))
                                                    (sv-out (array-ref out-degrees sv))
                                                    (state
                                                     (if (= sv-out max-out)
                                                         state
                                                         (begin
                                                           (array-set! edges sv (cons vertex (array-ref edges sv)))
                                                           (array-set! from-sv vertex #t)
                                                           (array-set! out-degrees sv (+ sv-out 1))
                                                           (let* ((state
                                                                   ; sv->vertex, no vertex->sv
                                                                   (_-**- (+ sv 1) outs state))
                                                                  (state
                                                                   (if (= outs max-out)
                                                                       state
                                                                       (begin
                                                                         (array-set! from-vertex sv #t)
                                                                         (array-set! edges vertex (cons sv (array-ref edges vertex)))
                                                                         (let ((state
                                                                                ; sv->vertex, vertex->sv
                                                                                (_-**- (+ sv 1) (+ outs 1) state)))
                                                                           (begin
                                                                             (array-set! edges vertex (cdr (array-ref edges vertex)))
                                                                             (array-set! from-vertex sv #f)
                                                                             state))))))
                                                             (begin
                                                               (array-set! out-degrees sv sv-out)
                                                               (array-set! from-sv vertex #f)
                                                               (array-set! edges sv (cdr (array-ref edges sv)))
                                                               state))))))
                                               (if (= outs max-out)
                                                   state
                                                   (begin
                                                     (array-set! edges vertex (cons sv (array-ref edges vertex)))
                                                     (array-set! from-vertex sv #t)
                                                     (let ((state
                                                            ; no sv->vertex, vertex->sv
                                                            (_-**- (+ sv 1) (+ outs 1) state)))
                                                       (begin
                                                         (array-set! from-vertex sv #f)
                                                         (array-set! edges vertex (cdr (array-ref edges vertex)))
                                                         state)))))))))
                              (_-**- 0 0 state))))))))
        (_-*- 0 state)))))


;;; ==== test input ====

; Produces all directed graphs with N verticies, distinguished root,
; and out-degree bounded by 2, upto isomorphism.

(define* run-graphs (subr graphs-eff (int) glist)
  (lambda (n) (fold-over-rdg n 2 cons nil)))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 7)
(define iterations int 3)

(define* run (subr graphs-eff (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (list-length (run-graphs input1) 0)))))
(run iterations 0)
