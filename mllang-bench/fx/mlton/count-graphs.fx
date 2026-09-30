;;; COUNT-GRAPHS -- count, up to isomorphism, the triangle-free graphs
;;; with 2E = 3V - 4 all of whose full subgraphs have 2E <= 3V - 4 (or at
;;; most one vertex), of each size from 0 to 11, by folds over subsets and
;;; bag permutations.
;;;
;;; Written by Henry Cejtin (henry@sourcelight.com).
;;; From MLton's benchmark suite (benchmark/tests/count-graphs.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. MLton's driver was not fetched; the
;;; iteration count, 1 run of `doit` (sizes 0 to 11 once), is this port's:
;;; one run already takes about 25 s natively. MLton's `doit n` runs n.
;;; Answer: (0 0 1 1 2 2 4 4 20 20 250 250), the counts for sizes 0 to
;;; 11, which the original prints (its `print` is a no-op, so it prints
;;; nothing).
;;;
;;; What changed:
;;; - The polymorphic folds (`fold`, `naturalFold`, `foldOverBagPerms`,
;;;   `foldOverSubsets`, `foldOverGraphs`) are polymorphic here too
;;;   (`plambda`), instantiated where they are called; every callback has one
;;;   effect, `cg`, rather than each fold being polymorphic in its folder's.
;;; - Each local exception (`accross of 'a`, `fini`, `noextend of 'b`) is a
;;;   prompt tag made where SML declares it, on each call, passed to the
;;;   folders where SML passes the constructor; `raise (accross s)` aborts
;;;   to it, and `handle` is a prompt. `raise Domain`, never caught, aborts
;;;   to a tag no prompt is for (an error, as an uncaught exception is).
;;; - `op ::` passed to `fold` is a lambda that conses. Tuples are products;
;;;   `int option` is a datatype.
;;; - `Array.tabulate` and `Vector.tabulate` are used at two element types
;;;   (arrays of bools, lists of vertices): each is written once, for its
;;;   own; vectors are arrays. `List.tabulate` is used only for `fn v => v`,
;;;   and is written for ints.
;;; - `foldOverBagPerms`'s `inner` takes a bag and finds its first element
;;;   and the rest in it, in the body of its `handle`, where SML passes all
;;;   three: with them, that body (a closure, as a prompt's body is) was
;;;   over nine variables, more than `register-regs` (8), so the register
;;;   compiler declined `outer`, it ran as cellular code, and an abort from
;;;   native code found no prompt (reported).
;;; - `doOne`'s argument strings "0" … "11" are the integers themselves, and
;;;   `doit` makes the list of the counts rather than printing them. The
;;;   unused `foldOverPermutations`, the first `f`, `showGraph` and the
;;;   `show…List`s are left out.

(define-type ints (listof int @heap))
(define-type intss (listof ints @heap))
(define-datatype int-option (none) (some int))

;; Everything the folds and their folders may do; a prompt's body may do
;; all of it but abort (control on @z).
(define-effect cgd (maxeff (read @heap) (write @heap) (alloc @heap) (alloc @z) spin (read @globals)))
(define-effect cg (maxeff cgd (goto @z)))

;; `Domain`: never caught.
(define domain (prompt-tag unit unit cgd @z) (make-continuation-prompt-tag))

;; My favorite high-order procedure.
(define fold (poly ((a type) (s type)) (subr cg ((listof a @heap) (subr cg (a s) s) s) s))
  (plambda ((a type) (s type))
    (lambda (lst folder state)
      (letrec ((loop (subr cg ((listof a @heap) s) s)
                 (lambda (lst state)
                   (if (null? lst) state (loop (cdr lst) (folder (car lst) state))))))
        (loop lst state)))))

(define natural-fold (poly ((s type)) (subr cg (int (subr cg (int s) s) s) s))
  (plambda ((s type))
    (lambda (limit folder state)
      (if (< limit 0)
          (abort-current-continuation domain #u)
          (letrec ((loop (subr cg (int s) s)
                     (lambda (i state) (if (= i limit) state (loop (+ i 1) (folder i state))))))
            (loop 0 state))))))

(define* natural-any (subr cg (int (subr cg (int) bool)) bool)
  (lambda (limit ok)
    (if (< limit 0)
        (abort-current-continuation domain #u)
        (letrec ((loop (subr cg (int) bool)
                   (lambda (i) (and (not (= i limit)) (or (ok i) (loop (+ i 1)))))))
          (loop 0)))))

(define* natural-all (subr cg (int (subr cg (int) bool)) bool)
  (lambda (limit ok)
    (if (< limit 0)
        (abort-current-continuation domain #u)
        (letrec ((loop (subr cg (int) bool)
                   (lambda (i) (or (= i limit) (and (ok i) (loop (+ i 1)))))))
          (loop 0)))))

;; Fold over all arrangements of bag elements.
;; Universe is a list of lists of items, with equivalent items in the
;; same list.
;; pFolder is used to build up the permutation.  It is called via
;;      pFolder (next, pState, state, accross)
;; where next is the next item in the permutation, pState is the
;; partially constructed permutation and state is the current fold
;; state over permutations that have already been considered.
;; If pFolder knows what will result from folding over all permutations
;; descending from the resulting partial permutation (starting at state),
;; it should raise the accross exception carrying the new state value.
;; If pFolder wants to continue building up the permutation, it should
;; return (newPState, newState).
;; When a permutation has been completely constructed, folder is called
;; via
;;      folder (pState, state)
;; where pState is the final pState and state is the current state.
;; It should return the new state.
(define fold-over-bag-perms
  (poly ((a type) (p type) (s type))
    (subr cg ((listof (listof a @heap) @heap)
              (subr cg (a p s (prompt-tag s s cgd @z)) (productof (pst p) (st s)))
              p
              (subr cg (p s) s)
              s)
          s))
  (plambda ((a type) (p type) (s type))
    (lambda (universe pfolder pstate folder state)
      (let ((accross (the (prompt-tag s s cgd @z) (make-continuation-prompt-tag))))
        (letrec ((outer (subr cg ((listof (listof a @heap) @heap) p s) s)
                   (lambda (universe pstate state)
                     (if (null? universe)
                         (folder pstate state)
                         (letrec ((inner (subr cg ((listof a @heap) (listof (listof a @heap) @heap) (listof (listof a @heap) @heap) s) s)
                                    (lambda (fbag rest rev-out state)
                                      (let ((state
                                              (prompt accross
                                                (let* ((first (car fbag))
                                                       (fclone (cdr fbag))
                                                       (r (pfolder first pstate state accross)))
                                                  (outer (fold rev-out
                                                               (lambda ((b (listof a @heap)) (l (listof (listof a @heap) @heap)))
                                                                 (the (listof (listof a @heap) @heap) (cons b l)))
                                                               (if (null? fclone) rest (the (listof (listof a @heap) @heap) (cons fclone rest))))
                                                         (extract r pst)
                                                         (extract r st)))
                                                (lambda (state) state))))
                                        (if (null? rest)
                                            state
                                            (let ((sbag (car rest)))
                                              (inner sbag (cdr rest)
                                                     (the (listof (listof a @heap) @heap) (cons fbag rev-out))
                                                     state)))))))
                           (let ((fbag (car universe)))
                             (inner fbag (cdr universe) nil state)))))))
          (outer universe pstate state))))))

;; Fold over the tree of subsets of the elements of universe.
;; The tree structure comes from the root picking if the first element
;; is in the subset, etc.
;; eFolder is called to build up the subset given a decision on wether
;; or not a given element is in it or not.  It is called via
;;      eFolder (elem, isinc, eState, state, fini)
;; If this determines the result of folding over all the subsets consistant
;; with the choice so far, then eFolder should raise the exception
;;      fini newState
;; If we need to proceed deeper in the tree, then eFolder should return
;; the tuple
;;      (newEState, newState)
;; folder is called to buld up the final state, folding over subsets
;; (represented as the terminal eStates).  It is called via
;;      folder (eState, state)
;; It returns the new state.
;; Note, the order in which elements are folded (via eFolder) is the same
;; as the order in universe.
(define fold-over-subsets
  (poly ((a type) (e type) (s type))
    (subr cg ((listof a @heap)
              (subr cg (a bool e s (prompt-tag s s cgd @z)) (productof (pst e) (st s)))
              e
              (subr cg (e s) s)
              s)
          s))
  (plambda ((a type) (e type) (s type))
    (lambda (universe efolder estate folder state)
      (let ((fini (the (prompt-tag s s cgd @z) (make-continuation-prompt-tag))))
        (letrec ((f (subr cg (a (listof a @heap) e) (subr cg (bool s) s))
                   (lambda (first rest estate)
                     (lambda ((isinc bool) (state s))
                       (prompt fini
                         (let ((r (efolder first isinc estate state fini)))
                           (outer rest (extract r pst) (extract r st)))
                         (lambda (state) state)))))
                 (outer (subr cg ((listof a @heap) e s) s)
                   (lambda (universe estate state)
                     (if (null? universe)
                         (folder estate state)
                         (let ((f (f (car universe) (cdr universe) estate)))
                           (f #f (f #t state)))))))
          (outer universe estate state))))))

;; Given a partitioning of [0, size) into equivalence classes (as a list
;; of the classes, where each class is a list of integers), and where two
;; vertices are equivalent iff transposing the two is an automorphism
;; of the full subgraph on the vertices [0, size), return the equivalence
;; classes for the graph.  The graph is provided as a connection function.
;; In the result, two equivalent vertices in [0, size) remain equivalent
;; iff they are either both connected or neither is connected to size.
;; The vertex size is equivalent to a vertex x in [0, size) iff
;;      connected (size, y) = connected (x, if y = x then size else y)
;; for all y in [0, size).
(define-type merge-state (productof (merged bool) (classes intss)))
(define-type split-state (productof (yes ints) (no ints)))

(define* refine (subr cg (int intss (subr cg (int int) bool)) intss)
  (lambda (size classes connected)
    (letrec ((size-match (subr cg (int) bool)
               ;; Check if vertex size is equivalent to vertex x.
               (lambda (x)
                 (natural-all size
                   (lambda ((y int))
                     (let ((c1 (connected size y)))
                       (let ((c2 (connected x (if (= y x) size y))))
                         (if c1 c2 (not c2))))))))
             (merge (subr cg (ints merge-state) merge-state)
               ;; Add class into classes, testing if size should be merged.
               (lambda (class state)
                 (let ((classes (extract state classes)))
                   (if (extract state merged)
                       (product (merged #t) (classes (the intss (cons (the ints (reverse class)) classes))))
                       (let ((first (car class)))
                         (if (size-match first)
                             (product (merged #t)
                                      (classes (the intss (cons (fold class (lambda ((x int) (l ints)) (the ints (cons x l))) (the ints (cons size nil)))
                                                                classes))))
                             (product (merged #f) (classes (the intss (cons (the ints (reverse class)) classes))))))))))
             (split (subr cg (int split-state) split-state)
               (lambda (elem state)
                 (if (connected elem size)
                     (product (yes (the ints (cons elem (extract state yes)))) (no (extract state no)))
                     (product (yes (extract state yes)) (no (the ints (cons elem (extract state no))))))))
             (subdivide (subr cg (ints merge-state) merge-state)
               (lambda (class state)
                 (if (and (not (null? class)) (null? (cdr class)))
                     (merge class state)
                     (let* ((r (fold class split (product (yes (the ints nil)) (no (the ints nil)))))
                            (yes (extract r yes))
                            (no (extract r no)))
                       (cond ((null? yes) (merge no state))
                             ((null? no) (merge yes state))
                             (else (merge no (merge yes state)))))))))
      (let ((r (fold classes subdivide (product (merged #f) (classes (the intss nil))))))
        (if (extract r merged)
            (the intss (reverse (extract r classes)))
            (fold (extract r classes)
                  (lambda ((c ints) (l intss)) (the intss (cons c l)))
                  (the intss (cons (the ints (cons size nil)) nil))))))))

;; Given a count of the number of vertices, a partitioning of the vertices
;; into equivalence classes (where two vertices are equivalent iff
;; transposing them is a graph automorphism), and a function which, given
;; two distinct vertices, returns a bool indicating if there is an edge
;; connecting them, check if the graph is minimal.
;; If it is, return
;;      SOME how-many-clones-we-walked-through
;; If not, return NONE.
;; A graph is minimal iff its connection matrix is (weakly) smaller
;; then all its permuted friends, where true is less than false, and
;; the entries are compared lexicographically in the following order:
;;      -
;;      0 -
;;      1 2 -
;;      3 4 5 -
;;      ...
;; Note, the vertices are the integers in [0, nverts).
(define* minimal (subr cg (int intss (subr cg (int int) bool)) int-option)
  (lambda (nverts classes connected)
    (let ((perm (the (arrayof int @heap) (make-array nverts -1)))
          (fini (the (prompt-tag int-option unit cgd @z) (make-continuation-prompt-tag))))
      (letrec ((pfolder (subr cg (int int int (prompt-tag int int cgd @z)) (productof (pst int) (st int)))
                 (lambda (new old state accross)
                   (letrec ((loop (subr cg (int) (productof (pst int) (st int)))
                              (lambda (v)
                                (if (= v old)
                                    (begin (array-set! perm old new)
                                           (product (pst (+ old 1)) (st state)))
                                    (let* ((a (connected old v))
                                           (b (connected new (array-ref perm v))))
                                      (cond ((and a (not b)) (abort-current-continuation accross state))
                                            ((and (not a) b) (abort-current-continuation fini #u))
                                            (else (loop (+ v 1)))))))))
                     (loop 0))))
               (folder (subr cg (int int) int) (lambda (p state) (+ state 1))))
        (prompt fini
          (some (fold-over-bag-perms classes pfolder 0 folder 0))
          (lambda (u) (none)))))))

(define* list-tabulate (subr cg (int (subr cg (int) int)) ints)
  (lambda (n f)
    (letrec ((loop (subr cg (int ints) ints)
               (lambda (i l) (if (< i 0) l (loop (- i 1) (the ints (cons (f i) l)))))))
      (loop (- n 1) nil))))

;; Fold over the tree of graphs.
;;
;; eFolder is used to fold over the choice of edges via
;;      eFolder (from, to, isinc, eState, state, accross)
;; with from > to.
;;
;; If eFolder knows the result of folding over all graphs which agree
;; with the currently made decisions, then it should raise the accross
;; exception carrying the resulting state as a value.
;;
;; To continue normally, it should return the tuple
;;      (newEState, newState)
;;
;; When all decisions are made with regards to edges from `from', folder
;; is called via
;;      folder (size, eState, state, accross)
;; where size is the number of vertices in the graph (the last from+1) and
;; eState is the final eState for edges from `from'.
;;
;; If folder knows the result of folding over all extensions of this graph,
;; it should raise accross carrying the resulting state as a value.
;;
;; If extensions of this graph should be folded over, it should return
;; the new state.
(define* make-vertss (subr cg (int) (arrayof ints @heap))
  (lambda (limit)
    (let ((v (the (arrayof ints @heap) (make-array limit nil))))
      (letrec ((loop (subr cg (int) (arrayof ints @heap))
                 (lambda (nverts)
                   (if (= nverts limit)
                       v
                       (begin (array-set! v nverts (list-tabulate nverts (lambda ((v int)) v)))
                              (loop (+ nverts 1)))))))
        (loop 0)))))

(define fold-over-graphs
  (poly ((a type) (b type))
    (subr cg ((subr cg (int int bool a b (prompt-tag b b cgd @z)) (productof (pst a) (st b)))
              a
              (subr cg (int a b (prompt-tag b b cgd @z)) b)
              b)
          b))
  (plambda ((a type) (b type))
    (lambda (efolder estate folder state)
      (let ((noextend (the (prompt-tag b b cgd @z) (make-continuation-prompt-tag)))
            (vertss (the (ref (arrayof ints @heap) @heap) (new (make-vertss 0)))))
        (letrec ((find-verts (subr cg (int) ints)
                   (lambda (size)
                     (begin
                       (if (>= size (array-length (get vertss)))
                           (set vertss (make-vertss (+ size 1)))
                           #u)
                       (array-ref (get vertss) size))))
                 (f (subr cg (int a b) b)
                   (lambda (size estate state)
                     (prompt noextend
                       (let ((state (folder size estate state noextend)))
                         (g (+ size 1) state))
                       (lambda (state) state))))
                 (g (subr cg (int b) b)
                   (lambda (size state)
                     (let ((indices (find-verts (- size 1))))
                       (letrec ((se-folder (subr cg (int bool a b (prompt-tag b b cgd @z)) (productof (pst a) (st b)))
                                  (lambda (to isinc estate state accross)
                                    (efolder (- size 1) to isinc estate state accross)))
                                (sf (subr cg (a b) b)
                                  (lambda (estate state) (f size estate state))))
                         (fold-over-subsets indices se-folder estate sf state))))))
          (f 0 estate state))))))

;; Given the size of a graph, a list of the vertices (the integers in
;; [0, size)), and the connected function, check if for all full subgraphs,
;;      3*V - 4 - 2*E >= 0 or V <= 1
;; where V is the number of vertices and E is the number of edges.
(define* short (subr (read @heap) (ints) bool)
  (lambda (lst) (or (null? lst) (null? (cdr lst)))))

(define-type ok-state (productof (ac int) (picked ints)))

(define* ok-so-far (subr cg (int ints (subr cg (int int) bool)) bool)
  (lambda (size verts connected)
    (let ((fini (the (prompt-tag bool unit cgd @z) (make-continuation-prompt-tag))))
      (letrec ((efolder (subr cg (int bool ok-state unit (prompt-tag unit unit cgd @z)) (productof (pst ok-state) (st unit)))
                 (lambda (elem isinc estate u accross)
                   (product
                     (pst (if isinc
                              (let ((picked (extract estate picked)))
                                (product (ac (fold picked
                                                   (lambda ((p int) (ac int)) (if (connected elem p) (- ac 2) ac))
                                                   (+ (extract estate ac) 3)))
                                         (picked (the ints (cons elem picked)))))
                              estate))
                     (st #u))))
               (folder (subr cg (ok-state unit) unit)
                 (lambda (estate state)
                   (if (or (>= (extract estate ac) 0) (short (extract estate picked)))
                       state
                       (abort-current-continuation fini #u)))))
        (prompt fini
          (begin (fold-over-subsets verts efolder (product (ac -4) (picked (the ints nil))) folder #u)
                 #t)
          (lambda (u) #f))))))

(define* h (subr cg (int (subr cg (int (subr cg (int int) bool) int) int) int) int)
  (lambda (max-size folder state)
    (let ((ctab (the (arrayof (arrayof bool @heap) @heap) (make-array max-size (the (arrayof bool @heap) (make-array 0 #f)))))
          (classesv (the (arrayof intss @heap) (make-array (+ max-size 1) nil))))
      (letrec ((tabulate (subr cg (int) unit)
                 (lambda (v)
                   (if (= v max-size)
                       #u
                       (begin (array-set! ctab v (the (arrayof bool @heap) (make-array v #f)))
                              (tabulate (+ v 1))))))
               (connected (subr cg (int int) bool)
                 (lambda (from to)
                   (let ((f (if (> from to) from to))
                         (t (if (> from to) to from)))
                     (array-ref (array-ref ctab f) t))))
               (update (subr cg (int int bool) unit)
                 (lambda (from to value)
                   (let ((f (if (> from to) from to))
                         (t (if (> from to) to from)))
                     (array-set! (array-ref ctab f) t value))))
               (triangle (subr cg (int int) bool)
                 (lambda (vnum e)
                   (natural-any e (lambda ((f int)) (and (connected vnum f) (connected e f))))))
               (efolder (subr cg (int int bool unit int (prompt-tag int int cgd @z)) (productof (pst unit) (st int)))
                 (lambda (from to isinc u state accross)
                   (if (and isinc (triangle from to))
                       (abort-current-continuation accross state)
                       (begin (update from to isinc)
                              (product (pst #u) (st state))))))
               (gfolder (subr cg (int unit int (prompt-tag int int cgd @z)) int)
                 (lambda (size u state accross)
                   (begin
                     (if (not (= size 0))
                         (array-set! classesv size (refine (- size 1) (array-ref classesv (- size 1)) connected))
                         #u)
                     (tagcase (minimal size (array-ref classesv size) connected)
                       (none () (abort-current-continuation accross state))
                       (some (eat-me)
                         (if (ok-so-far size (list-tabulate size (lambda ((v int)) v)) connected)
                             (let ((state (folder size connected state)))
                               (if (= size max-size)
                                   (abort-current-continuation accross state)
                                   state))
                             (abort-current-continuation accross state))))))))
        (begin
          (tabulate 0)
          (fold-over-graphs efolder #u gfolder state))))))

(define* final (subr cg (int (subr cg (int int) bool)) int)
  (lambda (size connected)
    (natural-fold size
                  (lambda ((from int) (ac int))
                    (natural-fold from
                                  (lambda ((to int) (ac int)) (if (connected from to) (- ac 2) ac))
                                  ac))
                  (- (* 3 size) 4))))

;; SML's second `f`.
(define* count (subr cg (int) int)
  (lambda (max-size)
    (h max-size
       (lambda ((size int) (connected (subr cg (int int) bool)) (state int))
         (if (= (final size connected) 0) (+ state 1) state))
       0)))

(define args ints
  (list 0 1 2 3 4 5 6 7 8 9 10 11))

(define* doit (subr cg () ints)
  (lambda ()
    (letrec ((loop (subr cg (ints) ints)
               (lambda (l) (if (null? l) nil (the ints (cons (count (car l)) (loop (cdr l))))))))
      (loop args))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 1)

(define* run (subr cg (int ints) ints)
  (lambda (i result) (if (= i 0) result (run (- i 1) (doit)))))
(run iterations nil)
