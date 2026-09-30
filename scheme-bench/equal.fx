;;; EQUAL -- tests the R6RS equal? predicate on some fairly large
;;; structures of various shapes.
;;;
;;; Copyright 2007 William D Clinger.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/equal.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of
;;; (equality-benchmarks 100 100 8 1000 2000 5000).
;;; Answer: #t.
;;;
;;; FX-26 has no `equal?`, and the benchmark measures the implementation's,
;;; so the port carries Larceny's own (src/Lib/Common/preds.sch, Clinger
;;; 2006-2007): the traditional recursive algorithm to a bounded depth,
;;; then Hopcroft and Karp's terminating one, which keeps equivalence
;;; classes of pairs and vectors in tables keyed by identity. Scheme's
;;; values are an `obj` datatype of the kinds the benchmark makes: `()`,
;;; symbols, mutable pairs (`(pairof obj obj @heap)`) and vectors (arrays).
;;; `eq?`/`eqv?` of objs is `obj-eqv?`: `eq?` of the pairs, of the arrays
;;; and of the symbols, which is exact on all three. Larceny's one table of
;;; pairs and vectors is two `eqtable`s, one per kind: `equate!` only ever
;;; merges the classes of two pairs or of two vectors, so a class holds one
;;; kind, and `done?` and `equate!` are polymorphic in it. Larceny's
;;; cases for bytevectors, strings and texts, which the benchmark never
;;; makes, are left out. The bounded `equal?`, which returns `#f` or the
;;; bound left, returns -1 for `#f` (the bound left is never negative).
;;; Larceny's local procedures of `equal?` that close over nothing are
;;; top-level ones; `equiv?`'s, which close over its tables, stay local.
;;; `hide` of the thunks is left out (the inputs are globals).
;;; `equality-benchmark5`'s optional iteration count is a second argument,
;;; and `equality-benchmark5short`, never called, is left out.

(define-datatype obj (empty) (sym symbol) (pr (pairof obj obj @heap)) (vec (arrayof obj @heap)))
(define-type opair (pairof obj obj @heap))
(define-type ovec (arrayof obj @heap))
(define-effect heap-use (maxeff (read @heap) (write @heap) (alloc @heap) spin))

;; Scheme's `eqv?` (and `eq?`) of the objects here.
(define obj-eqv? (subr pure (obj obj) bool)
  (lambda (x y)
    (tagcase x
      (empty () (tagcase y (empty () #t) (else z #f)))
      (sym (s) (tagcase y (sym (t) (eq? s t)) (else z #f)))
      (pr (p) (tagcase y (pr (q) (eq? p q)) (else z #f)))
      (vec (v) (tagcase y (vec (w) (eq? v w)) (else z #f))))))

(define obj-pair? (subr pure (obj) bool)
  (lambda (x) (tagcase x (pr (p) #t) (else z #f))))

(define obj-vector? (subr pure (obj) bool)
  (lambda (x) (tagcase x (vec (v) #t) (else z #f))))

(define obj-cdr (subr (read @heap) (obj) obj)
  (lambda (x) (tagcase x (pr (p) (cdr p)) (else z (error "cdr: not a pair")))))

(define obj-set-cdr! (subr (write @heap) (obj obj) unit)
  (lambda (x y) (tagcase x (pr (p) (set-cdr! p y)) (else z (error "set-cdr!: not a pair")))))

(define* obj-list-tail (subr (maxeff (read @heap) spin) (obj int) obj)
  (lambda (x k) (if (zero? k) x (obj-list-tail (obj-cdr x) (- k 1)))))

(define* obj-vector->list (subr (maxeff (read @heap) (alloc @heap) spin) (ovec) obj)
  (lambda (v)
    (letrec ((loop (subr (maxeff (read @heap) (alloc @heap) spin) (int obj) obj)
               (lambda (i acc) (if (< i 0) acc (loop (- i 1) (pr (cons (array-ref v i) acc)))))))
      (loop (- (array-length v) 1) (empty)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Larceny's `equal?` (src/Lib/Common/preds.sch).
;;;
;;; EQUIV? is a version of EQUAL? that terminates on all arguments.
;;;
;;; The basic idea of the algorithm is presented in
;;;
;;; J E Hopcroft and R M Karp.  A Linear Algorithm for
;;; Testing Equivalence of Finite Automata.
;;; Cornell University Technical Report 71-114,
;;; December 1971.
;;;
;;; The algorithm uses FIND and MERGE operations, which
;;; roughly correspond to done? and equate! in the code below.
;;; The algorithm maintains a stack of comparisons to do,
;;; and a set of equivalences that would be implied by the
;;; comparisons yet to be done.
;;;
;;; When comparing objects x and y whose equality cannot be
;;; determined without recursion, the algorithm pushes all
;;; the recursive subgoals onto the stack, and merges the
;;; equivalence classes for x and y.  If any of the subgoals
;;; involve comparing x and y, the algorithm will notice
;;; that they are in the same equivalence class and will
;;; avoid circularity by assuming x and y are equal.
;;; If all of the subgoals succeed, then x and y really are
;;; equal, so the algorithm is correct.
;;;
;;; If the hash tables give amortized constant-time lookup on
;;; object identity, then this algorithm could be made to run
;;; in O(n) time, where n is the number of nodes in the larger
;;; of the two structures being compared.
;;;
;;; This implementation uses two techniques to reduce the
;;; cost of the algorithm for common special cases:
;;;
;;; It starts out by trying the traditional recursive algorithm
;;; to bounded depth.
;;; It handles easy cases specially.

;; How long should we try the traditional recursive algorithm
;; before switching to the terminating algorithm?
(define equal:bound-on-recursion int 5000000)

;; The traditional recursive algorithm, with bounded recursion.
;; Returns #f (here -1) or an exact integer n.
;; If n > 0, then x and y are equal and the comparison involved
;; bound - n recursive calls.
;; If n <= 0, then the algorithm terminated before
;; it could determine whether x and y are equal.
(define* bounded-equal? (subr (maxeff (read @heap) spin) (obj obj int) int)
  (lambda (x y bound)
    (cond ((obj-eqv? x y) bound)
          ((<= bound 0) bound)
          (else
           (tagcase x
             (pr (px)
               (tagcase y
                 (pr (py)
                   (if (obj-eqv? (car px) (car py))
                       (bounded-equal? (cdr px) (cdr py) (- bound 1))
                       (let ((result (bounded-equal? (car px) (car py) (- bound 1))))
                         (if (>= result 0)
                             (bounded-equal? (cdr px) (cdr py) result)
                             -1))))
                 (else z -1)))
             (vec (vx)
               (tagcase y
                 (vec (vy)
                   (let ((nx (array-length vx))
                         (ny (array-length vy)))
                     (if (= nx ny)
                         (letrec ((loop (subr (maxeff (read @heap) spin) (int int) int)
                                    (lambda (i bound)
                                      (if (< i nx)
                                          (let ((result (bounded-equal? (array-ref vx i)
                                                                        (array-ref vy i)
                                                                        bound)))
                                            (if (>= result 0)
                                                (loop (+ i 1) result)
                                                -1))
                                          bound))))
                           (loop 0 (- bound 1)))
                         -1)))
                 (else z -1)))
             (else z -1))))))

;; A comparison is easy if eqv? returns the right answer.
(define* easy? (subr pure (obj obj) bool)
  (lambda (x y)
    (cond ((obj-eqv? x y) #t)
          ((obj-pair? x) (not (obj-pair? y)))
          ((obj-pair? y) #t)
          ((obj-vector? x) (not (obj-vector? y)))
          ((obj-vector? y) #t)
          (else #f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Tables mapping objects to their equivalence classes.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; FIXME:  Equivalence classes are represented as lists,
; which means they can't be merged in constant time.

(define-type (classes (k type)) (eqtable k (listof k @heap) @heap @heap))

(define memq (poly ((k type)) (subr (maxeff (read @heap) spin) (k (listof k @heap)) bool))
  (plambda ((k type))
    (lambda (x l)
      (letrec ((loop (subr (maxeff (read @heap) spin) ((listof k @heap)) bool)
                 (lambda (l) (if (null? l) #f (if (eq? x (car l)) #t (loop (cdr l)))))))
        (loop l)))))

; Are x and y equivalent according to the table?
(define done?
  (poly ((k type))
    (subr (maxeff (read @heap) (write @heap) spin (read (globals memq))) (k k (classes k)) bool))
  (plambda ((k type))
    (lambda (x y table) (memq x (eqtable-ref table y nil)))))

; Merge the equivalence classes of x and y in the table.
; Changes the table.
(define equate!
  (poly ((k type)) (subr (maxeff heap-use (read (globals memq))) (k k (classes k)) unit))
  (plambda ((k type))
    (lambda (x y table)
      (let ((xclass (eqtable-ref table x nil))
            (yclass (eqtable-ref table y nil)))
        (cond ((and (null? xclass) (null? yclass))
               (let ((class (the (listof k @heap) (list x y))))
                 (begin (eqtable-set! table x class)
                        (eqtable-set! table y class))))
              ((null? xclass)
               (let ((class0 (the (listof k @heap) (cons x (cdr yclass)))))
                 (begin (set-cdr! yclass class0)
                        (eqtable-set! table x yclass))))
              ((null? yclass)
               (let ((class0 (the (listof k @heap) (cons y (cdr xclass)))))
                 (begin (set-cdr! xclass class0)
                        (eqtable-set! table y xclass))))
              ((eq? xclass yclass) #u)
              ((memq x yclass) #u)
              (else
               (let ((class0 (append (cdr xclass) yclass)))
                 (begin
                   (set-cdr! xclass class0)
                   (letrec ((for-each (subr heap-use ((listof k @heap)) unit)
                              (lambda (l)
                                (if (null? l)
                                    #u
                                    (begin (eqtable-set! table (car l) xclass)
                                           (for-each (cdr l)))))))
                     (for-each yclass))))))))))

;; Returns #t iff x and y would have the same (possibly infinite)
;; printed representation.  Always terminates.
(define* equiv? (subr heap-use (obj obj) bool)
  (lambda (x y)
    (let ((pdone (the (classes opair) (make-eqtable (pair-identity))))
          (vdone (the (classes ovec) (make-eqtable (array-identity)))))

      ;; done is a hash table that maps objects to their
      ;; equivalence classes (here two, one per kind).
      ;;
      ;; Algorithmic invariant:  If all of the comparisons that
      ;; are in progress (pushed onto the control stack) come out
      ;; equal, then all of the equivalences in done are correct.
      ;;
      ;; Invariant of this prototype:  The equivalence classes include
      ;; only pairs and vectors.

      (letrec ((equiv? (subr heap-use (obj obj) bool)
                 (lambda (x y)
                   (if (obj-eqv? x y)
                       #t
                       (tagcase x
                         (pr (px) (tagcase y (pr (py) (pair-equiv? px py)) (else z #f)))
                         (vec (vx)
                           (tagcase y
                             (vec (vy)
                               (let ((n (array-length vx)))
                                 (if (= n (array-length vy))
                                     (if (done? vx vy vdone)
                                         #t
                                         (begin (equate! vx vy vdone)
                                                (vector-equiv? vx vy n 0)))
                                     #f)))
                             (else z #f)))
                         (else z #f)))))
               (pair-equiv? (subr heap-use (opair opair) bool)
                 (lambda (x y)
                   (let ((x1 (car x))
                         (y1 (car y))
                         (x2 (cdr x))
                         (y2 (cdr y)))
                     (cond ((done? x y pdone)
                            #t)
                           ((obj-eqv? x1 y1)
                            (begin (equate! x y pdone)
                                   (equiv? x2 y2)))
                           ((obj-eqv? x2 y2)
                            (begin (equate! x y pdone)
                                   (equiv? x1 y1)))
                           ((easy? x1 y1)
                            #f)
                           ((easy? x2 y2)
                            #f)
                           (else
                            (begin (equate! x y pdone)
                                   (and (equiv? x1 y1)
                                        (equiv? x2 y2))))))))
               ;; Like equiv? above, except x and y are known to be vectors,
               ;; n is the length of both, and i is the first index that has
               ;; not yet been pushed onto the todo set.
               (vector-equiv? (subr heap-use (ovec ovec int int) bool)
                 (lambda (x y n i)
                   (if (< i n)
                       (let ((xi (array-ref x i))
                             (yi (array-ref y i)))
                         (if (easy? xi yi)
                             (if (obj-eqv? xi yi)
                                 (vector-equiv? x y n (+ i 1))
                                 #f)
                             (and (equiv? xi yi)
                                  (vector-equiv? x y n (+ i 1)))))
                       #t))))
        (equiv? x y)))))

(define* equal? (subr heap-use (obj obj) bool)
  (lambda (x y)
    (let ((result (bounded-equal? x y equal:bound-on-recursion)))
      (if (>= result 0)
          (if (> result 0)
              #t
              (equiv? x y))
          #f))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; The benchmark.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list with n elements, all equal to x.
(define* make-test-list1 (subr (maxeff (alloc @heap) spin) (int obj) obj)
  (lambda (n x)
    (if (zero? n)
        (empty)
        (pr (cons x (make-test-list1 (- n 1) x))))))

;; Returns a list of n lists, each consisting of n x's.
;; The n elements of the outer list are actually the same list.
(define* make-test-tree1 (subr (maxeff (alloc @heap) spin) (int) obj)
  (lambda (n)
    (if (zero? n)
        (empty)
        (make-test-list1 n (make-test-tree1 (- n 1))))))

;; Returns a list of n elements, as returned by the thunk.
(define make-test-list2
  (poly ((e effect))
    (subr (maxeff e (alloc @heap) spin (read (globals empty pr))) (int (subr e () obj)) obj))
  (plambda ((e effect))
    (lambda (n thunk)
      (letrec ((loop (subr (maxeff e (alloc @heap) spin) (int) obj)
                 (lambda (n)
                   (if (zero? n)
                       (empty)
                       (pr (cons (thunk) (loop (- n 1))))))))
        (loop n)))))

;; Returns a balanced tree of height n, with the branching factor
;; at each level equal to the height of the tree at that level.
;; The subtrees do not share structure.
(define* make-test-tree2 (subr (maxeff (alloc @heap) spin) (int) obj)
  (lambda (n)
    (if (zero? n)
        (empty)
        (make-test-list2 n (lambda () (make-test-tree2 (- n 1)))))))

;; Returns an extremely unbalanced tree of height n.
(define* make-test-tree5 (subr (maxeff (alloc @heap) spin) (int) obj)
  (lambda (n)
    (if (zero? n)
        (empty)
        (pr (cons (make-test-tree5 (- n 1))
                  (sym 'a))))))

;; Calls the thunk n times.
(define iterate
  (poly ((e effect)) (subr (maxeff e spin) (int (subr e () bool)) bool))
  (plambda ((e effect))
    (lambda (n thunk)
      (letrec ((loop (subr (maxeff e spin) (int) bool)
                 (lambda (n)
                   (cond ((= n 1)
                          (thunk))
                         ((> n 1)
                          (begin (thunk)
                                 (loop (- n 1))))
                         (else #f)))))
        (loop n)))))

;; A simple circular list is a worst case for R5RS equal?.
(define* equality-benchmark0 (subr heap-use (int) bool)
  (lambda (n)
    (let ((x (obj-vector->list (the ovec (make-array n (sym 'a))))))
      (begin
        (obj-set-cdr! (obj-list-tail x (- n 1)) x)
        (iterate n (lambda () (equal? x (obj-cdr x))))))))

;; DAG with much sharing.
;; 10 is a good parameter for n.
(define* equality-benchmark1 (subr heap-use (int) bool)
  (lambda (n)
    (let ((x (make-test-tree1 n))
          (y (make-test-tree1 n)))
      (iterate n (lambda () (equal? x y))))))

;; Tree with no sharing.
;; 8 is a good parameter for n.
(define* equality-benchmark2 (subr heap-use (int) bool)
  (lambda (n)
    (let ((x (make-test-tree2 n))
          (y (make-test-tree2 n)))
      (iterate n (lambda () (equal? x y))))))

;; Flat vectors.
;; 1000 might be a good parameter for n.
(define* equality-benchmark3 (subr heap-use (int) bool)
  (lambda (n)
    (let* ((x (vec (make-array n (sym 'a))))
           (y (vec (make-array n (sym 'a)))))
      (iterate n (lambda () (equal? x y))))))

;; Shallow lists.
;; 300 might be a good parameter for n.
(define* equality-benchmark4 (subr heap-use (int) bool)
  (lambda (n)
    (let* ((x (obj-vector->list (the ovec (make-array n (make-test-tree2 3)))))
           (y (obj-vector->list (the ovec (make-array n (make-test-tree2 3))))))
      (iterate n (lambda () (equal? x y))))))

;; No sharing, no proper lists,
;; and deep following car chains instead of cdr.
(define* equality-benchmark5 (subr heap-use (int int) bool)
  (lambda (n iterations)
    (let* ((x (make-test-tree5 n))
           (y (make-test-tree5 n)))
      (iterate iterations (lambda () (equal? x y))))))

(define* equality-benchmarks (subr heap-use (int int int int int int) bool)
  (lambda (n0 n1 n2 n3 n4 n5)
    (and (equality-benchmark0 n0)
         (equality-benchmark1 n1)
         (equality-benchmark2 n2)
         (equality-benchmark3 n3)
         (equality-benchmark4 n4)
         (equality-benchmark5 n5 n5))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input0 int 100)
(define input1 int 100)
(define input2 int 8)
(define input3 int 1000)
(define input4 int 2000)
(define input5 int 5000)
(define iterations int 1)

(define* run (subr heap-use (int bool) bool)
  (lambda (i result)
    (if (= i 0)
        result
        (run (- i 1) (equality-benchmarks input0 input1 input2 input3 input4 input5)))))
(run iterations #f)
