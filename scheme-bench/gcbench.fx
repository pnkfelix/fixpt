;;; GCBENCH -- John Ellis and Pete Kovac's garbage collector benchmark.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/gcbench.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (gcbench 20).
;;; Answer: 0 (Larceny's checker accepts any result; this port's value is 0
;;; when the final sanity check passes, where the original would print
;;; "Failed", and 1 otherwise).
;;;
;;; This is adapted from a benchmark written by John Ellis and Pete Kovac
;;; of Post Communications.
;;; It was modified by Hans Boehm of Silicon Graphics.
;;; It was translated into Scheme by William D Clinger of Northeastern Univ.
;;;
;;;      This is no substitute for real applications.  No actual application
;;;      is likely to behave in exactly this way.  However, this benchmark was
;;;      designed to be more representative of real applications than other
;;;      Java GC benchmarks of which we are aware.
;;;      It attempts to model those properties of allocation requests that
;;;      are important to current GC techniques.
;;;      It is designed to be used either to obtain a single overall performance
;;;      number, or to give a more detailed estimate of how collector
;;;      performance varies with object lifetimes.  It prints the time
;;;      required to allocate and collect balanced binary trees of various
;;;      sizes.  Smaller trees result in shorter object lifetimes.  Each cycle
;;;      allocates roughly the same amount of memory.
;;;      Two data structures are kept around during the entire process, so
;;;      that the measured performance is representative of applications
;;;      that maintain some live in-memory data.  One of these is a tree
;;;      containing many pointers.  The other is a large array containing
;;;      double precision floating point numbers.  Both should be of comparable
;;;      size.
;;;
;;; What the port changed, and why:
;;;
;;; - Nodes. The original's node is a record of four mutable fields, left,
;;;   right, i and j, whose left and right are 0 in an empty node. FX-26 has
;;;   no record type that a 0 (or #f) can stand in for, so a node here is
;;;   three pairs, ((left . right) . (i . j)), and an empty node's children
;;;   are nil. Pairs have no header, so a node is six words, as Larceny's
;;;   record (header, record type, four fields) is; but three objects, not
;;;   one. `(eq? longLivedTree '())` is `null?`.
;;; - The long-lived array. The original fills half of a vector of
;;;   kArraySize elements with the inexact reals 1/(i+1), and checks one of
;;;   them at the end; the reals are ballast, live data for the collector to
;;;   keep, and nothing is computed with them. FX-26 has no floating point,
;;;   and the port does not pretend to: element i holds instead a new
;;;   `(ref int)` of i+1, a small heap object per element as a boxed flonum
;;;   is, and the final check asks whether element n holds n+1. The unfilled
;;;   half shares one object, as it shares the constant 0.0.
;;; - The inner procedures of `gcbench`, which close over its parameters,
;;;   are top-level procedures taking them as arguments; `do` loops are
;;;   recursive procedures; `expt` of 2 is a loop.
;;; - The displays (progress lines, "Failed") are left out: FX-26 has no
;;;   output. The result of the check is the value instead.

(define-type node (pairof (pairof node node @heap) (pairof int int @heap) @heap))

(define make-empty-node (subr (alloc @heap) () node)
  (lambda () (cons (cons (the node no-pair) (the node no-pair)) (cons 0 0))))

(define make-node (subr (alloc @heap) (node node) node)
  (lambda (l r) (cons (cons l r) (cons 0 0))))

(define* expt2 (subr spin (int) int)
  (lambda (n) (if (= n 0) 1 (* 2 (expt2 (- n 1))))))

;;  Nodes used by a tree of a given size
(define* tree-size (subr spin (int) int)
  (lambda (i) (- (expt2 (+ i 1)) 1)))

;;  Number of iterations to use for a given tree depth
(define* num-iters (subr spin (int int) int)
  (lambda (kStretchTreeDepth i)
    (quotient (* 2 (tree-size kStretchTreeDepth)) (tree-size i))))

;;  Build tree top down, assigning to older objects.
(define* populate (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int node) bool)
  (lambda (iDepth thisNode)
    (if (<= iDepth 0)
        #f
        (let ((iDepth (- iDepth 1)))
          (begin
            (set-car! (car thisNode) (make-empty-node))
            (set-cdr! (car thisNode) (make-empty-node))
            (populate iDepth (car (car thisNode)))
            (populate iDepth (cdr (car thisNode))))))))

;;  Build tree bottom-up
(define* make-tree (subr (maxeff (alloc @heap) spin) (int) node)
  (lambda (iDepth)
    (if (<= iDepth 0)
        (make-empty-node)
        (make-node (make-tree (- iDepth 1))
                   (make-tree (- iDepth 1))))))

;; GCBench: Top down construction
(define* top-down (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int int) unit)
  (lambda (i iNumIters depth)
    (if (>= i iNumIters)
        #u
        (begin (populate depth (make-empty-node))
               (top-down (+ i 1) iNumIters depth)))))

;; GCBench: Bottom up construction
(define* bottom-up (subr (maxeff (alloc @heap) spin) (int int int) unit)
  (lambda (i iNumIters depth)
    (if (>= i iNumIters)
        #u
        (begin (make-tree depth)
               (bottom-up (+ i 1) iNumIters depth)))))

(define* time-construction (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) unit)
  (lambda (kStretchTreeDepth depth)
    (let ((iNumIters (num-iters kStretchTreeDepth depth)))
      (begin (top-down 0 iNumIters depth)
             (bottom-up 0 iNumIters depth)))))

(define* construct-all (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int int) unit)
  (lambda (kStretchTreeDepth d kMaxTreeDepth)
    (if (> d kMaxTreeDepth)
        #u
        (begin (time-construction kStretchTreeDepth d)
               (construct-all kStretchTreeDepth (+ d 2) kMaxTreeDepth)))))

;; Fill the first half of the long-lived array.
(define* fill-array (subr (maxeff (write @heap) (alloc @heap) spin) ((arrayof (ref int @heap) @heap) int int) unit)
  (lambda (array i n)
    (if (>= i n)
        #u
        (begin (array-set! array i (new (+ i 1)))
               (fill-array array (+ i 1) n)))))

(define* gcbench (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int) int)
  (lambda (kStretchTreeDepth)
    (let* ((kLongLivedTreeDepth (- kStretchTreeDepth 2))
           (kArraySize (* 4 (tree-size kLongLivedTreeDepth)))
           (kMinTreeDepth 4)
           (kMaxTreeDepth kLongLivedTreeDepth))
      (begin
        ;  Stretch the memory space quickly
        (make-tree kStretchTreeDepth)
        ;  Create a long lived object
        (let ((longLivedTree (make-empty-node)))
          (begin
            (populate kLongLivedTreeDepth longLivedTree)
            ;  Create long-lived array, filling half of it
            (let ((array (the (arrayof (ref int @heap) @heap) (make-array kArraySize (new 0)))))
              (begin
                (fill-array array 0 (quotient kArraySize 2))
                (construct-all kStretchTreeDepth kMinTreeDepth kMaxTreeDepth)
                (if (or (null? longLivedTree)
                        (let* ((m (- (quotient (array-length array) 2) 1))
                               (n (if (< 1000 m) 1000 m)))
                          (not (= (get (array-ref array n)) (+ n 1)))))
                    1
                    0)))))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 20)
(define iterations int 1)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (gcbench input1)))))
(run iterations -1)
