(define (make-node) (make-vector 4 0))
(define (populate! depth node)
  (if (> depth 0)
      (begin
        (vector-set! node 0 (make-node))
        (vector-set! node 1 (make-node))
        (populate! (- depth 1) (vector-ref node 0))
        (populate! (- depth 1) (vector-ref node 1)))))
(define (make-tree depth)
  (if (<= depth 0)
      (make-node)
      (let ((v (make-node)))
        (vector-set! v 0 (make-tree (- depth 1)))
        (vector-set! v 1 (make-tree (- depth 1)))
        v)))
(define (tree-size depth) (- (expt 2 (+ depth 1)) 1))
(define (count-nodes t)
  (if (vector? t)
      (+ 1 (count-nodes (vector-ref t 0)) (count-nodes (vector-ref t 1)))
      0))

;; `stretch-depth` is defined by the test, which scales it.
(define long-lived-depth (- stretch-depth 2))
(define array-size (* 4 (tree-size long-lived-depth)))
(define half (quotient array-size 2))

;; Stretch the heap with a tree that is dropped immediately.
(make-tree stretch-depth)

;; The data that must survive everything below.
(define long-lived (make-node))
(populate! long-lived-depth long-lived)
(define array (make-vector array-size 0.0))
(do ((i 0 (+ i 1))) ((>= i half))
  (vector-set! array i (/ 1.0 (exact->inexact (+ i 1)))))

;; Churn: transient trees at increasing depths, both ways of building them.
(do ((d 4 (+ d 2))) ((> d long-lived-depth))
  (let ((iters (quotient (* 2 (tree-size stretch-depth)) (tree-size d))))
    (do ((i 0 (+ i 1))) ((>= i iters))
      (populate! d (make-node))
      (make-tree d))))

(list (count-nodes long-lived)
      (vector-length array)
      (= (vector-ref array 0) 1.0)
      (= (vector-ref array (- half 1)) (/ 1.0 (exact->inexact half))))
