;;; Bacon, Cheng and Rajan's unified theory, in miniature: one equation
;;; over a heap graph, solved twice. An object is live if a root refers
;;; to it or a live object does. Tracing finds the least solution: from
;;; nothing, along edges from what the roots reach. Reference counting
;;; finds the greatest: from every object's count, freeing what reaches
;;; zero and decrementing its successors. They differ by the garbage
;;; cycles. Both are `spin`, for the reasons lattice-fixpoint.fx gives.
(define-type graph (arrayof (listof int acyclic) const))
(define-type nodes (listof int acyclic))
;; The objects whose mark is set, in order.
(define marked (subr pure ((arrayof bool const)) nodes)
  (lambda (a)
    (letrec ((go (subr pure (int nodes) nodes)
               (lambda (i acc) (if (< i 0) acc (go (- i 1) (if (array-ref a i) (cons i acc) acc))))))
      (go (- (array-length a) 1) (list)))))
;; Tracing: the least fixpoint, by a depth-first mark from the roots.
(define trace (subr spin (graph nodes) (arrayof bool const))
  (lambda (g roots)
    (letfreeze r
      (let ((live (the (arrayof bool r) (make-array (array-length g) #f))))
        (letrec ((mark (subr (maxeff (read r) (write r) spin) (nodes) unit)
                   (lambda (vs)
                     (cond ((null? vs) #u)
                           ((array-ref live (car vs)) (mark (cdr vs)))
                           (else (begin (array-set! live (car vs) #t)
                                        (mark (array-ref g (car vs)))
                                        (mark (cdr vs))))))))
          (begin (mark roots) live))))))
;; Reference counting: the greatest fixpoint. Counts start at each
;; object's references, from roots and from every other object, live or
;; not; an object whose count is zero is freed, and its successors
;; decremented, until no count reaches zero. What is kept is every
;; object with a count above zero.
(define count (subr spin (graph nodes) (arrayof bool const))
  (lambda (g roots)
    (letfreeze r
      (let ((n (array-length g)))
        (let ((rc (the (arrayof int r) (make-array n 0)))
              (kept (the (arrayof bool r) (make-array n #t))))
          (letrec ((inc (subr (maxeff (read r) (write r) spin) (nodes) unit)
                     (lambda (vs) (if (null? vs) #u
                                      (begin (array-set! rc (car vs) (+ 1 (array-ref rc (car vs)))) (inc (cdr vs))))))
                   (inc-all (subr (maxeff (read r) (write r) spin) (int) unit)
                     (lambda (v) (if (= v n) #u (begin (inc (array-ref g v)) (inc-all (+ v 1))))))
                   ;; Free `v`: decrement its successors, freeing each that
                   ;; reaches zero (the cascade: Kahn's peeling, stopped
                   ;; by a cycle).
                   (free (subr (maxeff (read r) (write r) spin) (int) unit)
                     (lambda (v) (begin (array-set! kept v #f) (dec (array-ref g v)))))
                   (dec (subr (maxeff (read r) (write r) spin) (nodes) unit)
                     (lambda (vs)
                       (if (null? vs) #u
                           (let ((u (car vs)))
                             (begin (array-set! rc u (- (array-ref rc u) 1))
                                    (if (and (= (array-ref rc u) 0) (array-ref kept u)) (free u) #u)
                                    (dec (cdr vs)))))))
                   (sweep (subr (maxeff (read r) (write r) spin) (int) unit)
                     (lambda (v)
                       (if (= v n) #u
                           (begin (if (and (= (array-ref rc v) 0) (array-ref kept v)) (free v) #u)
                                  (sweep (+ v 1)))))))
            (begin (inc roots) (inc-all 0) (sweep 0) kept)))))))
;; Root 0. 0 -> 1 -> 2 is live. 3 -> 4 -> 1 is garbage with no cycle,
;; pointing into the live part. 5 <-> 6 is a garbage cycle.
(define heap graph
  (letfreeze r
    (let ((a (the (arrayof nodes r) (make-array 7 (list)))))
      (begin (array-set! a 0 (list 1)) (array-set! a 1 (list 2)) (array-set! a 3 (list 4))
             (array-set! a 4 (list 1)) (array-set! a 5 (list 6)) (array-set! a 6 (list 5)) a))))
(define roots nodes (list 0))
;; What each keeps: tracing (0 1 2); counting (0 1 2 5 6), the cycle too.
(list (marked (trace heap roots)) (marked (count heap roots)))
