;;; Identity (PLAN.md Q5): whether two mutable objects are the same one, of
;;; each kind, and a union-find over pairs whose roots are found by it, with
;;; objects moved by collections between the tests.
(define-type strings (listof string @heap))
(define-type node (pairof int int @uf))
(define-type nodes (arrayof node @uf))
;; What finding a root does: reads and shortens paths, waits for the parents.
(define-effect finds (maxeff (read @uf) (write @uf) (read @heap) spin))
(define* yes-no (subr pure (bool) string) (lambda (b) (if b "yes" "no")))
;; A node's parent: itself, at a root.
(define parent (ref nodes @heap) (new (make-array 0 (cons 0 0))))
(define* root (subr finds (node) node)
  (lambda (x)
    (let ((p (array-ref (get parent) (car x))))
      (if (pair-eq? p x) x (root p)))))
(define* join! (subr finds (node node) unit)
  (lambda (a b)
    (let ((ra (root a)) (rb (root b)))
      (if (pair-eq? ra rb) #u (array-set! (get parent) (car ra) rb)))))
;; Each node's parent, from `i` on, the node itself.
(define* own-parents! (subr finds (nodes int) unit)
  (lambda (nodes i)
    (if (= i (array-length nodes))
        #u
        (begin (array-set! (get parent) i (array-ref nodes i)) (own-parents! nodes (+ i 1))))))
;; Node `i` on joined to node `i mod k`.
(define* link! (subr finds (nodes int int) unit)
  (lambda (nodes k i)
    (if (= i (array-length nodes))
        #u
        (begin (join! (array-ref nodes i) (array-ref nodes (modulo i k)))
               (link! nodes k (+ i 1))))))
;; How many of the nodes from `i` on are roots, and `c`.
(define* count-roots (subr finds (nodes int int) int)
  (lambda (nodes i c)
    (if (= i (array-length nodes))
        c
        (let ((x (array-ref nodes i)))
          (count-roots nodes (+ i 1) (if (pair-eq? (root x) x) (+ c 1) c))))))
(define* fill! (subr (maxeff (write @uf) (alloc @uf) spin) (nodes int) unit)
  (lambda (nodes i)
    (if (= i (array-length nodes))
        #u
        (begin (array-set! nodes i (cons i 0)) (fill! nodes (+ i 1))))))
;; `n` nodes, each `i` joined to `i mod k`: how many roots are left.
(define* roots (subr (maxeff finds (alloc @uf) (write @heap)) (int int) int)
  (lambda (n k)
    (let ((nodes (the nodes (make-array n (cons 0 0)))))
      (begin (fill! nodes 0)
             (set parent (make-array n (cons 0 0)))
             (own-parents! nodes 0)
             (link! nodes k 0)
             (count-roots nodes 0 0)))))
(define* identity
  (subr (maxeff (read @uf) (write @uf) (alloc @uf) (write @heap) (alloc @heap) (read @heap) spin)
        (int) strings)
  (lambda (n)
    (let ((p (the node (cons 1 2))) (q (the node (cons 1 2)))
          (r (the (ref int @heap) (new 1))) (s (the (ref int @heap) (new 1)))
          (a (the (arrayof int @heap) (make-array 2 0))) (c (the (icell int @heap) (make-icell))))
      (list (yes-no (pair-eq? p p)) (yes-no (pair-eq? p q)) (yes-no (pair-eq? p no-pair))
            (yes-no (ref-eq? r r)) (yes-no (ref-eq? r s))
            (yes-no (array-eq? a a)) (yes-no (array-eq? a (make-array 2 0)))
            (yes-no (icell-eq? c c)) (yes-no (icell-eq? c (make-icell)))
            (int->string (roots n 7)) (int->string (roots n 1))))))
(identity 1000)
