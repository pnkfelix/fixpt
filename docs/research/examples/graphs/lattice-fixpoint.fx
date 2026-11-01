;;; A "fold" over a cyclic graph as equations solved as a least fixpoint:
;;; x_v = f(v, x_u for each successor u), iterated from bottom until
;;; nothing changes (Kildall; Datalog; Pregel's supersteps). The lattice
;;; is a dictionary: bottom, join and equality. Termination needs the
;;; lattice to be of finite height and the step to be monotone, which no
;;; type here says, so the solver is `spin`.
(define-type graph (arrayof (listof int acyclic) const))
(define-type (lattice (t type))
  (productof (bottom t) (join (subr pure (t t) t)) (same (subr pure (t t) bool))))
(define solve
  (poly ((t type))
    (subr spin ((lattice t) graph (subr pure (int (listof t acyclic)) t)) (arrayof t const)))
  (lambda (l g step)
    (letfreeze r
      (let ((x (the (arrayof t r) (make-array (array-length g) (extract l bottom)))))
        (letrec ((succs (subr (read r) ((listof int acyclic)) (listof t acyclic))
                   (lambda (us) (if (null? us) (list) (cons (array-ref x (car us)) (succs (cdr us)))))))
         (letrec (;; One sweep over every node; whether anything changed.
                 (sweep (subr (maxeff (read r) (write r) spin) (int bool) bool)
                   (lambda (v changed)
                     (if (= v (array-length g))
                         changed
                         (let* ((old (array-ref x v))
                                (new ((extract l join) old (step v (succs (array-ref g v))))))
                           (if ((extract l same) old new)
                               (sweep (+ v 1) changed)
                               (begin (array-set! x v new) (sweep (+ v 1) #t)))))))
                 (loop (subr (maxeff (read r) (write r) spin) () unit)
                   (lambda () (if (sweep 0 #f) (loop) #u))))
          (begin (loop) x)))))))
;; Which nodes reach node 3? A node reaches 3 if it is 3 or a successor
;; does: the lattice of booleans under `or`, bottom #f.
(define bools (lattice bool)
  (product (bottom #f) (join (lambda (a b) (or a b))) (same (lambda (a b) (eq? a b)))))
(define reaches-3 (subr pure (int (listof bool acyclic)) bool)
  (lambda (v xs)
    (letrec ((any (subr pure ((listof bool acyclic)) bool)
               (lambda (xs) (and (not (null? xs)) (or (car xs) (any (cdr xs)))))))
      (or (= v 3) (any xs)))))
;; As in dfs-forest.fx: 0 -> 1 -> 2 -> 0, 1 -> 3, 4 -> 3, and 5 alone.
(define g graph
  (letfreeze r
    (let ((a (the (arrayof (listof int acyclic) r) (make-array 6 (list)))))
      (begin (array-set! a 0 (list 1)) (array-set! a 1 (list 2 3)) (array-set! a 2 (list 0))
             (array-set! a 4 (list 3)) a))))
(array->list ((proj solve bool) bools g reaches-3))
