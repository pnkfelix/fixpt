;;; King and Launchbury's idea: depth-first search makes a spanning
;;; forest, an ordinary finite tree, and graph algorithms are folds over
;;; it. The graph is a frozen array of successor lists, which may have
;;; cycles. The visited set is an array at a region the search masks, so
;;; the search is `pure` but for `spin`: it ends because each node is
;;; visited once, which size-change cannot see.
(define-type graph (arrayof (listof int acyclic) const))
(define-datatype rose (rnode int (listof rose acyclic)))
(define-type forest (listof rose acyclic))
(define dfs (subr (maxeff spin (read (globals rnode))) (graph (listof int acyclic)) forest)
  (lambda (g roots)
    (letregion r
      (let ((seen (the (arrayof bool r) (make-array (array-length g) #f))))
        (letrec ((visit (subr (maxeff (read r) (write r) spin) ((listof int acyclic)) forest)
                   (lambda (vs)
                     (cond ((null? vs) (list))
                           ((array-ref seen (car vs)) (visit (cdr vs)))
                           (else
                            (begin
                              (array-set! seen (car vs) #t)
                              (let ((kids (visit (array-ref g (car vs)))))
                                (cons (rnode (car vs) kids) (visit (cdr vs))))))))))
          (visit roots))))))
;; A fold over the forest: its reverse postorder, which is a topological
;; order where the graph has no cycle. It walks a finite tree, so it
;; does not say `spin`.
(define reverse-postorder (subr pure (forest (listof int acyclic)) (listof int acyclic))
  (lambda (f acc)
    (letrec ((trees (subr pure (forest (listof int acyclic)) (listof int acyclic))
               (lambda (f acc)
                 (if (null? f)
                     acc
                     (trees (cdr f) (tree (car f) acc)))))
             (tree (subr pure (rose (listof int acyclic)) (listof int acyclic))
               (lambda (t acc)
                 (tagcase t
                   (rnode (v kids) (cons v (trees kids acc)))))))
      (trees f acc))))
;; 0 -> 1 -> 2 -> 0 (a cycle), 1 -> 3, 4 -> 3; node 5 unreached from 0.
(define g graph
  (letfreeze r
    (let ((a (the (arrayof (listof int acyclic) r) (make-array 6 (list)))))
      (begin (array-set! a 0 (list 1)) (array-set! a 1 (list 2 3)) (array-set! a 2 (list 0))
             (array-set! a 4 (list 3)) a))))
(define f forest (dfs g (list 0 4 5)))
(reverse-postorder f (list))
