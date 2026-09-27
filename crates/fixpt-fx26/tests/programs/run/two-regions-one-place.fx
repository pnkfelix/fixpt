;;; Two regions in one place: a list of nodes and a list of edges, each at a
;;; region of its own, both in one arena. The regions are bound inside the
;;; arena, so they won't outlive it, and `rcons` may put their data there.
(define count (subr pure (int) int)
  (lambda (n)
    (letrena p
      (letregion nodes
        (letregion edges
          (letrec ((build (subr (maxeff (read nodes) (read edges) (alloc nodes) (alloc edges) (alloc p)) (int (listof int nodes) (listof int edges)) int)
                     (lambda (i ns es)
                       (if (= i 0)
                           (+ (car ns) (car es))
                           (build (- i 1) (rcons p i ns) (rcons p (* 2 i) es))))))
            (build n (rcons p 0 nil) (rcons p 0 nil))))))))
(count 5)
