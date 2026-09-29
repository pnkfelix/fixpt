;;; A datatype with parameters: a rose tree of any element type, in any
;;; region, here `acyclic`, walked by a pair of procedures, one for a tree
;;; and one for a list of trees, which size-change sees end.
(define-datatype (rose (t type) (r region))
  (leaf t)
  (node (listof (rose t r) r)))
(define-rec
  (total (subr (read @globals) ((rose int acyclic)) int)
    (lambda (x) (tagcase x (leaf (n) n) (node (kids) (total-all kids)))))
  (total-all (subr (read @globals) ((listof (rose int acyclic) acyclic)) int)
    (lambda (ks) (if (null? ks) 0 (+ (total (car ks)) (total-all (cdr ks)))))))
(define kids (listof (rose int acyclic) acyclic) (list (leaf 1) (leaf 2)))
(total (node kids))
