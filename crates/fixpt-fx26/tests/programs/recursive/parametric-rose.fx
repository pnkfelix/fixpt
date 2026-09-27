;;; A datatype with parameters: a rose tree of any element type, in any
;;; region, here `finite`, walked by a pair of procedures, one for a tree
;;; and one for a list of trees, which size-change sees end.
(define-datatype (rose (t type) (r region))
  (leaf t)
  (node (listof (rose t r) r)))
(define-rec
  (total (subr pure ((rose int finite)) int)
    (lambda (x) (tagcase x (leaf (n) n) (node (kids) (total-all kids)))))
  (total-all (subr pure ((listof (rose int finite) finite)) int)
    (lambda (ks) (if (null? ks) 0 (+ (total (car ks)) (total-all (cdr ks)))))))
(define kids (listof (rose int finite) finite) (cons (leaf 1) (cons (leaf 2) nil)))
(total (node kids))
