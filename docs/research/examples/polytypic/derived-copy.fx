;;; The contrast: what `(derive tree equal ->datum)` would write (proposed
;;; form; this is its output, by hand). A copy per type, walking the type
;;; directly: no view, no dictionary, and pure, since each is one local
;;; group that size-change sees descend.
(define-datatype tree (leaf int) (node tree tree))
(define tree=? (subr pure (tree tree) bool)
  (letrec ((eq (subr pure (tree tree) bool)
             (lambda (x y)
               (tagcase x
                 (leaf (n) (tagcase y (leaf (m) (= n m)) (else _ #f)))
                 (node (l r) (tagcase y (node (l2 r2) (and (eq l l2) (eq r r2))) (else _ #f)))))))
    eq))
(define tree->datum (subr pure (tree) datum)
  (let ((end nil))     ; the empty list
    (letrec ((show (subr pure (tree) datum)
               (lambda (x)
                 (tagcase x
                   (leaf (n) (cons 'leaf (cons n end)))
                   (node (l r) (cons 'node
                                     (cons (show l) (cons (show r) end))))))))
      show)))
;; A family: the parameter's operation is an argument (the one place a
;; dictionary appears), the walk itself is still a copy per family.
(define-datatype (ptree (t type)) (pleaf t) (pnode (ptree t) (ptree t)))
(define ptree=?
  (poly ((t type) (e effect)) (subr e ((subr e (t t) bool) (ptree t) (ptree t)) bool))
  (lambda (elt x y)
    (letrec ((eq (subr e ((ptree t) (ptree t)) bool)
               (lambda (x y)
                 (tagcase x
                   (pleaf (a) (tagcase y (pleaf (b) (elt a b)) (else _ #f)))
                   (pnode (l r) (tagcase y
                                  (pnode (l2 r2) (and (eq l l2) (eq r r2)))
                                  (else _ #f)))))))
      (eq x y))))

(define t1 tree (node (leaf 1) (node (leaf 2) (leaf 3))))
(tree=? t1 t1)
(tree->datum t1)
;; FX-26 has no bool=? yet (P0), so the element equality is written out.
(define bool=? (subr pure (bool bool) bool) (lambda (a b) (if a b (not b))))
(ptree=? bool=? (pnode (pleaf #t) (pleaf #f)) (pnode (pleaf #t) (pleaf #t)))
