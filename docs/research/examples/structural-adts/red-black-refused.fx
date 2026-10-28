;;; Refused: a red node with a red child is no `rbtree`.
(define-type rbtree
  (oneof (leaf unit)
         (black (tupof (v int) (l rbtree) (r rbtree)))
         (red (tupof (v int) (l btree) (r btree)))))
(define-type btree
  (oneof (leaf unit) (black (tupof (v int) (l rbtree) (r rbtree)))))
(define e btree (one leaf #u))
(define bad rbtree (one red (tup (v 1) (l e) (r (one red (tup (v 2) (l e) (r e)))))))
