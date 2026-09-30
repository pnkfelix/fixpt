;;; Refused: a red node with a red child is no `rbtree`.
(define-type rbtree
  (sumof (leaf unit)
         (black (productof (v int) (l rbtree) (r rbtree)))
         (red (productof (v int) (l btree) (r btree)))))
(define-type btree
  (sumof (leaf unit) (black (productof (v int) (l rbtree) (r rbtree)))))
(define e btree (sum leaf #u))
(define bad rbtree (sum red (product (v 1) (l e) (r (sum red (product (v 2) (l e) (r e)))))))
