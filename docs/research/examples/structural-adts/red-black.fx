;;; FX-26 today: three of the four red-black invariants as structural types
;;; (Castagna's example, after Okasaki): the root and leaves are black, and
;;; no red node has a red child. The fourth, equal black height on every
;;; path, is an index, not a regular type.
(define-type rbtree
  (sumof (leaf unit)
         (black (productof (v int) (l rbtree) (r rbtree)))
         (red (productof (v int) (l btree) (r btree)))))
(define-type btree
  (sumof (leaf unit) (black (productof (v int) (l rbtree) (r rbtree)))))
(define-type rtree (sumof (red (productof (v int) (l btree) (r btree)))))
(define e btree (sum leaf #u))
(define r rtree (sum red (product (v 2) (l e) (r e))))
(define t btree (sum black (product (v 1) (l e) (r r))))
(define any rbtree t)
(define also rbtree r)
