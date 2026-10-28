;;; FX-26 today: three of the four red-black invariants as structural types
;;; (Castagna's example, after Okasaki): the root and leaves are black, and
;;; no red node has a red child. The fourth, equal black height on every
;;; path, is an index, not a regular type.
(define-type rbtree
  (oneof (leaf unit)
         (black (tupof (v int) (l rbtree) (r rbtree)))
         (red (tupof (v int) (l btree) (r btree)))))
(define-type btree
  (oneof (leaf unit) (black (tupof (v int) (l rbtree) (r rbtree)))))
(define-type rtree (oneof (red (tupof (v int) (l btree) (r btree)))))
(define e btree (one leaf #u))
(define r rtree (one red (tup (v 2) (l e) (r e))))
(define t btree (one black (tup (v 1) (l e) (r r))))
(define any rbtree t)
(define also rbtree r)
