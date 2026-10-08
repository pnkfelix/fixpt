;;; Hash tables' types, in FX-26: a table, its buckets and entries, and its
;;; key's hash and equality, generic in the key, the value and the region.
;;; A module file of no state, which `table.fx` loads, and so may its
;;; clients (`TODO.md` §68).

(define-type (bucket (k type) (v type) (r region)) (listof (pairof k v r) acyclic))
(define-type (bucket-array (k type) (v type) (r region)) (arrayof (bucket k v r) r))
;; A key's entry, or none: `nil`.
(define-type (entry (k type) (v type) (r region)) (union nil (pairof k v r)))
;; A key's hash, and whether two keys are the same.
(define-type (key-hash (k type)) (subr pure (k) int))
(define-type (key-same (k type)) (subr pure (k k) bool))
(define-type (table (k type) (v type) (r region))
  (bloblet (fields (key-hash k) (key-same k) (bucket-array k v r) int) r))

;; Rehashing: moving the entries of an `a` into new buckets, as `b` says,
;; reading, writing and consing in the table's region.
(define-type (rehashing (k type) (v type) (r region) (a type) (b type))
  (subr (maxeff (read @globals) (read r) (write r) (alloc r)) ((table k v r) a b) unit))

;;; ------------------------------------------------------------ signatures

;; What clients use of the `tables` module (`table.fx`, `TODO.md` §68): the
;; evaluator's.
(define-type tables-sig
  (moduleof
   (val std-nil-name? (subr pure (string) bool))
   (val symbol-hash (subr pure (symbol) int))
   (val make-table
        (poly ((r region)) (poly ((k type) (v type))
          (subr (alloc r) ((key-hash k) (key-same k)) (table k v r)))))
   (val table-ref
        (poly ((r region)) (poly ((k type) (v type))
          (subr (maxeff (read @globals) (read r)) ((table k v r) k v) v))))
   (val table-set!
        (poly ((r region)) (poly ((k type) (v type))
          (subr (maxeff (read @globals) (read r) (write r) (alloc r)) ((table k v r) k v) unit))))))
