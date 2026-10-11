;; ! carries a (blobref o (productof (x i32) (y i32))), which cannot be taken apart
;; An arm on a flat sum binds one name, a blobref to its variant: no bytes
;; are copied out.
(define-type o (bloblet (fields symbol) @b))
(define b o (make-bloblet 16 'p))
(define r (blobref o (sumof (p (productof (x i32) (y i32))))) (blobref-at b 0))
(tagcase r (p (x y) 0))
