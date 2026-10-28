; Accepted: frozen data is covariant in the order of lifetimes (Kayak's,
; 2026-10-28): data built in a place, frozen as it is made, `(acyclic p)`,
; may point into frozen data that outlives the place, the heap's; and a
; place's frozen data fits where an inner place's is expected.
(define heap-list (listof int acyclic) (list 1 2 3))
;; Consed straight into a frozen place region onto the heap's list.
(define* push
  (poly ((p place)) (subr (alloc p) ((place p) (listof int acyclic)) (listof int (acyclic p))))
  (plambda ((p place)) (lambda (pl xs) (rcons pl 5 xs))))
;; A walk of such a list: no `spin`, its parts smaller.
(define* total (poly ((p place)) (subr (read (acyclic p)) ((listof int (acyclic p))) int))
  (plambda ((p place))
    (lambda (xs)
      (letrec ((go (subr (read (acyclic p)) ((listof int (acyclic p))) int)
                 (lambda (ys) (if (null? ys) 0 (+ (car ys) (go (cdr ys)))))))
        (go xs)))))
(letrena p ((proj total p) ((proj push p) p heap-list)))
;; `(const p)` where `(acyclic p)` is had; the heap's `const` list too.
(letrena p (let ((xs (the (listof int (const p)) (rcons p 5 heap-list)))) 0))
;; A datatype whose field is at its region: the heap's inside a place's.
(define-datatype (tr (r region)) (leaf) (node (listof int r) (tr r)))
(define heap-tree (tr acyclic) (node heap-list (leaf)))
(letrena p
  (let ((t (the (tr (acyclic p)) (node ((proj push p) p heap-list) heap-tree))))
    (tagcase t (node (xs rest) ((proj total p) xs)) (else y 0))))
;; An outer place's frozen data in an inner place's.
(letrena p
  (let ((outer (the (listof int (acyclic p)) (rcons p 1 heap-list))))
    (letrena q (let ((inner (the (listof int (acyclic q)) (rcons q 2 outer)))) 0))))
