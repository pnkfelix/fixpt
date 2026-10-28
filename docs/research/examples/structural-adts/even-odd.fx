;;; FX-26 today: datasort refinements (Freeman and Pfenning's `rectype`) are
;;; structural sums, nothing more. `even` and `odd` are lists of even and odd
;;; length; each is a subtype of `lst` by width subtyping and equi-recursion,
;;; and `head-odd` needs no `nil` arm, since an `odd` has no `nil` tag.
(define-type lst  (oneof (nil unit) (cons (tupof (hd int) (tl lst)))))
(define-type even (oneof (nil unit) (cons (tupof (hd int) (tl odd)))))
(define-type odd  (oneof (cons (tupof (hd int) (tl even)))))
(define e2 even (one cons (tup (hd 1) (tl (one cons (tup (hd 2) (tl (one nil #u))))))))
(define as-list lst e2)                       ; forgetting the refinement costs nothing
(define len (subr pure (lst) int)
  (letrec ((len (subr pure (lst) int)
             (lambda (l) (tagcase l (nil u 0) (cons (hd tl) (+ 1 (len tl)))))))
    len))
(define head-odd (subr pure (odd) int)
  (lambda (l) (tagcase l (cons (hd tl) hd))))
(define o1 odd (one cons (tup (hd 7) (tl (one nil #u)))))
(+ (len e2) (head-odd o1))
