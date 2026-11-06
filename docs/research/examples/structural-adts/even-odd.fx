;;; FX-26 today: datasort refinements (Freeman and Pfenning's `rectype`) are
;;; structural sums, nothing more. `even` and `odd` are lists of even and odd
;;; length; each is a subtype of `lst` by width subtyping and equi-recursion,
;;; and `head-odd` needs no `nil` arm, since an `odd` has no `nil` tag.
(define-type lst  (sumof (nil unit) (cons (tupleof int lst))))
(define-type even (sumof (nil unit) (cons (tupleof int odd))))
(define-type odd  (sumof (cons (tupleof int even))))
(define e2 even (sum cons (tuple 1 (sum cons (tuple 2 (sum nil #u))))))
(define as-list lst e2)                       ; forgetting the refinement costs nothing
(define len (subr pure (lst) int)
  (letrec ((len (subr pure (lst) int)
             (lambda (l) (tagcase l (nil u 0) (cons (hd tl) (+ 1 (len tl)))))))
    len))
(define head-odd (subr pure (odd) int)
  (lambda (l) (tagcase l (cons (hd tl) hd))))
(define o1 odd (sum cons (tuple 7 (sum nil #u))))
(+ (len e2) (head-odd o1))
