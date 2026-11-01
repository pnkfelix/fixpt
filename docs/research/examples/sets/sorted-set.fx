;;; A set of ints as a sorted, finite list: the value semantics SETL
;;; wanted, as a library. Membership, union and adjoin are `pure`, since
;;; the lists are `acyclic` (frozen, finite) and built in order. Each
;;; recursion is a local `letrec`, so that no global reaches itself.
(define-type iset (listof int acyclic))
(define member? (subr pure (int iset) bool)
  (lambda (x s)
    (letrec ((go (subr pure (iset) bool)
               (lambda (s)
                 (cond ((null? s) #f)
                       ((= x (car s)) #t)
                       ((< x (car s)) #f)
                       (else (go (cdr s)))))))
      (go s))))
(define adjoin (subr pure (int iset) iset)
  (lambda (x s)
    (letrec ((go (subr pure (iset) iset)
               (lambda (s)
                 (cond ((null? s) (cons x s))
                       ((= x (car s)) s)
                       ((< x (car s)) (cons x s))
                       (else (cons (car s) (go (cdr s))))))))
      (go s))))
(define union (subr pure (iset iset) iset)
  (lambda (s t)
    (letrec ((go (subr pure (iset iset) iset)
               (lambda (s t)
                 (cond ((null? s) t)
                       ((null? t) s)
                       ((= (car s) (car t)) (cons (car s) (go (cdr s) (cdr t))))
                       ((< (car s) (car t)) (cons (car s) (go (cdr s) t)))
                       (else (cons (car t) (go s (cdr t))))))))
      (go s t))))
;; Built imperatively, used as a value: the accumulator is a ref at a
;; region the body masks, so `squares-below` is `pure` but for `spin`
;; (its loop is bounded by `n`, which size-change cannot see) and its
;; reads of `adjoin` (Clojure's transient / persistent!, checked by the
;; types instead of at run time).
(define squares-below (subr (maxeff spin (read (globals adjoin))) (int) iset)
  (lambda (n)
    (letregion r
      (let ((acc (the (ref iset r) (new (the iset (list))))))
        (letrec ((go (subr (maxeff (read r) (write r) spin (read (globals adjoin))) (int) unit)
                   (lambda (i)
                     (if (< (* i i) n)
                         (begin (set acc (adjoin (* i i) (get acc))) (go (+ i 1)))
                         #u))))
          (begin (go 0) (get acc)))))))
(define s iset (union (squares-below 50) (list 2 3 5 7)))
;; The set itself if 49 is in it and 6 is not, else the empty set.
(if (and (member? 49 s) (not (member? 6 s))) s (the iset (list)))
