;;; Constant lists, nothing writing them (`acyclic`), searched by a small
;;; procedure that calls itself: the search unrolled where the list is
;;; known (`TODO.md` §44), one made by `list`, one by a helper, one by
;;; `cons` onto another, and `nil`; and the answers the same as the
;;; search's.
(define-type syms (listof symbol acyclic))
(define* syms3 (subr (alloc acyclic) (symbol symbol symbol) syms) (lambda (a b c) (list a b c)))
(define* one-of? (subr spin (symbol syms) bool)
  (lambda (t l) (if (null? l) #f (if (symbol=? t (car l)) #t (one-of? t (cdr l))))))
(define k syms (list 'a 'b 'c))
(define k-helper syms (syms3 'p 'q 'r))
(define k-cons syms (cons 'z k))
(define k-none syms nil)
(define* in-k (subr (maxeff spin (read (globals k one-of?))) (symbol) bool)
  (lambda (t) (one-of? t k)))
(define* in-helper (subr (maxeff spin (read (globals k-helper one-of?))) (symbol) bool)
  (lambda (t) (one-of? t k-helper)))
(define* in-cons (subr (maxeff spin (read (globals k-cons one-of?))) (symbol) int)
  (lambda (t) (if (one-of? t k-cons) 1 2)))
(define* in-none (subr (maxeff spin (read (globals k-none one-of?))) (symbol) bool)
  (lambda (t) (one-of? t k-none)))
(define* score (subr (maxeff spin (read (globals in-k in-helper in-cons in-none))) () int)
  (lambda ()
    (if (and (and (in-k 'b) (not (in-k 'q)))
             (and (and (in-helper 'r) (not (in-helper 'a))) (not (in-none 'a))))
        (+ (in-cons 'z) (+ (* 10 (in-cons 'c)) (* 100 (in-cons 'x))))
        -1)))
(score)
