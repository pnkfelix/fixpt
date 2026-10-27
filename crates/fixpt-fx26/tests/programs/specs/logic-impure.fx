; Refused
;;; A procedure a specification calls must be `pure`: one that reads a
;;; region is not a function of its arguments alone.
(define-type ints (listof int @heap))
(define first-pos? (subr (read @heap) (ints) bool) (lambda (xs) (and (pair? xs) (< 0 (car xs)))))
(define f (subr pure ((xs : ints)) ints (ensures r (first-pos? r))) (lambda (xs) xs))
