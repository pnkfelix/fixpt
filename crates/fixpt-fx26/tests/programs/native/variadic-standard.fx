;;; `append` and `string-append`, standard `vsubr`s as `list` is: called
;;; with any count, the last list shared, not copied; as values, given to
;;; `apply` and passed as any `vsubr` is.
(define-type ints (listof int @heap))
(define* total (subr (maxeff spin (read @heap)) (ints) int)
  (lambda (xs) (if (null? xs) 0 (+ (car xs) (total (cdr xs))))))
(define tail ints (list 7 8))
(define joined ints (append (list 1) (list 2 3) (the ints nil) (list 4 5 6) tail))
;; 0 and 1 lists; the tail itself, shared.
(define-type strings (listof string @heap))
(+ (* 1000 (total joined))
   (+ (if (null? (the ints (append))) 100 0)
      (+ (if (eq? (cdr (cdr (cdr (cdr (cdr (cdr joined)))))) tail) 10 0) (total (append tail)))))
(string-append (string-append) "<" (string-append "a") "|" (string-append "a" "bc" "" "def") ">")
;; As values.
(define join-all (subr (maxeff spin (read @heap) (alloc @heap)) ((listof ints @heap)) ints)
  (lambda (xss) (apply append xss)))
(define say (subr (read @heap) (strings) string) (lambda (ss) (apply string-append ss)))
(define twice (subr pure ((vsubr pure string string) string) string) (lambda (f s) (f s s)))
(total (join-all (list (list 1 2) (the ints nil) (list 3) tail)))
(say (list "x" "y" "z"))
(twice string-append "ab")
