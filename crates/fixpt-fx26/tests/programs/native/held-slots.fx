;;; A slot written, then read again in the same straight-line code, while a
;;; register still holds it (TODO.md §121): the first of some facts at a
;;; place, its fields each read from the head, a list's `car` kept in a slot.
(define-datatype fact (fact string i64 string))
(define-type facts (listof fact @heap))
(define* first-fact (subr (maxeff (read @heap) spin) (facts string i64 string) string)
  (lambda (fs file pos what)
    (if (null? fs)
        ""
        (tagcase (car fs)
          (fact (ff fp fw)
            (if (and (i64= fp pos) (string=? ff file) (string=? fw what))
                fw
                (first-fact (cdr fs) file pos what)))))))
(define* held-slots (subr (maxeff (alloc @heap) (read @heap) spin) (int) int)
  (lambda (n)
    (let ((fs (the facts (list (fact "a" (int->i64 1) "x") (fact "b" (int->i64 n) "y")
                               (fact "b" (int->i64 n) "z")))))
      (string-length (string-append (first-fact fs "b" (int->i64 n) "z")
                                    (first-fact fs "b" (int->i64 2) "z"))))))
(held-slots 1000)
