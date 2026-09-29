;;; A symbol table: counts of each symbol in a list, then a lookup of three.
(define counts (table symbol int @t) (make-table symbol-hash symbol=?))
(define-effect tallies (maxeff (read @t) (write @t) (alloc @t)))
(define* count-all (subr (maxeff tallies (read @l) spin) ((listof symbol @l)) unit)
  (lambda (xs)
    (if (null? xs)
        #u
        (begin (table-set! counts (car xs) (+ 1 (table-ref counts (car xs) 0)))
               (count-all (cdr xs))))))
;; cons-chain: count-all takes a list in @l
(count-all (cons 'a (cons 'b (cons 'a (cons 'c (cons 'a nil))))))
(let ((a (table-ref counts 'a 0))
      (z (table-ref counts 'z 0)))
  (list a z (table-count counts)))
