;;; A symbol table: counts of each symbol in a list, then a lookup of three.
(define counts (table symbol int @t) (make-table symbol-hash symbol=?))
(define-effect tallies (maxeff (read @t) (write @t) (alloc @t)))
(define* count-all (subr (maxeff tallies (read @l) spin) ((listof symbol @l)) unit)
  (lambda (xs)
    (if (null? xs)
        #u
        (begin (table-set! counts (car xs) (+ 1 (table-ref counts (car xs) 0)))
               (count-all (cdr xs))))))
(count-all (list 'a 'b 'a 'c 'a))
(let ((a (table-ref counts 'a 0))
      (z (table-ref counts 'z 0)))
  (list a z (table-count counts)))
