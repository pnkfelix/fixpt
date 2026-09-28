;;; A symbol table: counts of each symbol in a list, then a lookup of three.
(define counts (table symbol int @t) (make-table symbol-hash symbol=?))
(define* count-all (subr (maxeff (read @t) (write @t) (alloc @t) (read @l) spin) ((listof symbol @l)) unit)
  (lambda (xs)
    (if (null? xs)
        #u
        (begin (table-set! counts (car xs) (+ 1 (table-ref counts (car xs) 0)))
               (count-all (cdr xs))))))
(count-all (cons 'a (cons 'b (cons 'a (cons 'c (cons 'a nil))))))
(the (listof int @o) (cons (table-ref counts 'a 0) (cons (table-ref counts 'z 0) (cons (table-count counts) nil))))
