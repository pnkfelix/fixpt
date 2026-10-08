;;; The type tests of datums, which register code does in machine code, on
;;; one datum of each kind: a fixnum, a character, both booleans, a short
;;; string, a long one (a large object), a symbol, a pair, the empty list,
;;; a vector and a bytevector. Each datum gives five bits; and symbols'
;;; hashes, which register code reads from the symbol.
(define* doubled (subr spin (string int) string)
  (lambda (s n) (if (= n 0) s (doubled (string-append s s) (- n 1)))))
(define bit (subr pure (bool int) int) (lambda (b v) (if b v 0)))
(define* kinds (subr pure (datum) int)
  (lambda (d)
    (+ (bit (datum-int? d) 1)
       (+ (bit (char? d) 2)
          (+ (bit (bool? d) 4) (+ (bit (string? d) 8) (bit (symbol? d) 16)))))))
(define* all (subr spin (datum int) int)
  (lambda (ds acc)
    (if (null? ds) acc (all (cdr ds) (+ (* acc 32) (kinds (car ds)))))))
(define none datum nil)
(define* some (subr spin () datum)
  (lambda ()
    (cons 7
     (cons #\a
      (cons #t
       (cons #f
        (cons "abc"
         (cons (doubled "x" 17)
          (cons 'abc
           (cons (cons 1 none)
            (cons none
             (cons (datum-list->vector (cons 1 none))
              none))))))))))))
(define same-hash (subr pure () bool)
  (lambda ()
    (let ((abc (symbol-name-hash 'abc)))
      (and (= abc (symbol-name-hash 'abc))
           (not (= abc (symbol-name-hash 'abd)))))))
(if (same-hash) (all (some) 0) -1)
