;; => 12
;; A table by identity: two keys, one set twice and the other deleted;
;; what each gives, how many entries are left, and whether the deleted one
;; is there (`evaluator_standard.rs`, the evaluator's tables).
(let ((t ((proj (proj make-eqtable @k @t) (ref int @k) int) ((proj (proj ref-identity @k) int)))))
  (let ((a (the (ref int @k) (new 1))) (b (the (ref int @k) (new 2))))
    (begin (eqtable-set! t a 10) (eqtable-set! t b 20) (eqtable-set! t a 11) (eqtable-delete! t b)
           (+ (+ (eqtable-ref t a 0) (eqtable-ref t b 0))
              (+ (eqtable-count t) (if (eqtable-has? t b) 100 0))))))
