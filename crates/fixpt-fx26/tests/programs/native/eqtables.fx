;;; Tables keyed by identity (PLAN.md Q5), hashed by address: two keys
;;; alike but not the same are two entries; keys found again after their
;;; objects were moved by collections (each round allocates past the
;;; nursery); entries deleted; refs as keys too.
(define-type strings (listof string @heap))
(define-type key (pairof int int @k))
(define-type keys (arrayof key @k))
(define-type counts (eqtable key int @k @t))
(define-effect uses (maxeff (read @t) (write @t) (alloc @t) (read @k) (write @k) (alloc @k) spin))
(define* fill! (subr (maxeff uses) (counts keys int) unit)
  (lambda (t ks i)
    (if (= i (array-length ks))
        #u
        (begin (array-set! ks i (cons (modulo i 10) 0)) (eqtable-set! t (array-ref ks i) i)
               (fill! t ks (+ i 1))))))
;; The sum of each key's value (0 if it has none), for keys `i` on, with
;; garbage made between, so that collections move the keys.
(define* total (subr (maxeff uses) (counts keys int int) int)
  (lambda (t ks i acc)
    (if (= i (array-length ks))
        acc
        (let ((junk (the keys (make-array 64 (array-ref ks i)))))
          (total t ks (+ i 1) (+ acc (eqtable-ref t (array-ref junk 63) 0)))))))
;; Every other key deleted, from `i` on.
(define* thin! (subr (maxeff uses) (counts keys int) unit)
  (lambda (t ks i)
    (if (>= i (array-length ks))
        #u
        (begin (eqtable-delete! t (array-ref ks i)) (thin! t ks (+ i 2))))))
(define* round (subr (maxeff uses (alloc @heap)) (int) strings)
  (lambda (n)
    (let ((t (the counts (make-eqtable (pair-identity))))
          (ks (the keys (make-array n (cons 0 0)))))
      (begin
        (fill! t ks 0)
        (let ((before (total t ks 0 0)))
          (begin
            (thin! t ks 0)
            (list (int->string (eqtable-count t)) (int->string before)
                  (int->string (total t ks 0 0))
                  (if (eqtable-has? t (cons 1 0)) "found a copy" "not a copy")
                  (if (eqtable-has? t (array-ref ks 1)) "has 1" "lost 1")
                  (if (eqtable-has? t (array-ref ks 0)) "kept 0" "deleted 0"))))))))
(define* refs (subr (maxeff (write @r) (alloc @r) (read @t) (write @t) (alloc @t)) () int)
  (lambda ()
    (let ((t (the (eqtable (ref int @r) int @r @t) (make-eqtable (ref-identity))))
          (a (the (ref int @r) (new 1))) (b (the (ref int @r) (new 1))))
      (begin (eqtable-set! t a 10) (eqtable-set! t b 20) (eqtable-set! t a 30)
             (+ (eqtable-ref t a 0) (eqtable-ref t b 0))))))
(define* eqtables (subr (maxeff uses (write @r) (alloc @r) (alloc @heap)) (int) strings)
  (lambda (n) (cons (int->string (refs)) (round n))))
(eqtables 20000)
