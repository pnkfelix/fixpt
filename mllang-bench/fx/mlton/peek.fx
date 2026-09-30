;;; PEEK -- property lists: a list of exception values in a ref, each
;;; property a fresh exception constructor, found again by walking the list.
;;;
;;; Written by Stephen Weeks (sweeks@sweeks.com).
;;; From MLton's benchmark suite (benchmark/tests/peek.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): (doit 1), each 10000000 rounds of 8 peeks.
;;; Answer: (640000000 580000000), the sums n1 and n2 (the original checks
;;; for them), as a list.
;;;
;;; Changed: SML's `exn` is an extensible sum, and `Plist.addPeek` makes a
;;; fresh exception constructor `E of 'a` each time it is called, which is
;;; what makes a property list heterogeneous. FX-26 has no extensible sum,
;;; so an exception value here is `(E key value)`: `key` a fresh integer
;;; from a counter, standing for the constructor's identity, which is what
;;; `peek`'s match `E x :: _` compares; `value` an int, since every
;;; property in the benchmark holds one (Int32 and Int64 both become int).
;;; valOf of NONE never happens here; it would raise Option, and here gives 0.

(define-datatype exn (E int int))
(define-datatype option (NONE) (SOME int))

(define-type plist (ref (listof exn @h) @h))
(define-type adder (subr (maxeff (read @h) (write @h) (alloc @h) (read (globals E))) (plist int) unit))
(define-type peeker (subr (maxeff (read @h) spin (read (globals NONE SOME))) (plist) option))

(define plist-new (subr (alloc @h) () plist) (lambda () (new nil)))

;; The next fresh constructor's identity.
(define next-key (ref int @k) (new 0))

(define add-peek (subr (maxeff (read @k) (write @k) (read (globals next-key))) ()
                       (productof (add adder) (peek peeker)))
  (lambda ()
    (let ((key (get next-key)))
      (begin
        (set next-key (+ key 1))
        (product
          (add (lambda ((r plist) (x int)) (set r (cons (E key x) (get r)))))
          (peek (lambda ((r plist))
                  (letrec ((loop (subr (maxeff (read @h) spin (read (globals NONE SOME))) ((listof exn @h)) option)
                             (lambda (l)
                               (if (null? l)
                                   (NONE)
                                   (tagcase (car l)
                                     (E (k x) (if (= k key) (SOME x) (loop (cdr l)))))))))
                    (loop (get r))))))))))

(define val-of (subr pure (option) int)
  (lambda (o) (tagcase o (NONE () 0) (SOME (x) x))))

;; An input, where no compiler can fold it: a global, which a later
;; definition may replace. The original's loop count.
(define rounds int 10000000)

(define* inner (subr (maxeff (read @h) (write @h) (alloc @h) (read @k) (write @k) spin)
                    ()
                    (listof int @h))
  (lambda ()
    (let* ((l1 (plist-new))
           (l2 (plist-new))
           (a (add-peek)) (b (add-peek)) (c (add-peek)) (d (add-peek))
           (add-a (extract a add)) (peek-a (extract a peek))
           (add-b (extract b add)) (peek-b (extract b peek))
           (add-c (extract c add)) (peek-c (extract c peek))
           (add-d (extract d add)) (peek-d (extract d peek)))
      (begin
        (add-a l1 13)
        (add-b l1 15)
        (add-c l1 17)
        (add-d l1 19)
        (add-a l2 19)
        (add-b l2 17)
        (add-c l2 15)
        (add-d l2 13)
        (letrec ((peek (subr (maxeff (read @h) spin (read (globals NONE SOME val-of))) (plist) int)
                   (lambda (l)
                     (+ (+ (+ (val-of (peek-a l1)) (val-of (peek-b l)))
                           (val-of (peek-c l)))
                        (val-of (peek-d l)))))
                 (loop (subr (maxeff (read @h) (alloc @h) spin (read (globals NONE SOME val-of))) (int int int) (listof int @h))
                   (lambda (i ac1 ac2)
                     (if (= i 0)
                         (list ac1 ac2)
                         (loop (- i 1) (+ ac1 (peek l1)) (+ ac2 (peek l2)))))))
          (loop rounds 0 0))))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 1)

(define* doit (subr (maxeff (read @h) (write @h) (alloc @h) (read @k) (write @k) spin) (int (listof int @h)) (listof int @h))
  (lambda (i result) (if (= i 0) result (doit (- i 1) (inner)))))
(doit iterations nil)
