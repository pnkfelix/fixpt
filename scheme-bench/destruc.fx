;;; DESTRUC -- Destructive operation benchmark.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/destruc.scm),
;;; ported to FX-26. Larceny's input: 4000 iterations of (destructive 600 50).
;;; Answer: ((1 1 2) (1 1 1) (1 1 1 2) (1 1 1 1) (1 1 1 1 2) (1 1 1 1 2)
;;;          (1 1 1 1 2) (1 1 1 1 2) (1 1 1 1 2)
;;;          (1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 2 2 2 2 2 3)).
;;;
;;; The inner lists hold '() or integers, so their elements are an `item`:
;;; `none`, one shared value standing for '(), or `(num i)`, which
;;; allocates where Larceny's fixnum does not. The `do` loops
;;; are local `letrec` loops. `length` wants a list the checker knows is
;;; finite, and these are written, so it is `list-length`, written here.
;;; The result is shown as a datum, by `result->datum`, after the benchmark.

(define-datatype item (null-item) (num int))
(define none item (null-item))

(define-type items (listof item @heap))
(define-type rows (listof items @heap))

(define* list-length (subr (maxeff (read @heap) spin) (items) int)
  (lambda (l) (if (null? l) 0 (+ 1 (list-length (cdr l))))))

(define* append-to-tail! (subr (maxeff (read @heap) (write @heap) spin) (items items) items)
  (lambda (x y)
    (if (null? x)
        y
        (letrec ((loop (subr (maxeff (read @heap) (write @heap) spin) (items items) items)
                   (lambda (a b)
                     (if (null? b)
                         (begin
                           (set-cdr! a y)
                           x)
                         (loop b (cdr b))))))
          (loop x (cdr x))))))

(define-effect effs (maxeff (read @heap) (write @heap) (alloc @heap) spin
                          (read (globals none num list-length append-to-tail!))))

(define* destructive (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) rows)
  (lambda (n m)
    (let ((l (letrec ((make-l (subr (maxeff (alloc @heap) spin) (int rows) rows)
                        (lambda (i a) (if (= i 0) a (make-l (- i 1) (cons nil a))))))
               (make-l 10 nil))))
      (letrec ((outer (subr effs (int) rows)
                 (lambda (i)
                   (if (= i 0)
                       l
                       (begin
                         (cond ((null? (car l))
                                (grow l))
                               (else
                                (halve l (cdr l) i)))
                         (outer (- i 1))))))
               ;; the first arm's loop over l
               (grow (subr effs (rows) unit)
                 (lambda (l)
                   (if (null? l)
                       #u
                       (begin
                         (if (null? (car l)) (set-car! l (cons none nil)) #u)
                         (append-to-tail! (car l) (make-m m nil))
                         (grow (cdr l))))))
               (make-m (subr (maxeff (alloc @heap) spin (read (globals none))) (int items) items)
                 (lambda (j a) (if (= j 0) a (make-m (- j 1) (cons none a)))))
               ;; the else arm's loop over l1 and l2
               (halve (subr effs (rows rows int) unit)
                 (lambda (l1 l2 i)
                   (if (null? l2)
                       #u
                       (begin
                         (set-cdr! (skip (quotient (list-length (car l2)) 2) (car l2) i)
                                   (let ((n (quotient (list-length (car l1)) 2)))
                                     (cond ((= n 0)
                                            (begin
                                              (set-car! l1 nil)
                                              (car l1)))
                                           (else
                                            (cut n (car l1) i)))))
                         (halve (cdr l1) (cdr l2) i)))))
               (skip (subr (maxeff (read @heap) (write @heap) spin (read (globals num))) (int items int) items)
                 (lambda (j a i)
                   (if (= j 0)
                       a
                       (begin
                         (set-car! a (num i))
                         (skip (- j 1) (cdr a) i)))))
               (cut (subr (maxeff (read @heap) (write @heap) spin (read (globals num))) (int items int) items)
                 (lambda (j a i)
                   (if (= j 1)
                       (let ((x (cdr a)))
                         (begin
                           (set-cdr! a nil)
                           x))
                       (begin
                         (set-car! a (num i))
                         (cut (- j 1) (cdr a) i))))))
        (outer n)))))

(define* items->datum (subr (maxeff (read @heap) spin) (items) datum)
  (lambda (l)
    (if (null? l)
        (datum-list (the (listof datum @heap) nil))
        (datum-cons (tagcase (car l)
                      (null-item () (datum-list (the (listof datum @heap) nil)))
                      (num (x) (datum-int x)))
                    (items->datum (cdr l))))))

(define* result->datum (subr (maxeff (read @heap) spin) (rows) datum)
  (lambda (l)
    (if (null? l)
        (datum-list (the (listof datum @heap) nil))
        (datum-cons (items->datum (car l)) (result->datum (cdr l))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 600)
(define input2 int 50)
(define iterations int 4000)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int rows) rows)
  (lambda (i result) (if (= i 0) result (run (- i 1) (destructive input1 input2)))))
(result->datum (run iterations nil))
