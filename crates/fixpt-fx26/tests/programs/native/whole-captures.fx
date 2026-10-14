;;; Whole continuations (`cwcc`) that cross machines (`TODO.md` §93):
;;; taken in native or cellular code (made so by `stay-cellular`), thrown
;;; from the other through frames of both, deep too; and kept, then called
;;; again after `cwcc` has returned, from either.
(define-type k-int (subr (goto @k) (int) void))
(define-effect jumping
  (maxeff (goto @k) (comefrom @k) (read @globals) (read @g) (write @g) (alloc @g) spin))
(define saved (ref (listof k-int @g) @g) (new nil))
(define count (ref int @g) (new 0))
;; The throw, native and cellular.
(define* throw-n (subr jumping (k-int int) int) (lambda (k v) (+ 1000 (k v))))
(define* throw-c (subr jumping (k-int int) int)
  (lambda (k v) (begin (stay-cellular #u) (+ 1000 (k v)))))
;; Frames between, native and cellular.
(define* via-n (subr jumping ((subr jumping () int)) int) (lambda (g) (+ 100 (g))))
(define* via-c (subr jumping ((subr jumping () int)) int)
  (lambda (g) (begin (stay-cellular #u) (+ 100 (g)))))
;; The capture, native and cellular: `cwcc`, the receiver throws through `via`.
(define* cap-n (subr jumping ((subr jumping (k-int) int)) int)
  (lambda (r) (+ 1 (cwcc (lambda ((k k-int)) (r k))))))
(define* cap-c (subr jumping ((subr jumping (k-int) int)) int)
  (lambda (r) (begin (stay-cellular #u) (+ 1 (cwcc (lambda ((k k-int)) (r k)))))))
;; Deep: frames of both, a hundred each, between the capture and the throw.
(define-rec
  (deep-n (subr jumping (k-int int) int)
    (lambda (k d) (if (= d 0) (throw-c k 7) (+ 1 (deep-c k (- d 1))))))
  (deep-c (subr jumping (k-int int) int)
    (lambda (k d) (begin (stay-cellular #u) (if (= d 0) (throw-n k 7) (+ 1 (deep-n k (- d 1))))))))
(list (cap-c (lambda (k) (via-n (lambda () (throw-n k 5)))))
      (cap-n (lambda (k) (via-c (lambda () (throw-c k 5)))))
      (cap-c (lambda (k) (via-n (lambda () (throw-c k 5)))))
      (cap-n (lambda (k) (via-c (lambda () (throw-n k 5)))))
      (cap-n (lambda (k) (via-n (lambda () (via-c (lambda () (throw-n k 5)))))))
      (cap-c (lambda (k) (via-c (lambda () (via-n (lambda () (throw-c k 5)))))))
      (cap-c (lambda (k) (deep-n k 200)))
      (cap-n (lambda (k) (deep-c k 200))))
;; Called again after `cwcc` has returned, native and cellular.
(define* again-n (subr jumping (int) int) (lambda (v) (+ 1000 ((car (get saved)) v))))
(define* again-c (subr jumping (int) int)
  (lambda (v) (begin (stay-cellular #u) (+ 1000 ((car (get saved)) v)))))
;; The capture, native and cellular, kept.
(define* keeper (subr jumping (k-int) int) (lambda (k) (begin (set saved (list k)) 0)))
(define* keep-n (subr jumping () int)
  (lambda () (+ 10 (cwcc (lambda ((k k-int)) (keeper k))))))
(define* keep-c (subr jumping () int)
  (lambda () (begin (stay-cellular #u) (+ 10 (cwcc (lambda ((k k-int)) (keeper k)))))))
;; Counts the times through, going again until 3.
(define* loop (subr jumping ((subr jumping () int) (subr jumping (int) int)) int)
  (lambda (keep again)
    (let ((v (keep)))
      (begin (set count (+ (get count) 1))
             (if (< v 13) (again (+ (- v 10) 1)) (+ v (* 100 (get count))))))))
(define* run (subr jumping ((subr jumping () int) (subr jumping (int) int)) int)
  (lambda (keep again) (begin (set count 0) (loop keep again))))
(list (run keep-n again-n) (run keep-c again-c) (run keep-n again-c) (run keep-c again-n))
