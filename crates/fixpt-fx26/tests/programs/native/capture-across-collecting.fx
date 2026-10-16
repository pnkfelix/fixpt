;;; Captures in cellular code up to a prompt in the native frames out from
;;; it, run collecting at every safepoint (`DONE.md` §104): the tag, moved
;;; by the collection at the capture's own safepoint (every fourth is major,
;;; and moves everything), still finds its prompt there. Each capture is
;;; under 0 to 3 cellular frames, so that the safepoints before it differ,
;;; and some capture's is a major collection's.
(define-effect grabbing (maxeff (goto @p) (comefrom @p) (read @globals) spin))
(define u (prompt-tag int int grabbing @p) (make-continuation-prompt-tag))
(define* grab-c (subr grabbing () int)
  (lambda ()
    (begin (stay-cellular #u) (call-with-composable-continuation (lambda (k) (k (k 1))) u))))
(define* under-n (subr grabbing ((subr grabbing () int)) int)
  (lambda (b) (prompt u (b) (lambda (v) v))))
(define* climb-c (subr grabbing ((subr grabbing () int) int) int)
  (lambda (g d) (begin (stay-cellular #u) (if (= d 0) (g) (+ 1 (climb-c g (- d 1)))))))
(define* times (subr grabbing (int int) int)
  (lambda (n acc)
    (if (= n 0)
        acc
        (times (- n 1) (+ acc (under-n (lambda () (climb-c grab-c (remainder n 4)))))))))
(times 40 0)
