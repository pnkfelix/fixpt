;;; Recursion alternating between native and cellular code (`DONE.md`
;;; §93): each call between the machines nests a few Rust frames, so a
;;; few million deep runs out of the thread's Rust stack long before
;;; either machine's own. A stack overflow, the session still usable after.
(define-effect deep (maxeff spin (read @globals)))
(define-rec
  (deep-n (subr deep (int) int)
    (lambda (d) (if (= d 0) 0 (+ 1 (deep-c (- d 1))))))
  (deep-c (subr deep (int) int)
    (lambda (d) (begin (stay-cellular #u) (if (= d 0) 0 (+ 1 (deep-n (- d 1))))))))
(deep-n 1000)
(deep-n 3000000)
(deep-n 1001)
