;;; Aborts across machines: a prompt cellular code installed (made cellular
;;; by `stay-cellular`), aborted to from native code; one native code
;;; installed, aborted to from cellular code, through native code between;
;;; and an abort under a deep native stack, whose cost does not grow with it.
(define t (prompt-tag int int (maxeff (read @globals) spin) @z) (make-continuation-prompt-tag))
(define* raise (subr (goto @z) (int) void) (lambda (n) (abort-current-continuation t n)))
(define* in-cellular (subr (maxeff (goto @z) (read @globals) spin) (int) int)
  (lambda (n) (begin (stay-cellular #u) (prompt t (+ 1 (raise n)) (lambda (v) (+ v 10))))))
(in-cellular 5)
(define* raise-cellular (subr (maxeff (goto @z) spin) (int) int)
  (lambda (n) (begin (stay-cellular #u) (abort-current-continuation t n))))
(define* mid (subr (maxeff (goto @z) (read @globals) spin) (int) int) (lambda (n) (+ 1 (raise-cellular n))))
(define* in-native (subr (maxeff (goto @z) (read @globals) spin) (int) int) (lambda (n) (prompt t (mid n) (lambda (v) (+ v 100)))))
(in-native 5)
(define* deep (subr (maxeff (goto @z) (read @globals) spin) (int int) int)
  (lambda (d n) (if (= d 0) (prompt t (raise n) (lambda (v) v)) (+ 1 (deep (- d 1) n)))))
(define* many (subr (maxeff (goto @z) (read @globals) spin) (int int) int)
  (lambda (k acc) (if (= k 0) acc (many (- k 1) (+ acc (deep 2000 1))))))
(many 200 0)
