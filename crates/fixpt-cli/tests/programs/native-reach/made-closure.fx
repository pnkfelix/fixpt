;;; A closure cellular code makes, as kayak's emitter module's members were:
;;; by a definition run as cellular code (`stay-cellular`), kept in a list
;;; (no global's value, which is compiled after its definition); called by
;;; native code (`native_reach.rs`).
(define adders (listof (subr pure (int) int) @heap)
  (let* ((k (stay-cellular 5)) (adder (lambda ((x int)) (+ x k)))) (list adder)))
(define loop (subr (maxeff spin (read @heap) (read (globals loop adders))) (int int) int)
  (lambda (i acc) (if (= i 0) acc (loop (- i 1) ((car adders) acc)))))
(loop 1000 0)
