;; A module's member re-exported, `(define inc (with m inc))`: a call of
;; the re-export inlined as a call of `inc` defined directly would be,
;; behind a guard that the global holds the member's closure (`TODO.md`
;; §38). `inc` names no other member; one that did would be called.
(define m (module (define inc (subr pure (int) int) (lambda (x) (+ x 1)))))
(define inc (with m inc))
(define-effect counts (maxeff spin (read (globals inc))))
(define loop (subr counts (int int) int)
  (lambda (i acc)
    (letrec ((go (subr counts (int int) int)
               (lambda (i acc) (if (= i 0) acc (go (- i 1) (inc acc))))))
      (go i acc))))
(loop 1000 0)
