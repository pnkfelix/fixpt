;;; A top-level procedure calling itself in tail position, as kayak's
;;; `find-bind` does, defined one form at a time (the REPL, `fixpt run`): its
;;; register code loops behind a guard that the global still holds it, as a
;;; definition compiled whole does (`native_reach.rs`).
(define-effect walks (maxeff (read @heap) (read @globals) spin))
(define find (subr walks (string (listof string @heap)) bool)
  (lambda (name xs)
    (cond ((null? xs) #f) ((string=? (car xs) name) #t) (else (find name (cdr xs))))))
(find "c" (list "a" "b" "c"))
,disassemble find
