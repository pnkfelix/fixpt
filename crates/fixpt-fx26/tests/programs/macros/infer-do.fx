;; ! `init` is placed in the scope of other bindings than its signature says it is
;; Scheme's `do`: each `step` in every variable's scope, each `init` in
;; none, which no signature says yet (`TODO.md` §223): refused, the
;; signature inferred said.
(define-syntax my-do
  (syntax-rules ()
    ((_ ((v init step) ...) (test res) body)
     (letrec ((loop (subr spin (int int) int)
                    (lambda ((v int) ...) (if test res (begin body (loop step ...))))))
       (loop init ...)))))
(my-do ((i 0 (+ i 1)) (acc 0 (+ acc i))) ((= i 5) acc) #u)
