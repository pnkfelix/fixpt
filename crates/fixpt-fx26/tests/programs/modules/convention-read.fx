;; => "x10 at 296; refused as said: #t #t #t"
;; A native convention's declaration read as data (`fx26:convention.fx`,
;; `TODO.md` §97): fixpt's, whose closure register and `closure` routine's
;; state field a generator reads; and three it refuses, a clause missing,
;; one it has no room for, one it cannot hold, each as it says.
(define cv (load-input "fx26:convention.fx"))
(define why (subr (maxeff (read @globals) spin) ((listof string acyclic)) string)
  (lambda (ts)
    (tagcase ((with cv cv-read-clauses) ts)
      (ok c (string-append "x" (int->string (extract (extract c registers) closure)) " at "
                           (int->string (extract (extract c state) closure))))
      (refused w w))))
(define says (subr (maxeff (read @globals) spin) ((listof string acyclic) string) string)
  (lambda (ts want) (if (string=? (why ts) want) "#t" (why ts))))
(define mine (listof string acyclic) (the (listof string acyclic) (native-convention)))
(define narrow string "(registers (arguments x1 x2) (frame x29))")
(string-append
  (why mine) "; refused as said: "
  (says (cdr mine) "no `target` clause") " "
  (says (cons "(color blue)" mine) "a `color` clause, which a convention has no room for") " "
  (says (cons (car mine) (cons narrow (cdr (cdr mine))))
        (string-append "the `registers` clause is not one a convention holds: " narrow)))
