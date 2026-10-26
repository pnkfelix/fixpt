;; => "a|b|err|got hi|exited 3; failed not-found"
;; Programs run beside this one (Heist's, FIXPT-CHANGES.md F4): started,
;; given input, their output (standard output and error, one stream) read
;; until they end; and one that cannot start.
(define* wait-for (subr (maxeff (io process) (io clock) spin) (int string) string)
  ;; What process `p` writes, after `acc`, until it ends; and how it ended.
  (lambda (p acc)
    (let ((more (string-append acc (process-output p))))
      (tagcase (process-status p)
        (exited c (string-append more "exited " (int->string c)))
        (signalled s (string-append more "signalled " (int->string s)))
        (unknown u (string-append more "unknown"))
        (running u (begin (sleep-until (i64+ (clock) (int->i64 1000000))) (wait-for p more)))))))
(define* bars (subr spin (string) string)
  ;; `s`, each newline a bar.
  (lambda (s)
    (letrec ((go (subr spin (int (listof char acyclic)) (listof char acyclic))
               (lambda (i acc)
                 (if (< i 0) acc
                     (let ((c (string-ref s i)))
                       (go (- i 1) (cons (if (char=? c #\newline) #\| c) acc)))))))
      (list->string (go (- (string-length s) 1) nil)))))
(define script string "printf 'a\\nb\\n'; echo err >&2; read x; echo got $x; exit 3")
(define ran string
  (tagcase (process-start (list "/bin/sh" "-c" script) "")
    (started p (begin (process-write p "hi\n") (process-close-input p) (bars (wait-for p ""))))
    (failed e "failed")))
(define missing string
  (tagcase (process-start (list "/no/such/program") "")
    (started p "started")
    (failed e (tagcase (extract e kind) (not-found u "failed not-found") (else y "failed other")))))
(string-append ran "; " missing)
