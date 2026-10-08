; Accepted: what a test shows of sizes comes from its type, not its name
; (`TODO.md` §54): aliases of `=` and `<` at their types count down a `nat`
; as they do (`nat-count-down.fx`), and one of `nat?` certifies.
(define same (subr pure (int int) (bool (then (= 0 1)) (else (not (= 0 1))))) =)
(define less (subr pure (int int) (bool (then (< 0 1)) (else (<= 1 0)))) <)
(define natural (subr pure (int) (bool (then (nat 0)) (else))) nat?)
(define count (subr (read (globals same)) (nat) int)
  (letrec ((count (subr (read (globals same)) (nat) int)
             (lambda (n) (if (same n 0) 0 (+ 1 (count (- n 1)))))))
    count))
(define* below (subr (read (globals less)) (nat nat) nat)
  (lambda (i n) (if (less i n) (- n i) 0)))
(define* as-nat (subr (read (globals natural)) (int) nat)
  (lambda (x) (if (natural x) (certify-nat x) 0)))
(count (below (as-nat 3) 10))
