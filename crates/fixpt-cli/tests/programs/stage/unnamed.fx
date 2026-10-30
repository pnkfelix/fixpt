;; `stage` takes a module by its name: refused, by both checkers.
(define api (module (define x 41)))
(define f (subr (maxeff stage spin (read (globals api))) () int)
  (lambda () (stage (module (define y 1)) pure int '1 (p (p)) (why 0))))
