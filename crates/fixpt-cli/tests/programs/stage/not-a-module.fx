;; `stage` takes a module: refused, by both checkers.
(define n 3)
(define f (subr (maxeff stage spin (read (globals n))) () int)
  (lambda () (stage n pure int '1 (p (p)) (why 0))))
