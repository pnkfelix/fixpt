;; ! `stage` is given a bound of `t`, which may be of less than `t` is: `t` may stand only where less is safe, in the effect, and in what is given, not taken; or give its exact evidence
;; A bound in a list at a region a variable names, which may be written:
;; compared exactly, so refused as the program is checked.
(define api (module (define x 41)))
(define listing
  (poly ((t type) (r region))
    (subr (maxeff stage spin (read (globals api))) ((typebound t) (regionrep r) datum) int))
  (plambda ((t type) (r region))
    (lambda (tb rb code) (stage api pure (listof t r) code (p 1) (why -1) (given tb rb)))))
0
