;; Staged code changes the program's state through `m`: a reference `m`
;; holds, and a global a procedure of `m` names, which the code itself
;; cannot name; the program then sees both changed.
(define counter (ref int @heap) (new 0))
(define api
  (module (define held (ref int @heap) (new 10))
          (define bump! (lambda () (set counter (+ (get counter) 1))))))
(define run
  (subr (maxeff stage spin (read @heap) (write @heap) (read (globals api counter))) (datum) string)
  (lambda (code)
    (stage api (maxeff (read @heap) (write @heap) (read (globals counter))) unit code
      (p (begin (p) "made"))
      (why (extract why message)))))
(define main
  (subr (maxeff stage spin (io stdout) (read @heap) (write @heap) (read (globals api run counter)))
        () int)
  (lambda ()
    (begin
      (write-out (string-append (run '(begin (bump!) (bump!) (set held (+ (get held) 5)))) "\n"))
      (write-out (string-append (int->string (get counter)) " "
                                (int->string (get (with api held))) "\n"))
      0)))
