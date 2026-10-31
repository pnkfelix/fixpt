;; A heap dumped (`fixpt dump`, `TODO.md` §189): what the load does, a
;; count bumped twice, is in the dump; `main` bumps it again as it runs.
(define count (ref int @heap) (new 0))
(define bump! (subr (maxeff (read @heap) (write @heap) (read (globals count))) () unit)
  (lambda () (set count (+ (get count) 1))))
(bump!)
(bump!)
(define main
  (subr (maxeff (io stdout) (io args) (read @heap) (write @heap) (alloc @a) (read @a)
                (read (globals count bump!)))
        () int)
  (lambda ()
    (let ((as (the (listof string @a) (args))))
      (begin (bump!)
             (write-out (string-append "count " (int->string (get count)) ", args "
                                       (int->string (list-length as)) "\n"))
             7))))
