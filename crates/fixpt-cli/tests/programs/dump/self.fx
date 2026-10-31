;; A program that dumps its own heap (`dump-heap!`, `TODO.md` §189) once it
;; has set itself up, and a resumed run of it, which starts at `resumed`.
(define count (ref int @heap) (new 0))
(define resumed
  (subr (maxeff (io stdout) (io args) (read @heap) (write @heap) (alloc @a) (read @a)
                (read (globals count)))
        () int)
  (lambda ()
    (let ((as (the (listof string @a) (args))))
      (begin (set count (+ (get count) 1))
             (write-out (string-append "resumed: count " (int->string (get count)) ", args "
                                       (int->string (list-length as)) "\n"))
             5))))
(define main
  (subr (maxeff (io stdout) (io fs-write) (read @heap) (write @heap)
                (read (globals count resumed)))
        () int)
  (lambda ()
    (begin (set count 40)
           (tagcase (dump-heap! "self.img" resumed)
             (done u (write-out "dumped\n"))
             (failed e (write-out (string-append "no dump: " (extract e detail) "\n"))))
           0)))
