; Files (Heist's FIXPT-CHANGES.md F5), relative to the working directory:
; what a path is (a link not followed), a link's target; the failures of a
; missing path and a file that is no link.
(define-type file-kind (sumof (file unit) (directory unit) (symlink unit) (other unit)))
(define-type info-result
  (sumof (info (productof (kind file-kind) (size int) (modified int) (mode int)))
         (failed io-error)))
(define* say (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define* what (subr (io fs-read) (string) string)
  (lambda (path)
    (tagcase (the info-result (file-info path))
      (info i (string-append
               path " "
               (tagcase (extract i kind)
                 (file u (string-append "file " (int->string (extract i size))))
                 (directory u "directory") (symlink u "symlink") (other u "other"))
               (if (and (> (extract i modified) 0) (> (extract i mode) 0))
                   ""
                   " (no time or mode)")))
      (failed e (string-append path (tagcase (extract e kind)
                                      (not-found u " not-found")
                                      (else y " failed")))))))
(define* link (subr (io fs-read) (string) string)
  (lambda (path)
    (tagcase (read-symlink path)
      (target t (string-append path " -> " t))
      (failed e (string-append path " no link")))))
(define main (subr (maxeff (io fs-read) (io fs-write) (io stdout) (alloc @b) (read @b) spin
                           (read (globals say what link)))
                   () int)
  (lambda ()
    (begin
      (write-file "a.txt" (the (bytevectorof @b) (string->utf8 "hello")))
      (say (what "a.txt"))
      (say (what "."))
      (say (what "l"))
      (say (link "l"))
      (say (what "nope"))
      (say (link "a.txt"))
      0)))
