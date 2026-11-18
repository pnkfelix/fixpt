; `write-file-unflushed` (Kayak's, 2026-11-18): a file replaced whole and
; atomically, as `write-file` replaces it, nothing flushed to the disk:
; written long, then short, it reads back the short alone; one in a
; directory that is not there, `not-found`: status 7.
(define-type read-result (sumof (data (bytevectorof @b)) (failed io-error)))
(define put (subr (maxeff (io fs-write) (alloc @b) (read @b)) (string string) int)
  (lambda (path text)
    (tagcase (write-file-unflushed path (the (bytevectorof @b) (string->utf8 text)))
      (done u 0)
      (failed e (tagcase (extract e kind) (not-found u 7) (else k 8))))))
(define text-of (subr (read @b) (read-result) string)
  (lambda (r)
    (tagcase r
      (data b (tagcase (utf8->string b) (text s s) (bad k "not UTF-8")))
      (failed e (extract e detail)))))
(define main (subr (maxeff (io fs-read) (io fs-write) (io stdout) (alloc @b) (read @b)
                           (read (globals put text-of)))
                   () int)
  (lambda ()
    (begin
      (put "c.txt" "a longer text, at first")
      (put "c.txt" "short")
      (write-out (string-append (text-of (read-file "c.txt")) "\n"))
      (put "no-such-directory/c.txt" "lost"))))
