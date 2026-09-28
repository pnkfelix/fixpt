;;; The front end driving itself (PLAN.md §11, step 11): a program's text
;;; read, parsed, checked and compiled, all by the pieces written in FX-26,
;;; to the word that runs it. Appended to the front end, whose last
;;; expression gives the driver and the pieces it drives, so that the front
;;; end compiled to a word gives, when run, the compiler, compiled, ready to
;;; compile; and each piece, to be timed alone (`tests/bootstrap.rs`).

(define-datatype bresult (b-word tword) (b-fail string))

(define b-feed (subr (maxeff reads spin) (state string int) state)
  (lambda (st text i)
    (eager-feed (eager-feed-string st (substring text i (string-length text))) (integer->char 10))))

;; Every form of `text`, as the reader reads it, or none if it cannot.
(define b-read (subr (maxeff reads (read @c) (alloc @c) spin) (string) (listof syns acyclic))
  (lambda (text)
    (let ((st (b-feed (eager-start-fx26) text 0)))
      (if (string=? (datum-symbol-name (eager-status st)) "complete")
          (cons (eager-state-syntax st) nil)
          nil))))

;; `program`, checked in the initial environment written `standard`
;; (`(name type)` for each binding), and compiled.
(define bootstrap (subr (maxeff reads (read @c) (alloc @c) parses checks compiles (comefrom @p) (comefrom @z) (comefrom @y) spin) (string string) bresult)
  (lambda (standard program)
    (let ((std (b-read standard)) (prog (b-read program)))
      (if (or (null? std) (null? prog))
          (b-fail "the reader could not read the text")
          (tagcase (parse-program (car prog))
            (p-err (m a b) (b-fail (string-append "parse: " m)))
            (p-ok (tops)
              (tagcase (check-program (car std) tops)
                (k-err (m a b) (b-fail (string-append "check: " m)))
                (k-ok (lines)
                  (tagcase (compile-checked (checked-tops) (checked-extracts))
                    (c-ok (w) (b-word w))
                    (c-err (m) (b-fail (string-append "compile: " m)))))
                (k-done (te) (b-fail "check: no result")))))))))

(product (1 bootstrap) (2 b-read) (3 parse-program) (4 check-program) (5 compile-program) (6 checked-extracts)
         (7 native-assemble) (8 compile-registers!))
