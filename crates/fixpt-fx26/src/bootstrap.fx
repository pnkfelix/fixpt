;;; The front end driving itself (PLAN.md §11, step 11): a program's text
;;; read, parsed, checked and compiled, all by the pieces written in FX-26,
;;; to the word that runs it. Appended to the front end, whose last
;;; expression it is, so that the front end compiled to a word gives, when
;;; run, this driver: the compiler, compiled, ready to compile.

(define-datatype bresult (b-word tword) (b-fail string))

(define b-feed (subr reads (state string int) state)
  (lambda (st text i)
    (if (= i (string-length text))
        (eager-feed st (integer->char 10))
        (b-feed (eager-feed st (string-ref text i)) text (+ i 1)))))

;; Every form of `text`, as the reader reads it, or none if it cannot.
(define b-read (subr (maxeff reads (read @c) (alloc @c)) (string) (listof syns @s))
  (lambda (text)
    (let ((st (b-feed (eager-start-fx26) text 0)))
      (if (string=? (datum-symbol-name (eager-status st)) "complete")
          (cons (eager-state-syntax st) nil)
          nil))))

;; `program`, checked in the initial environment written `standard`
;; (`(name type)` for each binding), and compiled.
(define bootstrap (subr (maxeff reads (read @c) (alloc @c) parses checks compiles (comefrom @p) (comefrom @z) (comefrom @y)) (string string) bresult)
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
                  (tagcase (compile-program tops (checked-extracts))
                    (c-ok (w) (b-word w))
                    (c-err (m) (b-fail (string-append "compile: " m)))))
                (k-done (te) (b-fail "check: no result")))))))))

bootstrap
