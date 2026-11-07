;;; The front end driving itself (PLAN.md §11, step 11): a program's text
;;; read, parsed, checked and compiled, all by the pieces written in FX-26,
;;; to the word that runs it. Appended to the front end, whose last
;;; expression gives the driver and the pieces it drives, so that the front
;;; end compiled to a word gives, when run, the compiler, compiled, ready to
;;; compile; and each piece, to be timed alone (`tests/bootstrap.rs`).

(define-datatype bresult (b-word tword) (b-fail string))

(define b-feed (->* (state string int) state)
  (lambda (st text i)
    (let ((rest (substring text i (string-length text))))
      (eager-feed (eager-feed-string st rest) (integer->char 10)))))

;; Reading a text to its forms, in `@c`; and the stages after, parsing,
;; checking and compiling, their failures caught.
(define-effect b-reading (maxeff reads (read @c) (alloc @c) spin))
;; What compiling may do, of the compiler's types (`compile-types.fx`).
(define compile-types (load-module "fx26:compile-types.fx"))
(define-effect compiles (select compile-types compiles))
;; What the checker tells the compiler (`check-env-types.fx`).
(define check-env-types (load-module "fx26:check-env-types.fx"))
;; What checking may do, of the checker's types (`check-types-types.fx`).
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-effect checks (select check-types-types checks))
(define-effect b-stages (maxeff parses checks compiles (comefrom @p) (comefrom @z) (comefrom @y)))

;; Every form of `text`, as the reader reads it, or none if it cannot.
(define b-read (->* (string) (listof syns acyclic))
  (lambda (text)
    (let ((st (b-feed (eager-start-fx26) text 0)))
      (if (string=? (symbol->string (eager-status st)) "complete")
          (cons (eager-state-syntax st) nil)
          nil))))

;; A program's forms parsed (`parse-program`): read in the standard
;; environment `std`'s state (`standard-state`), by `path`, under the
;; checker's switches (`checked-settings`).
(define readings ((proj (load-module "fx26:readings.fx") @s @e @m @c)))
(define b-parse
  (lambda ((std (listof syn acyclic)) (forms (listof syn acyclic)))
    (let ((s ((with readings standard-state) std)))
      (extract (parse-program (product (1 0) (2 s) (3 (checked-settings))) forms) 1))))
;; A program's trees compiled with what the checker written in FX-26 found,
;; the trees' own keys.
(define b-compile
  (lambda ((tops (listof top acyclic)) (facts (select check-env-types k-facts)))
    (compile-program tops facts (product (1 -1) (2 0) (3 nil)))))

;; `program`, checked in the initial environment written `standard`
;; (`(name type)` for each binding), and compiled.
(define bootstrap (->* (string string) bresult)
  (lambda (standard program)
    (let ((std (b-read standard)) (prog (b-read program)))
      (if (or (null? std) (null? prog))
          (b-fail "the reader could not read the text")
          (tagcase (begin (check-lines! #f)
                          (b-parse (car std) (car prog)))
            (p-err (m a b) (b-fail (string-append "parse: " m)))
            (p-ok (tops)
              (tagcase (check-program (car std) tops)
                (k-err (m a b) (b-fail (string-append "check: " m)))
                (k-ok (lines)
                  (tagcase (compile-checked (checked-tops) (checked-extracts)
                                            (product (1 0) (2 0) (3 nil)))
                    (c-ok (w) (b-word w))
                    (c-err (m) (b-fail (string-append "compile: " m)))))
                (k-done (te) (b-fail "check: no result")))))))))

(product (1 bootstrap) (2 b-read) (3 b-parse) (4 check-program)
         (5 b-compile) (6 checked-extracts) (7 native-assemble) (8 compile-registers!)
         (9 loaded-files!) (10 native-assemble-x64))
