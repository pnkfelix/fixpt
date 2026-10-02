;;; The FX-26 parser, in FX-26: `(load-module "file")` (`docs/research/
;;; first-class-modules.md`, M7), as the Rust parser's `parse_load_module`
;;; reads it: the file's forms a module's items, its `define-datatype`s
;;; expanded and its `define-generative`s left a module's own. After
;;; `parser.fx`, which reaches it through `parse-load-module`.
;;;
;;; FX-26 code reads no files: the driver reads each file a program's
;;; `load-module`s name, with the reader written in FX-26, before the
;;; program is parsed (`loaded-files!`), as a system call would. A file's
;;; positions are its own, each moved past the program's by its base, a
;;; multiple of `load-base`, so that what is said of a place in it can say
;;; which file and where.

;; What the driver read for each `load-module`, by where the form starts:
;; the file's base (0 if it could not be read or read), its path, why not
;; (`cannot read …`, or where in it reading failed), its forms, and its
;; text.
(define-type loaded-file
  (productof (1 int) (2 int) (3 string) (4 string) (5 syns-a) (6 string)))
(define-type loaded-files (listof loaded-file acyclic))
(define loaded (ref loaded-files @s) (new nil))
;; For a driver: what the program's `load-module`s read.
(define loaded-files! (subr (maxeff (read @globals) (write @s)) (loaded-files) unit)
  (lambda (fs) (set loaded fs)))
;; The positions of one file and the next apart.
(define load-base int 1000000000)

;; What was read for the `load-module` starting at `a`, in a list of one.
(define loaded-at (subr (maxeff (read @globals) (read @s)) (loaded-files int) loaded-files)
  (lambda (fs a)
    (cond ((null? fs) nil)
          ((= (extract (car fs) 1) a) (the loaded-files (cons (car fs) nil)))
          (else (loaded-at (cdr fs) a)))))
;; The file read at `base`, in a list of one.
(define loaded-based (subr (maxeff (read @globals) (read @s)) (loaded-files int) loaded-files)
  (lambda (fs base)
    (cond ((null? fs) nil)
          ((and (> base 0) (= (extract (car fs) 2) base)) (the loaded-files (cons (car fs) nil)))
          (else (loaded-based (cdr fs) base)))))

;; `s`, its positions moved by `base`.
(define-rec
  (syn-moved (subr (maxeff (read @globals) (read @s) (alloc @s) spin) (syn int) syn)
    (lambda (s base)
      (tagcase s
        (atom (d a b) (atom d (+ a base) (+ b base)))
        (lst (items d a b) (lst (syns-moved items base) d (+ a base) (+ b base)))
        (dotted (items t d a b)
          (dotted (syns-moved items base) (syn-moved t base) d (+ a base) (+ b base)))
        (vec (items d a b) (vec (syns-moved items base) d (+ a base) (+ b base))))))
  (syns-moved (subr (maxeff (read @globals) (read @s) (alloc @s) spin) (syns-a int) syns-a)
    (lambda (xs base)
      (if (null? xs) nil (cons (syn-moved (car xs) base) (syns-moved (cdr xs) base))))))

;; Where position `at` of `text` is: `line:column`, each from 1.
(define text-place (subr (maxeff (read @globals) spin) (string int) string)
  (lambda (text at)
    (letrec ((go (subr (maxeff (read @globals) spin) (int int int) string)
               (lambda (i line col)
                 (cond ((or (>= i at) (>= i (string-length text)))
                        (str3 (int->string line) ":" (int->string col)))
                       ((char=? (string-ref text i) #\newline) (go (+ i 1) (+ line 1) 1))
                       (else (go (+ i 1) line (+ col 1)))))))
      (go 0 1 1))))
;; What an error `m` at `at`, in the file read at `base` (`fs`), says where
;; the `load-module` is: the file, and where in it. As it is, if `at` is
;; not in that file.
(define in-loaded
  (subr (maxeff (read @globals) (read @s) spin) (loaded-files int string int) string)
  (lambda (fs base m at)
    (let ((f (loaded-based fs base)))
      (if (or (null? f) (< at base) (>= at (+ base load-base)))
          m
          (let ((path (extract (car f) 4)) (text (extract (car f) 6)))
            (string-append (str3 "in `" path "`, ")
                           (str3 (text-place text (- at base)) ": " m)))))))

;; A file's form, as a module's items: a datatype's type and constructors,
;; as the program's would be (`parse-datatype`); anything else one item.
(define top-item (subr parses (top) mod-item)
  (lambda (t)
    (tagcase t
      (t-define-type (head sum a b) (mod-item-of 1 (syn-symbol head) (one-syn sum) nil))
      (t-define (n tys x a b) (mod-item-of 2 n tys (the exp-list (cons x nil))))
      (else y (pfail-at module-usage 0 0)))))
(define tops-items (subr (maxeff parses spin) (top-list mod-items) mod-items)
  (lambda (ts rest) (if (null? ts) rest (cons (top-item (car ts)) (tops-items (cdr ts) rest)))))
(define file-items (subr (maxeff parses spin) (syns-a) mod-items)
  (lambda (fs)
    (cond ((null? fs) nil)
          ((datatype? (car fs)) (tops-items (parse-datatype (car fs)) (file-items (cdr fs))))
          (else (let ((it (parse-module-item (car fs)))) (cons it (file-items (cdr fs))))))))

;; The items of a form that is a module.
(define module-items-of (subr pure (top) mod-items)
  (lambda (t)
    (tagcase t
      (t-exp (x) (tagcase x (e-module (items a b) items) (else y nil)))
      (else y nil))))
;; A module's item that says it was read from a file: its base, and path.
(define loaded-mark (subr (read @globals) (int string) mod-item)
  (lambda (base path) (mod-item-of base (string->symbol path) (the syns-a nil) nil)))
;; A module's item that says reading its file failed, and why: refused where
;; the module is checked, as the Rust checker refuses it where it parses
;; the form.
(define loaded-error (subr (read @globals) (string) mod-items)
  (lambda (m) (cons (mod-item-of -1 (string->symbol m) (the syns-a nil) nil) nil)))

;; `(load-module "path")`, at `a`..`b`: the module's items, after its mark;
;; or why it could not be read.
(define parse-loaded (subr (maxeff parses spin) (string int int) mod-items)
  (lambda (path a b)
    (let ((f (loaded-at (get loaded) a)))
      (cond
        ((null? f) (loaded-error (str3 "cannot read `" path "`: it was not read")))
        ((= (extract (car f) 2) 0) (loaded-error (extract (car f) 3)))
        (else
         (let* ((base (extract (car f) 2))
                (forms (syns-moved (extract (car f) 5) base))
                ;; The items, as a form's, out of the prompt that catches
                ;; what is wrong in them.
                (r (prompt parse-tag (p-ok (cons (t-exp (e-module (file-items forms) a b)) nil))
                           (lambda (r) r))))
           (tagcase r
             (p-err (m x y)
               (if (>= x base)
                   (loaded-error (in-loaded (get loaded) base m x))
                   (pfail-at m x y)))
             (p-ok (ts)
               (cons (loaded-mark base path) (module-items-of (car ts)))))))))))
(set parse-load-module parse-loaded)
