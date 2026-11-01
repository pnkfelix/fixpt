;;; The FX-26 parser's record of the files a program loads (`parser.fx`):
;;; what a driver says it read, where an error in one is said to be, each
;;; top-level `include`'s names, and the loads shared between files. Apart
;;; from `parser.fx` since 2026-10-31 (`TODO.md` §188), which loads it and
;;; gives on what it defines.
;;;
;;; A module file of the reader's regions and the parser's, as `parser.fx`
;;; is: the state is at `rs`, one for each `parser.fx` made.
(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
;; The parser's types, at these regions (`parser-types.fx`), and the names it
;; uses of them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") rs re rm rc rp)))
(import parser-types e-module t-exp (type names top top-list mod-items loaded-files))

;;; ------------------------------------------------------------ files loaded

(define loaded (ref loaded-files rs) (new nil))
;; The same, in the order a driver reads them, depth first, as the parser
;; meets the loads: the next load's, first, most often (`loaded-next-at`).
(define loaded-next (ref loaded-files rs) (new nil))
;; For a driver: what the program's `load-module`s read, the last read
;; first.
(define loaded-files! (->* (loaded-files) unit)
  (lambda (fs) (begin (set loaded fs) (set loaded-next (loaded-onto fs nil)))))
;;; ------------------------------------------------------------ top-level includes

;; For a driver: each top-level `(include m)` of the program, by where it
;; starts, and the names of what `m` gives, its values, types and effects,
;; which only a checker knows (`Checker::include_forms`); or why it is
;; refused, and where.
(define-type include-given
  (productof (1 int) (2 names) (3 names) (4 names) (5 string) (6 int) (7 int)))
(define-type includes (listof include-given acyclic))
(define includes-given (ref includes rs) (new nil))
(define includes-given! (->* (includes) unit) (lambda (is) (set includes-given is)))
;; What was given of the `include` starting at `a`, in a list of one.
(define include-given-at (->* (includes int) includes)
  (lambda (is a)
    (cond ((null? is) nil)
          ((= (extract (car is) 1) a) (the includes (cons (car is) nil)))
          (else (include-given-at (cdr is) a)))))
;; `xs` reversed onto `ys`.
(define loaded-onto
  (->* (loaded-files loaded-files) loaded-files)
  (lambda (xs ys) (if (null? xs) ys (loaded-onto (cdr xs) (the loaded-files (cons (car xs) ys))))))
;; The positions of one file and the next apart.
(define load-base int 1000000000)

;; Every load of a path is one value, made once (`TODO.md` §68): the first
;; defines a hidden global, `%shared:` and its key (`loaded-key`), as the
;; file loaded, before the form that loads it; every load is that global.
;; The keys loaded, and the definitions not yet placed before their form.
(define shared-keys (ref (listof string acyclic) rs) (new nil))
(define shared-pending (ref top-list rs) (new nil))
;; The files being read now, by key, each with its path as its load wrote
;; it, the innermost first: a load of one of them is a cycle (`TODO.md`
;; §71).
(define loading-keys (ref (listof (pairof string string rs) acyclic) rs) (new nil))
;; Whether `key` names a `load-input`'s file.
(define input-key? (->* (string) bool)
  (lambda (k) (and (> (string-length k) 6) (string=? (substring k 0 6) "input:"))))
;; A program's parse begins with none.
(define shared-reset! (->* () unit)
  (lambda ()
    (begin (set shared-keys nil) (set shared-pending nil) (set loading-keys nil))))
;; The files being read, as `loading-keys` keeps them.
(define-type loading-list (listof (pairof string string rs) acyclic))
;; The chain from the load of `key` on, onto `acc`, as `parse.rs` says it:
;; `a` loads `b` …; "" if `key` is not being read.
(define load-chain (->* (loading-list string string) string)
  (lambda (ks key acc)
    (cond ((null? ks) "")
          ((string=? (car (car ks)) key)
           (string-append "a load cycle: `" (cdr (car ks)) acc))
          (else (load-chain (cdr ks) key
                            (string-append "` loads `" (cdr (car ks)) acc))))))
;; If `key` is being read, the cycle a load of it at `path` makes; else "".
(define load-cycle (->* (string string) string)
  (lambda (key path)
    (load-chain (get loading-keys) key (string-append "` loads `" path "`"))))
;; The definitions not yet placed, in order, now placed: none left.
(define shared-taken (->* () top-list)
  (lambda ()
    (letrec ((onto (subr (maxeff (read @globals) spin) (top-list top-list) top-list)
                (lambda (xs ys) (if (null? xs) ys (onto (cdr xs) (cons (car xs) ys))))))
      (let ((ts (get shared-pending))) (begin (set shared-pending nil) (onto ts nil))))))
(define shared-key? (->* (string (listof string acyclic)) bool)
  (lambda (k ks) (and (not (null? ks)) (or (string=? k (car ks)) (shared-key? k (cdr ks))))))

;; What was read for the `load-module` starting at `a`, in a list of one.
(define loaded-at (->* (loaded-files int) loaded-files)
  (lambda (fs a)
    (cond ((null? fs) nil)
          ((= (extract (car fs) 1) a) (the loaded-files (cons (car fs) nil)))
          (else (loaded-at (cdr fs) a)))))
;; The same, taking it from the front of `loaded-next` where it is there,
;; as it is when the driver read the files in the order they are parsed;
;; else found as `loaded-at` finds it.
(define loaded-next-at (->* (int) loaded-files)
  (lambda (a)
    (let ((next (get loaded-next)))
      (if (and (not (null? next)) (= (extract (car next) 1) a))
          (begin (set loaded-next (cdr next)) (the loaded-files (cons (car next) nil)))
          (loaded-at (get loaded) a)))))
;; The file read at `base`, in a list of one.
(define loaded-based (->* (loaded-files int) loaded-files)
  (lambda (fs base)
    (cond ((null? fs) nil)
          ((and (> base 0) (= (extract (car fs) 2) base)) (the loaded-files (cons (car fs) nil)))
          (else (loaded-based (cdr fs) base)))))

;; Where position `at` of `text` is: `line:column`, each from 1.
(define text-place (->* (string int) string)
  (lambda (text at)
    (letrec ((go (subr (maxeff (read @globals) spin) (int int int) string)
               (lambda (i line col)
                 (cond ((or (>= i at) (>= i (string-length text)))
                        (string-append (int->string line) ":" (int->string col)))
                       ((char=? (string-ref text i) #\newline) (go (+ i 1) (+ line 1) 1))
                       (else (go (+ i 1) line (+ col 1)))))))
      (go 0 1 1))))
;; What an error `m` at `at`, in the file read at `base` (`fs`), says where
;; the `load-module` is: the file, and where in it. As it is, if `at` is
;; not in that file.
(define in-loaded
  (->* (loaded-files int string int) string)
  (lambda (fs base m at)
    (let ((f (loaded-based fs base)))
      (if (or (null? f) (< at base) (>= at (+ base load-base)))
          m
          (let ((path (extract (car f) 4)) (text (extract (car f) 6)))
            (string-append "in `" path "`, "
                           (text-place text (- at base)) ": " m))))))

;; Error `m` at `at`, said in each file on the way out to the program
;; (`TODO.md` §73): while `at` is in a file read (past `load-base`), `in
;; `path`, line:col: m`, at where that file is first loaded (in a file read
;; before it, so this ends, a load cycle too); and where it is then. As
;; Rust's `Checker::in_loaded`.
(define loaded-placed
  (->* (loaded-files string int) (productof (1 string) (2 int)))
  (lambda (fs m at)
    (let ((f (if (< at load-base) nil (loaded-first fs (* load-base (quotient at load-base)) nil))))
      (if (null? f)
          (product (1 m) (2 at))
          (let* ((base (extract (car f) 2))
                 (where (text-place (extract (car f) 6) (- at base))))
            (loaded-placed
             fs (string-append "in `" (extract (car f) 4) "`, " where ": " m)
             (extract (car f) 1)))))))

;; The file read at `base`, as it was first loaded, in a list of one: the
;; last of `fs`, newest first (`loaded-files!`).
(define loaded-first
  (->* (loaded-files int loaded-files) loaded-files)
  (lambda (fs base found)
    (cond ((null? fs) found)
          ((= (extract (car fs) 2) base)
           (loaded-first (cdr fs) base (the loaded-files (cons (car fs) nil))))
          (else (loaded-first (cdr fs) base found)))))

;; The same, the file named `path`, as the load being read wrote it: a
;; file read once may be loaded under more than one path (`TODO.md` §71).
(define in-loaded-as
  (->* (loaded-files int string string int) string)
  (lambda (fs base path m at)
    (let ((f (loaded-based fs base)))
      (if (or (null? f) (< at base) (>= at (+ base load-base)))
          m
          (string-append "in `" path "`, "
                         (text-place (extract (car f) 6) (- at base)) ": " m)))))

;; The items of a form that is a module.
(define module-items-of (->* (top) mod-items)
  (lambda (t)
    (tagcase t
      (t-exp (x) (tagcase x (e-module (items a b abk) items) (else y nil)))
      (else y nil))))
