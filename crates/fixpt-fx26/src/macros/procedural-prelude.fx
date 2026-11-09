;;; What a procedural macro's transformer sees besides the standard
;;; environment (`macros/procedural.rs`; `TODO.md` §228): aliases, ER's
;;; `rename` and `compare`, and syntactic closures. Each is bound around a
;;; transformer as a local (`procedural::applied`), so that naming one in a
;;; procedure reads no global; each closed over what it uses, so that
;;; calling one does nothing but spin.

;; `x`'s name as where its alias's macro was defined: `%~N:x` is `x`.
(define %alias-base (subr spin (symbol) symbol)
  (letrec ((colon (subr spin (string int) int)
             (lambda (s i)
               (cond ((>= i (string-length s)) -1)
                     ((char=? (string-ref s i) #\:) i)
                     (else (colon s (+ i 1))))))
           (base (subr spin (symbol) symbol)
             (lambda (x)
               (let ((s (symbol->string x)))
                 (if (and (> (string-length s) 2) (string=? (substring s 0 2) "%~"))
                     (let ((c (colon s 2)))
                       (if (< c 0)
                           x
                           (base (string->symbol (substring s (+ c 1) (string-length s))))))
                     x)))))
    base))
;; ER's `rename`, for expansion `n`: `x` as where the macro was defined.
(define %er-renamer (subr pure (int) (subr pure (symbol) symbol))
  (lambda (n)
    (lambda (x)
      (string->symbol
       (string-append "%~"
                      (string-append (int->string n) (string-append ":" (symbol->string x))))))))
;; ER's `compare`: two names the same, aliases as their names.
(define %er-compare (subr spin (symbol symbol) bool)
  (let ((base %alias-base)) (lambda (a b) (symbol=? (base a) (base b)))))
;; Hanson's syntactic closures: `form` closed in `env`, but for its `free`
;; names, which are as where the closure is placed.
(define %make-syntactic-closure (subr pure (symbol datum datum) datum)
  (lambda (env free form) (list '%sc env free form)))
(define %identifier? (subr pure (datum) bool) (lambda (d) (symbol? d)))
(define %identifier=? (subr spin (symbol symbol symbol symbol) bool)
  (let ((base %alias-base)) (lambda (e1 a e2 b) (symbol=? (base a) (base b)))))
