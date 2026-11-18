;; => 42
;; A macro's use names a binder, here `loop`, and its body calls what that
;; binds, though a macro `loop` is defined at the top level (TODO.md §295,
;; found by §294: ratfink's `iterate` beside a file with a macro `loop`).
(define-syntax loop (macro (_ expr) expr) (syntax-rules ((_ e) e)))
(define-syntax iterate
  (macro (_ name @ bvar n @ expr body @ expr) expr (bind name in body))
  (syntax-rules
    ((_ name n body)
     ((letrec ((name (subr spin (int) int) (lambda ((i int)) (body i)))) name) n))))
(iterate loop 10 (lambda ((i int)) (if (= i 0) 42 (loop (- i 1)))))
