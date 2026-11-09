;; ! `int-order` gives no value `more`, which a template's `(with int-order more)` takes from it alone
;; A template's `(with m name)` where `m` gives no `name`: refused, not
;; what `name` is where the macro is used (the top level's `more` here),
;; which a `with`'s body would otherwise read.
(define int-order
  (module (define-type t int)
          (define less (subr pure (t t) bool) (lambda (a b) (< a b)))))
(define more (subr pure (int) int) (lambda (x) x))
(define-syntax call-more
  (-> (id expr) expr)
  (syntax-rules ()
    ((_ m e) ((with m more) e))))
(call-more int-order 1)
