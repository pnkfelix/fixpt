;; ! `int-order`, the module a template's `(with module name)` takes from, is bound by the template or given by a use: a top level's, not yet
;; A template's `(with m name)` of a module the top level binds: not yet.
(define int-order
  (module (define-type t int)
          (define less (subr pure (t t) bool) (lambda (a b) (< a b)))))
(define-syntax less?
  (-> (expr expr) expr)
  (syntax-rules ()
    ((_ x y) ((with int-order less) x y))))
(less? 1 2)
