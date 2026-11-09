;; => 5
;; A template's `(with m name)`: the value `name` of module `m`, a binder
;; of the template's (here a `lambda`'s parameter, in the later ones'
;; types) or a module a use gives.
(define-type ordered (moduleof (abs t type) (val less (subr pure (t t) bool))))
(define int-order
  (module (define-type t int)
          (define less (subr pure (t t) bool) (lambda (a b) (< a b)))))
(define-syntax max-fn
  (-> () expr)
  (syntax-rules ()
    ((_) (lambda ((o ordered) (a (select o t)) (b (select o t))) (if ((with o less) a b) b a)))))
(define-syntax less-of
  (-> (id expr expr) expr)
  (syntax-rules ()
    ((_ m x y) ((with m less) x y))))
(define max-of (subr pure ((o : ordered) (select o t) (select o t)) (select o t)) (max-fn))
(if (less-of int-order 1 2) (max-of int-order 3 5) 0)
