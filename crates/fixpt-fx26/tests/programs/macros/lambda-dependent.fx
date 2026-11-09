;; => 3
;; A template's `lambda` whose parameters' types name the earlier ones,
;; `(select o t)`, as the checkers bind them: each parameter in scope in
;; the types after it, made fresh with them.
(define-type ordered (moduleof (abs t type) (val less (subr pure (t t) bool))))
(define int-order
  (module (define-type t int)
          (define less (subr pure (t t) bool) (lambda (a b) (< a b)))))
(define-syntax first-fn
  (-> () expr)
  (syntax-rules ()
    ((_) (lambda ((o ordered) (a (select o t)) (b (select o t))) a))))
((first-fn) int-order 3 5)
