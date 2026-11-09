;; => 101
;; A name in `(globals …)` the template binds, made fresh there as where it
;; is defined.
(define-syntax define-counter
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ name)
     (begin (define count (ref int @heap) (new 100))
            (define name (subr (maxeff (read @heap) (read (globals count))) () int)
              (lambda () (+ (get count) 1)))))))
(define-counter next)
(next)
