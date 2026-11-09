;; A file's macro that makes definitions: what it defines under the name a
;; use gives is the importer's; its own definition made fresh; its free
;; names this file's.
(define limit int 10)
(define-syntax define-clamped
  (-> (bvar expr) defn)
  (syntax-rules ()
    ((_ name e) (begin (define raw e) (define name (if (> raw limit) limit raw))))))
