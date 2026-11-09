;; ! `#%toplevel:limit` names no parameter or result here
;; A name in a template's specification that the template does not bind is
;; the top level's, which a specification may not name: not a parameter a
;; use gives the same name.
(define-syntax define-capped
  (-> (bvar bvar) defn)
  (syntax-rules ()
    ((_ name p) (define name (subr pure ((p : int)) int (requires (< p limit))) (lambda (x) x)))))
(define-capped capped limit)
