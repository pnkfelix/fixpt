;; A file's macro whose description holds a part the use gives beside a
;; type of the file's own: `cell` the file's, `t` the use's, as it is there.
(define-type cell int)
(define-syntax pair-of (-> (type) type) (syntax-rules () ((_ t) (tupleof cell t))))
(define-syntax cell-list (-> (type) type) (syntax-rules () ((_ r) (listof cell r))))
;; A type the use gives under the template's own binder `a`.
(define-syntax ident (-> (type) type)
  (syntax-rules () ((_ t) (poly ((a type)) (subr pure (a t) t)))))
