;; Conditions, design B (`docs/research/conditions.md`, `TODO.md` §89): a
;; module file of three procedures, a first library, built in: a program
;; loads it as `(load-module "fx26:conditions.fx")`.
;;
;; - `handle`: runs `body` given a tag of a region made for it alone, and
;;   `on-escape` with what an `escape` to the tag carries. `body` is
;;   polymorphic in the region (rank 2), so nothing it gives can name the
;;   region, and the prompt removes the escape's `(goto r)`.
;; - `with-handler`: runs `body` given a key, in a region made for it alone,
;;   whose mark is `handler`.
;; - `raise`: the handler a key's mark holds, called with the condition
;;   where `raise` is, before anything unwinds; its value is `raise`'s. With
;;   no handler, a panic. A handler that escapes to a `handle` outside is a
;;   restart.
(define handle
  (poly ((a type) (h type) (e effect))
    (subr e ((poly ((r region)) (subr (maxeff e (goto r)) ((escape-tag a h r)) a)) (subr e (h) a))
          a))
  (plambda ((a type) (h type) (e effect))
    (lambda (body on-escape)
      (letregion r
        (let ((t ((proj (proj make-escape-tag r) a h))))
          (prompt t ((proj body r) t) on-escape))))))
(define with-handler
  (poly ((c type) (v type) (a type) (e effect) (eh effect))
    (subr (maxeff e eh)
          ((subr eh (c) v)
           (poly ((k region)) (subr (maxeff e eh (read k)) ((mark-key (subr eh (c) v) k)) a)))
          a))
  (plambda ((c type) (v type) (a type) (e effect) (eh effect))
    (lambda (handler body)
      (letregion k
        (let ((key ((proj (proj make-continuation-mark-key k) (subr eh (c) v)))))
          ((proj (proj with-mark k) (subr eh (c) v) a (maxeff e eh (read k)))
           key
           handler
           (lambda () ((proj body k) key))))))))
(define raise
  (poly ((k region)) (poly ((c type) (v type) (eh effect))
    (subr (maxeff (read k) eh) ((mark-key (subr eh (c) v) k) c) v)))
  (plambda ((k region)) (plambda ((c type) (v type) (eh effect))
    (lambda (key condition)
      (((proj (proj first-mark k) (subr eh (c) v))
        key
        (lambda ((x c)) (error "a condition raised with no handler")))
       condition)))))
