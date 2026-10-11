;; ! `crate` is not a type, nor one a module included gives
;; A family no module included gives, applied in an item's type, is said so.
(define boxes (module (define-type (box (k type) (r region)) (pairof k k r))))
(define m
  (module
    (include boxes)
    (define sum (subr (read @heap) ((crate int @heap)) int) (lambda (b) (car b)))))
