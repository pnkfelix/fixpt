; Rejected: each mention of `grow` in itself adds a `listof`, so the
; expansion never ends; a family may mention itself only with the same
; descriptions.
(define-type (grow (t type)) (oneof (end t) (more (grow (listof t @r)))))
(define x (grow int) (one end 1))
