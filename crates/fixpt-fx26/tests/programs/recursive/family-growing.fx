; Rejected: each mention of `grow` in itself adds a `listof`, so the
; expansion never ends; a family may mention itself only with the same
; descriptions.
(define-type (grow (t type)) (sumof (end t) (more (grow (listof t @r)))))
(define x (grow int) (sum end 1))
