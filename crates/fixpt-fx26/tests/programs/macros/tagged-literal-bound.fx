;; ! `#Lq"z"` is not a name that may be bound
;; A tagged literal where a macro binds a name: refused, and written as it
;; was read, by both expanders.
(define-syntax bindit (syntax-rules ((_ x e) (let ((x 1)) e))))
(bindit #Lq"z" 2)
