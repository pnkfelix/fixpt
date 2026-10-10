;; ! `w`'s type mentions `t`, which is hidden in this module
;; A hidden `include` hides every name it takes in, the abstract types that
;; are the module's own now too (`TODO.md` §69); one an exported type
;; mentions is refused, as a hidden abstract type is.
(define m (module (hide (include (module (define-generative t int) (define z t (up-t 5)))))
                  (define w t z)))
(with m w)
