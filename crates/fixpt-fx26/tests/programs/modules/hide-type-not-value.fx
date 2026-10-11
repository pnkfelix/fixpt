;; => 7
;; A hidden type does not hide a value of the same name, nor a hidden value
;; a type: their marks are apart (`%hidden:`, `%hiddenv:`), as a type and
;; a value may share a name.
(define m (module (hide (define-type k int))
                  (define k k 7)
                  (define-type j int)
                  (hide (define j int 1))))
(with m k)
