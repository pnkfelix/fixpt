; Keywords (`docs/fx26.md`, "Keywords"): `#:name` evaluates to itself, one
; object for each name, a datum of a shape of its own, told from a symbol by
; `typecase`, in quoted data as itself, and converted to and from symbols.
(define kind (subr pure (datum) string)
  (lambda (d)
    (typecase d
      (keyword k (string-append "#:" (symbol->string (keyword->symbol k))))
      (symbol s (string-append "'" (symbol->string s)))
      (else x "other"))))
(define first (->* (datum) string)
  (lambda (l) (typecase l (pair p (kind (car p))) (else x "none"))))
(define named (subr pure (symbol) keyword) (lambda (s) (symbol->keyword s)))
(string-append (kind #:sorted) " " (kind 'sorted) " " (first '(#:a b)) " " (first `(b #:a))
               (if (eq? (named 'sorted) #:sorted) " same" " other")
               (if (keyword? 'sorted) " keyword" " symbol"))
