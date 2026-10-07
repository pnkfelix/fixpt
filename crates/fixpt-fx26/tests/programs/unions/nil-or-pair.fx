; Accepted: "a pair, or none": `(union nil (pairof …))`, which `no-pair`
; and `cons` both fit, and `car` takes (checking for `nil`).
(define-type entry (union nil (pairof symbol int @r)))
(define* value (subr (read @r) (entry) int) (lambda (e) (if (null? e) 0 (cdr e))))
(+ (value (the entry no-pair)) (value (cons 'a 4)))
