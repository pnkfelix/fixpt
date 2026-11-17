;; A file of a region parameter with macros (`binding-shapes.md`, step 4
;; (c)): each instance's count its own, which its macros name: `tick-once`
;; by another's template, `tick-ten` made by a use of `define-ticker`.
(module-parameters ((r region)))
(define-type tally int)
(define count (ref int r) (new 0))
(define tick (subr (maxeff (read r) (write r)) (int) int)
  (lambda (k) (begin (set count (+ (get count) k)) (get count))))
(define-syntax tick-once (macro (_ expr) expr) (syntax-rules ((_ e) (tick e))))
(define-syntax tick-twice (macro (_ expr) expr)
  (syntax-rules ((_ e) (let ((k e)) (begin (tick-once k) (tick-once k))))))
(define-syntax as-tally (macro (_ expr) expr) (syntax-rules ((_ e) (the tally e))))
(define-syntax define-ticker (macro (_ bvar) defn)
  (syntax-rules ((_ n) (define-syntax n (syntax-rules ((_) (tick-once 10)))))))
(define-ticker tick-ten)
