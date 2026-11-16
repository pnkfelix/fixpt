;; A module file that uses its own macros (Heist's (a)): each template's
;; free name is this file's item, hidden or not, or a standard binding,
;; whatever a binder around the use calls the same; that binder is renamed.
(define limit int 10)
(hide (define secret int 7))
(define-syntax capped (macro (_ expr) expr)
  (syntax-rules ((_ e) (let ((v e)) (if (< v limit) v limit)))))
(hide (define-syntax plus-secret (macro (_ expr) expr) (syntax-rules ((_ e) (+ e secret)))))
(define-syntax define-twice (macro (_ bvar expr) defn)
  (syntax-rules ((_ n e) (begin (define raw e) (define n (+ (capped raw) (capped raw)))))))
(define a int (capped 3))
;; The use's `limit`, 100, is not the template's, 10.
(define b int (let ((limit 100)) (capped limit)))
;; The parameter `secret` is 1, the file's hidden one 7.
(define c int ((lambda ((secret int)) (plus-secret secret)) 1))
(define-twice d 4)
;; A macro this file's own use of a macro that defines one makes (TODO §287), used by a later
;; form: its `limit` the file's, 10.
(define-syntax define-clamper (macro (_ bvar) defn)
  (syntax-rules ((_ n) (define-syntax n (syntax-rules ((_ x) (if (> x limit) limit x)))))))
(define-clamper clamp)
(define clamped int (clamp 50))
