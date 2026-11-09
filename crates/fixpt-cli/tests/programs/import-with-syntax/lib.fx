;; A file's macros, which `import-with-syntax` brings: `clamp`, `clamp2`;
;; `twice` hidden, which `clamp2`'s template still uses. Each template's
;; names are this file's: `limit` its own, whatever the importer's is.
(define limit int 10)
(hide (define secret int 7))
(define-syntax clamp (expr) (syntax-rules () ((_ e) (let ((v e)) (if (> v limit) limit v)))))
(hide (define-syntax twice (expr) (syntax-rules () ((_ e) (let ((w e)) (+ w w))))))
(define-syntax clamp2 (expr) (syntax-rules () ((_ e) (twice (clamp e)))))
