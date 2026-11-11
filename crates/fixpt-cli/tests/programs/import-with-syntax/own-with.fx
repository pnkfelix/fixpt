;; A file's own macro used where a `with` may give a name its template
;; names: not yet (`binding-shapes.md`, step 3, stage 5).
(define limit int 10)
(define m (module (define limit int 100)))
(define-syntax get-limit () (syntax-rules () ((_) limit)))
(define x int (with m (get-limit)))
