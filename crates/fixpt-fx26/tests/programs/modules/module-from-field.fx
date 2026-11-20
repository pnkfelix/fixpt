;; => 14
;; A module kept in a product's field, in a cell, opened where it is read
;; (Heist's should-work note, entry 17): the field's type says the module's
;; names, `(get (extract h th))`'s shape a `sig`'s; and so does a product
;; made untyped, `(new m)`'s cell of `m`'s, a field labelled by a keyword
;; (in a `let`: a top-level one's region made up is exported unlike by the
;; two checkers, TODO §305).
(define-type sig (moduleof (abs st type) (val state st) (val peek (subr (read @heap) (st) int))))
(define m sig (module (define-type st (ref int @heap)) (define state st (new 7))
                      (define peek (subr (read @heap) (st) int) (lambda ((s st)) (get s)))))
(define-type holder (productof (th (ref sig @heap))))
(define h holder (product (th (new m))))
(+ (let ((th (get (extract h th)))) (with th (peek state)))
   (let* ((h2 (product (#:th (new m)))) (th (get (extract h2 th)))) (with th (peek state))))
