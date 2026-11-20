;; A load whose procedures a client includes (`fasl.rs`'s
;; `a_clients_fasl_links_what_it_includes`), as Heist's of `sat.fx`: a
;; counter in the heap, no state of the module's own.
(define-type counter (ref int @heap))
(define* make-counter (subr (alloc @heap) () counter) (lambda () (new 0)))
(define* bump! (subr (maxeff (read @heap) (write @heap)) (counter) int)
  (lambda (c) (begin (set c (+ (get c) 1)) (get c))))
