;;; Words allocated in one arena, read inside the body that owns it.
;;; MOCK: `place-words-allocated` is the proposal (stage 3), stubbed; its
;;; type takes the place as a value, as `rcons` does, and reads it.
(define-effect observes (maxeff (read @telemetry) (write @telemetry)))
(define fake (ref int @telemetry) (new 0))
(define* place-words-allocated
  (poly ((p place)) (subr (maxeff (read p) observes) ((place p)) nat))
  (plambda ((p place))
    (lambda ((q (place p))) (begin (set fake (get fake)) (confirm-nat (get fake) (n n) 0)))))

;; Build n pairs in an arena and report how many words that took. `(read r)`
;; and `(alloc r)` are masked when the arena ends; `observes` is not.
(define* arena-cost (subr (maxeff observes spin) (int) int)
  (lambda (n)
    (letrena r
      (letrec ((build (subr (maxeff (alloc r) spin) (int (listof int r)) (listof int r))
                 (lambda (i acc) (if (= i 0) acc (build (- i 1) (rcons r i acc))))))
        (let* ((w0 (place-words-allocated r))
               (xs (build n nil))
               (w1 (place-words-allocated r)))
          (- w1 w0))))))

(arena-cost 1000)   ; 0 with the stub; the proposal's answer is 3000 or so
