;; => 57
;; `module-parameters` of modules (Heist's, 2026-10-28): each file a
;; function of the modules it is given, their names its own, hidden; its
;; expressions run as it is made (11); typed by `load-moduleof` as any
;; file is; with a region, the `plambda` first.
(define m-base (load-module "../module-files/mp-base.fx"))
(define m-buffer ((load-module "../module-files/mp-buffer.fx") m-base))
(define m-mixed ((proj (load-module "../module-files/mp-mixed.fx") @q) m-base))
(define* seen-of (subr (read @c) ((load-moduleof "../module-files/mp-buffer.fx" m-base)) int)
  (lambda (m) ((with m seen))))
(+ (+ (seen-of m-buffer) (extract ((with m-buffer origin)) y))
   (get ((with m-mixed cell) 21)))
