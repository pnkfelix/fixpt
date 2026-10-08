;; => 6
;; Three layers of module files, each giving the one below its region;
;; the instances below reached through the top one (`(with p rd)`).
(define top ((proj (load-module "../module-files/layer3.fx") @q)))
(define p (with top p))
(define rd (with p rd))
(define-type cell (select rd cell))
(define thrice (with top thrice))
(define c (with rd c))
(define peek (with top peek))
(begin (thrice) (thrice) (peek c))
