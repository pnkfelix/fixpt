; docs/research/examples/conditions/handlers.fx written with the built-in
; `fx26:conditions.fx` (TODO.md §89): `raise` where the failure is,
; `with-handler` to choose what happens, `handle` for a restart.
(define c (load-module "fx26:conditions.fx"))
(define handle (with c handle))
(define with-handler (with c with-handler))
(define raise (with c raise))
(define* digit
  (poly ((k region) (eh effect))
    (subr (maxeff (read k) eh) ((mark-key (subr eh (char) int) k) char) int))
  (plambda ((k region) (eh effect))
    (lambda (key ch)
      (if (and (char>=? ch #\0) (char<=? ch #\9)) (- (char->integer ch) 48) (raise key ch)))))
(define* sum-over
  (poly ((e effect)) (subr (maxeff e spin) ((subr e (char) int) string int) int))
  (plambda ((e effect))
    (lambda (f s i)
      (if (>= i (string-length s)) 0 (+ (f (string-ref s i)) ((proj sum-over e) f s (+ i 1)))))))
;; What the bodies below do: the instantiation of `with-handler` and
;; `handle` must say it, as inference does not reach into an argument
;; that is itself polymorphic (rank 2).
(define-effect bodies (maxeff (read (globals digit raise sum-over)) spin))
;; A character that is no digit counts 0: the handler gives a value.
(define* lenient-sum (subr (maxeff (read (globals digit sum-over with-handler)) spin) (string) int)
  (lambda (s)
    ((proj with-handler char int int bodies pure)
                  (lambda ((ch char)) 0)
                  (plambda ((k region))
                    (lambda ((key (mark-key (subr pure (char) int) k)))
                      (sum-over (lambda ((ch char)) (digit key ch)) s 0))))))
;; One makes the whole -1: the handler escapes to a `handle`, a restart.
(define* strict-sum
  (subr (maxeff (read (globals digit sum-over with-handler handle)) spin) (string) int)
  (lambda (s)
    ((proj handle int string (maxeff bodies (read (globals with-handler))))
            (plambda ((r region))
              (lambda ((t (escape-tag int string r)))
                ((proj with-handler char int int bodies (goto r))
                 (lambda ((ch char)) (escape t "no digit"))
                              (plambda ((k region))
                                (lambda ((key (mark-key (subr (goto r) (char) int) k)))
                                  (sum-over (lambda ((ch char)) (digit key ch)) s 0))))))
            (lambda ((why string)) -1))))
(list (lenient-sum "1x3") (strict-sum "123") (strict-sum "1x3"))
