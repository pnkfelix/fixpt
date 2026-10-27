;; A function of a scheduler and the buffers made over it: the second's type
;; what `made-buffer.fx` makes of the first (`load-input-moduleof`).
(plambda ((ed region) (world effect))
  (lambda ((core (load-moduleof "made-core.fx" ed world))
           (buffer (load-input-moduleof "made-buffer.fx" ed world core)))
    (module
      (define twice (subr (read ed) ((select buffer buffer)) int)
        (lambda (b) (* 2 ((with buffer size) b))))
      (define ticket-of (subr pure ((select buffer buffer)) int)
        (lambda (b) ((with core number) (extract b t)))))))
