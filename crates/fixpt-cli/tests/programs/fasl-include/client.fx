;; A client that includes the counter's load, as Heist's of `sat.fx`.
(hide (include (load-module "counter.fx")))
(define* bump-twice! (subr (maxeff (read @heap) (write @heap)) (counter) int)
  (lambda (c) (begin (bump! c) (bump! c))))
