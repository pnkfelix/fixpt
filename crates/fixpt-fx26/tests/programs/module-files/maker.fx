;; A file of one expression, for `load-input` (`TODO.md` §68): a procedure
;; making a module of what it is given.
(lambda ((n int)) (module (define twice int (* 2 n))))
