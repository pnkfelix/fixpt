;; => 2
;; A product with names is bound to one name, its fields `extract`ed.
(tagcase (sum #:rect (product (#:w 1) (#:h 2))) (#:rect r (extract r #:h)))
