;; An expression that only reads, among a module's items: it does nothing.
(module-parameters ((m-base (load-moduleof "mp-base.fx") #:unqualified)))
(twice 3)
