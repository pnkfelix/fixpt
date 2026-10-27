;; => 0
;; In a module file, an included module's types are in scope by name, as in
;; a `module` (Heist's problem D: the FX-26 checker had refused them).
(define m (load-module "../module-files/include-in-file.fx"))
(begin (with m z) 0)
