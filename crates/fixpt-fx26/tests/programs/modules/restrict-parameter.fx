;; => 3
;; A file a function of a module restricted to what it uses, given a whole
;; one: its values the restricted type's, by name, the rest left out.
(let* ((core ((proj (load-module "../module-files/made-core.fx") @heap pure)))
       (t ((proj (load-input "../module-files/made-tickets.fx") @heap pure) core)))
  (begin ((with t next)) ((with t next)) ((with t next))))
