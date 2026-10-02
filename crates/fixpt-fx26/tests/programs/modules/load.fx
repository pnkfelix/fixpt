;; => 2
;; A file is a module (M7): `load-module` reads its items, and its type is
;; the file's interface.
(define c (load-module "../module-files/counter.fx"))
(with c (value (inc (inc zero))))
