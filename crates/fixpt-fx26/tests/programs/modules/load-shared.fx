;; => 1
;; Every load of a file is one value, and so are its abstract types: a file
;; may offer an operation on another's, which a program that loaded that one
;; itself gives its values to (`docs/research/derived-signatures.md`, Q2).
(define c (load-module "../module-files/shared-counter.fx"))
(define u (load-module "../module-files/shared-twice.fx"))
((with u bump) (with c zero))
