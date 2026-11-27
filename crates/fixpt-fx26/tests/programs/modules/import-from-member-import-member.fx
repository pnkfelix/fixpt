;; => 41
;; A file over a bundle (`module-files/ifm-ab.fx`) taking names of a module
;; the bundle holds by `import` (Heist's `fixpt-import-from-member.md`,
;; 2026-11-27): the client's `import-member`.
(define m-ab ((load-module "../module-files/ifm-ab.fx")))
(define m-c ((load-module "../module-files/ifm-c-import-member.fx") m-ab))
((with m-c x41))
