;; ! an `include` uses `k`, which the module defines: an included module is made before its items
;; An included module is made before the module's items, and sees none of
;; them (`TODO.md` §69, §72): said so, the hidden `%include` not named.
(define m (module (include (module (define w int k))) (define k int 1)))
