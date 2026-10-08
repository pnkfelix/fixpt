;; A file of signatures (`TODO.md` §68): no state, so any file may load it.
(define-type dep-sig
  (moduleof (val cat3 (subr pure (string string string) string)) (val limit int)))
