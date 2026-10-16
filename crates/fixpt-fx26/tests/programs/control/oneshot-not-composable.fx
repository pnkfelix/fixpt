; A one-shot continuation (`TODO.md` §98) is not a composable one: a
; procedure that takes a composable continuation may resume it twice, so it
; is not given a one-shot one. Rejected.
(lambda ((k (oneshot int int pure @p)))
  ((lambda ((c (composable int int pure @p))) 1) k))
