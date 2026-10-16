; Nor is a composable continuation a one-shot one (`TODO.md` §98): where
; the type says one-shot, a second resume fails, and a composable one's
; would not. Rejected.
(lambda ((c (composable int int pure @p)))
  ((lambda ((k (oneshot int int pure @p))) 1) c))
