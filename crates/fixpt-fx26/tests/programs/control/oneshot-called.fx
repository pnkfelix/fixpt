; A one-shot continuation (`TODO.md` §98) is called as a composable one
; is, with the same control effects on its tag's region; and it can stand
; where a subroutine is wanted, as a composable one can. Checked, not
; called: its value is 0.
(define called
  (lambda ((k (oneshot int int pure @p)))
    ((lambda ((f (subr (maxeff (goto @p) (comefrom @p)) (int) int))) (f 1)) k)))
0
