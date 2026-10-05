; The gap of `docs/research/soundness.md` 4.6, as a program: a composable
; continuation whose frames hold a counter at `@z`, a region named nowhere
; else, so that masking hides the prompt body's effects on it; the
; continuation gets out through `saved`, and is called twice, giving 12 and
; then 13. `again`'s effect names no `@z` though it reads and writes it:
; T3 does not hold as stated. What keeps it harmless: the counter is
; reachable only through the continuation, and every call of one has
; `goto` and `comefrom` on its tag's region, so nothing takes it for pure.
(define-effect keeps (maxeff (write @s) (alloc @s)))
(define-effect control (maxeff (goto @p) (comefrom @p)))
(define-type kont (composable int int keeps @p))
(define t (prompt-tag int int keeps @p) (make-continuation-prompt-tag))
(define saved (ref (listof kont @s) @s) (new nil))
(define grab (subr (maxeff control keeps (read (globals saved t))) () int)
  (lambda ()
    (let ((t t) (saved saved))
      (prompt t
        (let ((c (the (ref int @z) (new 0))))
          (+ ((proj (proj call-with-composable-continuation @p) int int keeps int keeps)
              (lambda ((k kont)) (begin (set saved (cons k nil)) 0))
              t)
             (begin (set c (+ (get c) 1)) (get c))))
        (lambda ((v int)) v)))))
(grab)
(define again (subr (maxeff control keeps (read @s) (read (globals saved t))) (int) int)
  (lambda (n) ((car (get saved)) n)))
(again 10)
(again 10)
