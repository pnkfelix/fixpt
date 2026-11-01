;; => 20
;; A deep handler that resumes (Heist's R4, `TODO.md` §211, 6): user code,
;; apart and polymorphic in the region of the tag it is given, asks twice;
;; each ask captures the rest of the code and aborts to the handler with it,
;; which resumes it with 10 under a prompt of the same tag, so that the
;; next ask comes back to it too. The prompts around a resumed continuation
;; do not delimit (the continuation is free, and its type names the
;; region), so the handler says the control on `@ev` in its type, and the
;; `letregion` that made the region and the tag masks it: the turn does
;; nothing another could see, and runs in an `attempt`.
(define-type (k-of (r region)) (composable int int (read @globals) r))
(define-type (tag-of (r region)) (prompt-tag int (k-of r) (read @globals) r))
(define ask (poly ((r region)) (subr (maxeff (goto r) (comefrom r)) ((tag-of r)) int))
  (plambda ((r region))
    (lambda (tag)
      ((proj (proj call-with-composable-continuation r)
             int (k-of r) (read @globals) int (maxeff (goto r) (comefrom r)))
       (lambda ((k (k-of r)))
         ((proj (proj abort-current-continuation r) int (k-of r) (read @globals)) tag k))
       tag))))
(define user
  (poly ((r region)) (subr (maxeff (goto r) (comefrom r) (read (globals ask))) ((tag-of r)) int))
  (plambda ((r region)) (lambda (tag) (+ ((proj ask r) tag) ((proj ask r) tag)))))
(define turn (subr (maxeff spin (read @globals)) () int)
  (lambda ()
    (letregion ev
      (let ((tag ((proj (proj make-continuation-prompt-tag @ev) int (k-of @ev) (read @globals)))))
        (letrec ((handle
                   (subr (maxeff spin (goto @ev) (comefrom @ev) (read @globals))
                         ((subr (maxeff (goto @ev) (comefrom @ev) (read @globals)) () int)) int)
                   (lambda (th)
                     (prompt tag (th) (lambda ((k (k-of @ev))) (handle (lambda () (k 10))))))))
          (handle (lambda () ((proj user @ev) tag))))))))
(attempt (turn) (lambda ((m string)) -1))
