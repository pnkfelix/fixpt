;; A handler that resumes, declared without the control on its region, as
;; though its prompts masked it: they do not (a resumed continuation, free
;; in the body, names the region), and the refusal says why, and what does
;; mask it (Heist's, `TODO.md` §211). Not about `spin`, which its types
;; say: no "it may not end".
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
                   (subr (maxeff spin (read @globals))
                         ((subr (maxeff (goto @ev) (comefrom @ev) (read @globals)) () int)) int)
                   (lambda (th)
                     (prompt tag (th) (lambda ((k (k-of @ev))) (handle (lambda () (k 10))))))))
          (handle (lambda () ((proj user @ev) tag))))))))
(attempt (turn) (lambda ((m string)) -1))
