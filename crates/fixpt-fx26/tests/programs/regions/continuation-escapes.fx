; Rejected: a continuation captured inside the region, up to a prompt
; outside it, could be resumed after the region is gone.
(define t (prompt-tag int int pure @p) (make-continuation-prompt-tag))
(let ((capture (proj call-with-composable-continuation @p)))
  (prompt t
    (letreap r
      ((proj capture int int pure int (maxeff (goto @p) (comefrom @p)))
       (lambda ((k (composable int int pure @p))) 1)
       t))
    (lambda ((v int)) v)))
