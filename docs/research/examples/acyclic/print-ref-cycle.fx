;;; Crashes `fixpt eval` with a stack overflow: printing a cycle through a
;;; ref. No acyclic data is involved; a cycle through pairs alone prints
;;; with datum labels (`acyclic-shallow-and-deep.md` §3).
(define-type wcell (ref (listof wcell @w) @r))
(define c wcell (new (the (listof wcell @w) (list))))
(set c (list c))
c
