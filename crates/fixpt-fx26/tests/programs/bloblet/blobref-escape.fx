;; ! would outlive its region
;; A blobref keeps its owner, and so its owner's region: one into a bloblet
;; of `letrena r` does not leave it.
(letrena r
  (let ((b (the (bloblet (fields) r) (make-bloblet 8))))
    (the (blobref (bloblet (fields) r) f64) (blobref-at b 0))))
