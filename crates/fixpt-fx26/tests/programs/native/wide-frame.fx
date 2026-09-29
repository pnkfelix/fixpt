;;; A procedure whose frame is too large for one `stp` (70 values live
;;; across a call, and a collection there): its frame is made in two
;;; instructions, and, too large for a stack map's mask, traced whole.
(define* id (subr (maxeff (alloc @heap) (read @heap)) (int) int) (lambda (x) (car (cons x (the (listof int @heap) nil)))))
(define* wide (subr (maxeff (alloc @heap) (read @heap) (read (globals id))) (int) int)
  (lambda (x)
    (let* ((v0 (+ x 0)) (v1 (+ x 1)) (v2 (+ x 2)) (v3 (+ x 3)) (v4 (+ x 4)) (v5 (+ x 5)) (v6 (+ x 6)) (v7 (+ x 7)) (v8 (+ x 8)) (v9 (+ x 9)) (v10 (+ x 10)) (v11 (+ x 11)) (v12 (+ x 12)) (v13 (+ x 13)) (v14 (+ x 14)) (v15 (+ x 15)) (v16 (+ x 16)) (v17 (+ x 17)) (v18 (+ x 18)) (v19 (+ x 19)) (v20 (+ x 20)) (v21 (+ x 21)) (v22 (+ x 22)) (v23 (+ x 23)) (v24 (+ x 24)) (v25 (+ x 25)) (v26 (+ x 26)) (v27 (+ x 27)) (v28 (+ x 28)) (v29 (+ x 29)) (v30 (+ x 30)) (v31 (+ x 31)) (v32 (+ x 32)) (v33 (+ x 33)) (v34 (+ x 34)) (v35 (+ x 35)) (v36 (+ x 36)) (v37 (+ x 37)) (v38 (+ x 38)) (v39 (+ x 39)) (v40 (+ x 40)) (v41 (+ x 41)) (v42 (+ x 42)) (v43 (+ x 43)) (v44 (+ x 44)) (v45 (+ x 45)) (v46 (+ x 46)) (v47 (+ x 47)) (v48 (+ x 48)) (v49 (+ x 49)) (v50 (+ x 50)) (v51 (+ x 51)) (v52 (+ x 52)) (v53 (+ x 53)) (v54 (+ x 54)) (v55 (+ x 55)) (v56 (+ x 56)) (v57 (+ x 57)) (v58 (+ x 58)) (v59 (+ x 59)) (v60 (+ x 60)) (v61 (+ x 61)) (v62 (+ x 62)) (v63 (+ x 63)) (v64 (+ x 64)) (v65 (+ x 65)) (v66 (+ x 66)) (v67 (+ x 67)) (v68 (+ x 68)) (v69 (+ x 69)) (w (id 0)))
      (+ w (+ v69 (+ v68 (+ v67 (+ v66 (+ v65 (+ v64 (+ v63 (+ v62 (+ v61 (+ v60 (+ v59 (+ v58 (+ v57 (+ v56 (+ v55 (+ v54 (+ v53 (+ v52 (+ v51 (+ v50 (+ v49 (+ v48 (+ v47 (+ v46 (+ v45 (+ v44 (+ v43 (+ v42 (+ v41 (+ v40 (+ v39 (+ v38 (+ v37 (+ v36 (+ v35 (+ v34 (+ v33 (+ v32 (+ v31 (+ v30 (+ v29 (+ v28 (+ v27 (+ v26 (+ v25 (+ v24 (+ v23 (+ v22 (+ v21 (+ v20 (+ v19 (+ v18 (+ v17 (+ v16 (+ v15 (+ v14 (+ v13 (+ v12 (+ v11 (+ v10 (+ v9 (+ v8 (+ v7 (+ v6 (+ v5 (+ v4 (+ v3 (+ v2 (+ v1 (+ v0 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(wide 1)
;; Many times, so that collections come while its frame is on the stack.
(define* run (subr (maxeff (alloc @heap) (read @heap) (read (globals wide)) spin) (int int) int)
  (lambda (i acc) (if (= i 0) acc (run (- i 1) (+ acc (wide i))))))
(run 1000 0)
