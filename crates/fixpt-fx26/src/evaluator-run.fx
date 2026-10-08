;;; The evaluator written in FX-26: its values shown, and its entry points.
;;; After `evaluator.fx`, whose values and state it reads.

;;; --------------------------------------------------------------- showing
;;; As Scheme's writer shows what the lowered program computes.

;; How Scheme writes a bloblet of `n` fields and `m` bytes.
(define show-bloblet (subr (read @globals) (int int) string)
  (lambda (n m) (k-cat5 "#<bloblet " (int->string n) " fields " (int->string m) " bytes>")))

;; A value as Scheme would write it. A list may be cyclic (built with
;; `set-cdr!`), and values have no identity to compare here, so the walk
;; has fuel: past it, `…`. The car of a pair gets half what is left, so a
;; cycle through cars and cdrs alike stays bounded too.
(define-rec
  (show-val (subr (maxeff (read @globals) (read @v) spin) (val) string)
    (lambda (v) (show-val-in v 10000)))
  (show-val-in (subr (maxeff (read @globals) (read @v) spin) (val int) string)
    (lambda (v fuel)
      (tagcase v
        (v-int (n) (int->string n))
        (v-bool (b) (if b "#t" "#f"))
        (v-str (s) (string-append "\"" (string-append s "\"")))
        (v-char (c) (string-append "#\\" (char->string c)))
        (v-f64 (x) (f64->string x))
        (v-f32 (x) (f32->string x))
        (v-sym (s) (symbol->string s))
        (v-unit () "#u")
        (v-nil () "()")
        (v-pair (p) (if (<= fuel 0) "…" (k-cat3 "(" (show-items p fuel) ")")))
        (v-ref (r) "#<box>")
        (v-icell (c) "#<bloblet 3 fields 0 bytes>")
        (v-array (a) (show-bloblet (+ 1 (array-length a)) 0))
        (v-blob (fs bs) (show-bloblet (+ 1 (array-length fs)) (array-length bs)))
        (v-product (fs) (k-cat3 "#<product of " (int->string (length-pairs fs)) ">"))
        (v-sum (t x) (k-cat3 "#<sum " (symbol->string t) ">"))
        (v-clo (ps body e) "#<procedure>")
        (v-vsubr (g) "#<procedure>")
        (v-prim (n) "#<procedure>")
        (v-tag (t) "#<prompt-tag>")
        (v-cont (k) "#<continuation>")
        (v-esc (k) "#<continuation>")
        (v-key (k) "#<mark-key>"))))
  ;; A list's elements, space-separated, and a dotted tail.
  (show-items (subr (maxeff (read @globals) (read @v) spin) (vpair int) string)
    (lambda (p fuel)
      (let ((head (show-val-in (bloblet-ref p 0) (quotient fuel 2))) (tail (bloblet-ref p 1)))
        (tagcase tail
          (v-nil () head)
          (v-pair (q)
            (if (<= fuel 1)
                (string-append head " …")
                (k-cat3 head " " (show-items q (- fuel 1)))))
          (else x (k-cat3 head " . " (show-val-in tail (- fuel 1)))))))))

;; A whole program begins with no globals, and no names kept.
(define ev-begin! (subr stores (k-reshape-list k-with-list) unit)
  (lambda (rs ws) (begin (set genv nil) (set ev-keep nil) (set ev-reshapes rs) (set ev-withs ws))))
;; The entry point for a program the checker written in FX-26 checked: what
;; it runs (`checked-tops`, under redefinition), run; its value shown, or
;; its error. A whole program, as each is.
(define run-checked (subr (maxeff evals (read @t) spin) ((listof k-run acyclic)) string)
  (lambda (runs)
    (tagcase (begin (ev-begin! (get k-reshapes) (get k-with-vals)) (eval-runs runs))
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m)))))

;; The entry point: a program's trees, run; its value shown, or its error.
(define run-program (subr (maxeff evals spin) ((listof top acyclic)) string)
  (lambda (tops)
    (tagcase (begin (ev-begin! nil nil) (eval-program tops))
      (ev-ok (v) (show-val v))
      (ev-err (m) (string-append "!! " m)))))
