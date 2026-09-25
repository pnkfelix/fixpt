;;; The FX-26 run-time environment, as Scheme.
;;;
;;; Lowering (`lower.rs`) sends each standard FX-26 name either straight to
;;; the Scheme procedure of the same meaning (`car`, `+`, `null?`, `call/cc`,
;;; ...) or to one of these, where FX-26 and Scheme differ: FX-26's mutators
;;; return the unit value, a reference is a box, and the control operations
;;; take their arguments as procedures rather than as syntax.
;;;
;;; Every name here starts with `%fx26-`. A program's own names are lowered
;;; with an `fx:` prefix, so the two can never meet.

;;; ---- unit ----
;;; Written `#u`, as FX-87 writes it; the symbol `|#u|` prints that way.
(define %fx26-unit (string->symbol "#u"))

;;; ---- references ----
(define (%fx26-new v) (%make-box v))
(define (%fx26-get r) (%box-ref r))
(define (%fx26-set r v) (%box-set! r v) %fx26-unit)

;;; ---- pairs ----
(define (%fx26-set-car! p v) (set-car! p v) %fx26-unit)
(define (%fx26-set-cdr! p v) (set-cdr! p v) %fx26-unit)

;;; ---- delimited control ----
;;; A prompt is the `prompt` form, lowered to `call-with-continuation-prompt`
;;; directly. These are the constants.
(define (%fx26-make-prompt-tag) (make-continuation-prompt-tag 'fx26))
(define (%fx26-abort tag v) (abort-current-continuation tag v))
(define (%fx26-call/comp proc tag) (call-with-composable-continuation proc tag))

;;; ---- continuation marks ----
;;; A key is any value compared with `eq?`, so a fresh pair makes one.
(define (%fx26-make-mark-key) (list 'fx26-mark-key))
(define (%fx26-with-mark key v thunk) (with-continuation-mark key v (thunk)))
(define (%fx26-first-mark key default) (continuation-mark-set-first #f key default))
(define (%fx26-current-marks key)
  (continuation-mark-set->list (current-continuation-marks) key))
(define (%fx26-marks-of k key) (continuation-mark-set->list (continuation-marks k) key))

;;; ---- characters, strings, numbers ----
(define (%fx26-char-in? c s)
  (let loop ((i 0))
    (and (< i (string-length s)) (or (char=? c (string-ref s i)) (loop (+ i 1))))))
;; A number in `radix`, as a list of none or one.
(define (%fx26-parse-number s radix)
  (let ((n (string->number s radix))) (if n (list n) '())))
;; An exact non-negative integer in `radix`, or -1.
(define (%fx26-parse-int s radix)
  (let ((n (string->number s radix)))
    (if (and n (exact-integer? n) (>= n 0)) n -1)))

;;; ---- data ----
;;; A datum is the Scheme value itself; these build and test ones the
;;; ordinary procedures do not.
(define (%fx26-identity x) x)
(define (%fx26-bytevector items) (apply bytevector items))
(define (%fx26-byte? d) (and (exact-integer? d) (<= 0 d 255)))
