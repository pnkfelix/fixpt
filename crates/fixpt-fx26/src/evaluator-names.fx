;;; The evaluator's primitives, by name: which standard names it has
;;; (`evaluator.fx`, `standard`), and which of its dispatchers runs each.
;;; Before `evaluator.fx`, which uses `primitive?`.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what `evaluator.fx` uses re-exported after it.
(define evaluator-names (module
;; The primitives the evaluator has, between spaces.
(define primitive-names string
  (k-cat4 " + - * = < > <= >= not modulo quotient "
          (k-cat3 "cons rcons rnew rmake-array rmake-icell car cdr null? set-car! set-cdr! "
                  "new get set make-icell icell-put! icell-get char=? char->integer integer->char "
                  "string-append string-length string-ref string=? string->symbol symbol->string ")
          "symbol=? eq? char->string make-array array-ref array-set! array-length "
          (k-cat3 "make-continuation-prompt-tag abort-current-continuation "
                  "call-with-composable-continuation make-continuation-mark-key with-mark "
                  "first-mark current-marks marks-of cwcc %vlambda apply list ")))
;; What the ports wrote themselves, as `ev-std-prim` does them.
(define std-primitive-names string
  (k-cat3 " remainder zero? max min bool=? char<? char<=? char>? char>=? char-upcase "
          "string<? string<=? string>? string>=? error string-hash symbol-name-hash "
          "pair? int? char? bool? string? symbol? procedure? array? "))
;; `f64`'s, as `ev-f64-prim` does them.
(define f64-primitive-names string
  (k-cat4 " f64+ f64- f64* f64/ f64-min f64-max f64-atan2 f64-expt f64< f64<= f64> f64>= f64= "
          "f64-nan? f64-infinite? f64-finite? int->f64 f64->int f64->string string->f64 "
          "f64-abs f64-neg f64-sqrt f64-floor f64-ceiling f64-truncate f64-round "
          "f64-exp f64-log f64-sin f64-cos f64-tan f64-asin f64-acos f64-atan "))
;; `f32`'s, as `ev-f32-prim` does them.
(define f32-primitive-names string
  (k-cat4 " f32+ f32- f32* f32/ f32-min f32-max f32< f32<= f32> f32>= f32= "
          "f32-abs f32-neg f32-sqrt f32-floor f32-ceiling f32-truncate f32-round "
          "f32-nan? f32-infinite? f32-finite? "
          (k-cat3 "int->f32 f32->int f32->string f32->f64 f64->f32 int->string "
                  "make-flatarray flatarray-ref flatarray-set! flatarray-length "
                  "i32-flat u32-flat i64-flat u64-flat f32-flat f64-flat ")))

;; Whether `needle` occurs in `hay` from position `i` on.
(define occurs? (subr (maxeff (read @globals) spin) (string string int) bool)
  (lambda (needle hay i)
    (and (<= (+ i (string-length needle)) (string-length hay))
         (or (string=? (substring hay i (+ i (string-length needle))) needle)
             (occurs? needle hay (+ i 1))))))

(define primitive? (subr (maxeff (read @globals) spin) (string) bool)
  (lambda (n)
    (let ((padded (string-append " " (string-append n " "))))
      (or (occurs? padded primitive-names 0)
          (or (occurs? padded f64-primitive-names 0)
              (or (occurs? padded f32-primitive-names 0)
                  (occurs? padded std-primitive-names 0)))))))))

(define primitive? (with evaluator-names primitive?))
