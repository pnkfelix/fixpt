;;; The reader and the parser loaded alone (`session.rs`'s `reader_text`,
;;; lowered: a session whose checker and compilers run as register code,
;;; and an eager reader): `reader.fx`, then this, where the whole front end
;;; has the conductor instead. One front end, so one parser, made here,
;;; and what Rust calls of it at top level, as the conductor re-exports
;;; its own program's (`conductor.fx`).

(define parser-top-module ((proj make-reader @s @e @m @c @p)))
(define read-text-at (with eager-reader-module read-text-at))
(define parse-program (with parser-top-module parse-program))
(define parser-exps-module (with parser-top-module parser-exps-module))
(define parser-of-top (with parser-exps-module parser-module))
(define loaded-files! (with parser-of-top loaded-files!))
(define includes-given! (with parser-of-top includes-given!))
(define loaded (with parser-of-top loaded))
(define macros-module (with parser-top-module macros-module))
(define imports-module (with parser-top-module imports-module))
(define standard-names! (with imports-module standard-names!))
(define expansions-made (with macros-module expansions-given))
(define macro-source (with macros-module source-of))
(define shapes-module (with parser-top-module shapes-module))
(define walk-module (with shapes-module walk-module))
(define program-walked
  (lambda ((text string))
    (let ((read (read-text text)))
      (if (null? read)
          (the (listof string acyclic) nil)
          ((with walk-module walked-forms) (car read))))))
(define program-shaped
  (lambda ((text string))
    (let ((read (read-text text)))
      (if (null? read)
          (the (listof string acyclic) nil)
          ((with shapes-module shaped-forms) (car read) (get loaded))))))
