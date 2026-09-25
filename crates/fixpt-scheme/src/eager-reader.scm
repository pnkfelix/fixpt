;;; The eager reader: an R7RS reader, written in Scheme, fed one character at
;;; a time.
;;;
;;; Olin Shivers, "Eager parsing and user interaction with call/cc": parse as
;;; the characters arrive, so a mistake is caught at the keystroke that makes
;;; it, and make backing up cheap by keeping a continuation per character.
;;; Here the continuations are *composable*, captured up to a prompt of the
;;; reader's own, which is exactly the shape of the job: when the parser needs
;;; a character it captures "the rest of the parse" and returns it to whoever
;;; is typing. Feeding the next character resumes that continuation. Every one
;;; it hands back is a checkpoint, and backspace is going back to the one
;;; before.
;;;
;;; Two disciplines make that safe:
;;;
;;; * **Nothing is mutated.** A checkpoint may be resumed more than once --
;;;   backspace, then a different character -- and a continuation is a copy of
;;;   the machine but the heap is shared, so the parser keeps all its state in
;;;   arguments and results. Lookahead is *passed along*, not pushed back:
;;;   every reading procedure takes the next character and returns the one
;;;   after what it read.
;;;
;;; * **The parser says where it is, in continuation marks.** Each construct
;;;   marks its frame with what it is reading, and a list re-marks itself in
;;;   tail position with the elements read so far. So a suspended parse's marks
;;;   *are* its stack: "inside a list after `vector-ref` and `(make-vector 3
;;;   0)`", read out with `continuation-marks` and nothing else.
;;;
;;; This is the Scheme profile only. Datum labels (`#0=`) are not supported.
;;; The Rust reader in `fixpt-read` is the reference, and `tests/eager.rs`
;;; reads the same inputs with both and requires the same data.

(define %eager-tag (make-continuation-prompt-tag 'eager-reader))
(define %eager-key (list 'eager-reader-context))

;;; ------------------------------------------------------------- the states
;;; What a feed returns. `need`: waiting for a character; `error`: this
;;; character is wrong in a way more input cannot fix.

(define-record-type %eager-state
  (%make-eager-state kind k position data message)
  eager-state?
  (kind eager-state-kind)            ; need | error
  (k %eager-state-k)                 ; the rest of the parse, when kind is need
  (position eager-state-position)    ; characters consumed so far
  (data %eager-state-data)           ; complete top-level data, newest first
  (message eager-state-message))     ; for errors

;; Suspend for the next character. `pos` is how many have been read, and
;; `data` the complete top-level data so far, both threaded through from
;; `eager-start` -- nothing is kept in a variable.
(define (%next-char pos data)
  (call-with-composable-continuation
   (lambda (k)
     (abort-current-continuation
      %eager-tag
      (%make-eager-state 'need k pos data #f)))
   %eager-tag))

(define (%eager-run thunk)
  (call-with-continuation-prompt thunk %eager-tag (lambda (state) state)))

;;; The reading procedures thread a *cursor*: `(c pos data)` -- the lookahead
;;; character, how many characters have been consumed, and the top-level data.
;;; `(%advance cur)` consumes the lookahead and waits for the next.
;;;
;;; A construct that ends on a closing character -- `)`, `"`, `|#` -- does
;;; *not* wait for the character after it: it returns a cursor whose `c` is #f,
;;; and whoever looks next fetches it (`%need`). That puts the wait *outside*
;;; the construct's marked extent, so a form is seen as finished the moment
;;; its last character arrives, not one character later.

(define (%cur-char cur) (car cur))
(define (%cur-pos cur) (cadr cur))
(define (%cur-data cur) (caddr cur))
(define (%advance cur)
  (let ((pos (+ (%cur-pos cur) 1)) (data (%cur-data cur)))
    (list (%next-char pos data) pos data)))

(define (%consumed cur)
  (list #f (+ (%cur-pos cur) 1) (%cur-data cur)))

(define (%need cur)
  (if (%cur-char cur)
      cur
      (list (%next-char (%cur-pos cur) (%cur-data cur)) (%cur-pos cur) (%cur-data cur))))

(define (%fail cur message)
  (%fail-at cur (%cur-pos cur) message))

(define (%fail-at cur pos message)
  (abort-current-continuation
   %eager-tag
   (%make-eager-state 'error #f pos (%cur-data cur) message)))

(define-syntax %marking
  (syntax-rules ()
    ((_ what body) (with-continuation-mark %eager-key what body))))

;;; ------------------------------------------------------------- the driver

;; A reader with nothing read yet.
(define (eager-start)
  (%eager-run
   (lambda ()
     (%read-top (list (%next-char 0 '()) 0 '())))))

;; Feed one character to a waiting state, giving the next state. States are
;; values: feeding the same state twice gives two independent parses.
(define (eager-feed state ch)
  (if (eq? (eager-state-kind state) 'need)
      (%eager-run (lambda () ((%eager-state-k state) ch)))
      state))

;; The complete top-level data read so far, in order.
(define (eager-state-data state) (reverse (%eager-state-data state)))

;; What the suspended parse is in the middle of, innermost first. Each entry
;; is a list whose head says what it is:
;;   (top)                        between data at the top level
;;   (list start close items)     a list, with the elements read so far,
;;                                newest first -- kept that way so that
;;                                re-marking per element stays O(1)
;;   (dotted start close items)   after a list's `.`
;;   (string start) (symbol start) (atom start) (char start) (hash start)
;;   (comment start) (block-comment start) (datum-comment start)
;;   (abbrev start name)          after ' ` , or ,@
(define (eager-context state)
  (if (eq? (eager-state-kind state) 'need)
      (continuation-mark-set->list
       (continuation-marks (%eager-state-k state) %eager-tag)
       %eager-key)
      '()))

;; `complete` when everything fed so far reads as whole data, `incomplete`
;; when it stopped partway through one, `error` when it is wrong in a way more
;; input cannot fix.
(define (eager-status state)
  (cond ((eq? (eager-state-kind state) 'error) 'error)
        ((let loop ((ctx (eager-context state)))
           (or (null? ctx)
               (and (memq (caar ctx) '(top comment)) (loop (cdr ctx)))))
         'complete)
        (else 'incomplete)))

;; If the last thing read inside the innermost open list is a `,help` hole,
;; the characters that would close every open list, innermost first, so the
;; REPL can answer the hole while the form is still being typed. Otherwise #f:
;; the hole must be the newest element, and everything open must be a list
;; (or a vector, which a list also closes), not a string or a comment.
(define (eager-hole-closers state)
  (let ((ctx (eager-context state)))
    (and (pair? ctx)
         (eq? (caar ctx) 'list)
         (let ((items (list-ref (car ctx) 3)))
           (and (pair? items) (%hole? (car items))))
         (let loop ((ctx ctx) (acc '()))
           (if (null? ctx)
               #f
               (case (caar ctx)
                 ((top) (list->string (reverse acc)))
                 ((list dotted) (loop (cdr ctx) (cons (list-ref (car ctx) 2) acc)))
                 ((hash) (loop (cdr ctx) acc))
                 (else #f)))))))

(define (%hole? d)
  (and (pair? d) (eq? (car d) 'unquote)
       (pair? (cdr d)) (memq (cadr d) '(help ?))
       (null? (cddr d))))

;;; --------------------------------------------------------------- top level

(define (%read-top cur)
  (let loop ((cur cur))
    (%marking '(top)
      (let ((cur (%skip-atmosphere cur)))
        (let-values (((d cur) (%read-datum cur)))
          (loop (list (%cur-char cur) (%cur-pos cur) (cons d (%cur-data cur)))))))))

;;; -------------------------------------------------------------- atmosphere

(define (%delimiter? c)
  (or (char-whitespace? c)
      (memv c '(#\( #\) #\[ #\] #\" #\; #\' #\` #\,))))

;; Whitespace and comments. Returns the cursor at the next meaningful
;; character. `#;` reads a datum and throws it away.
(define (%skip-atmosphere cur)
  (let* ((cur (%need cur)) (c (%cur-char cur)))
    (cond ((char-whitespace? c) (%skip-atmosphere (%advance cur)))
          ((char=? c #\;) (%skip-atmosphere (%line-comment cur)))
          ((char=? c #\#)
           (let ((start (%cur-pos cur)) (next (%advance cur)))
             (case (%cur-char next)
               ((#\|) (%skip-atmosphere (%block-comment (%advance next) start 1)))
               ((#\;)
                (%skip-atmosphere
                 (%marking (list 'datum-comment start)
                   (let-values (((d cur) (%read-datum (%skip-atmosphere (%advance next)))))
                     cur))))
               ;; Not atmosphere after all: hand the `#` and what follows to
               ;; the datum reader, which is why the cursor carries both.
               (else (list #\# start (%cur-data cur) next)))))
          (else cur))))

(define (%line-comment cur)
  (%marking (list 'comment (%cur-pos cur))
    (let loop ((cur (%advance cur)))
      (if (char=? (%cur-char cur) #\newline)
          (%consumed cur)
          (loop (%advance cur))))))

;; `#| … |#`, nesting.
(define (%block-comment cur start depth)
  (%marking (list 'block-comment start)
    (let ((c (%cur-char cur)))
      (cond ((char=? c #\|)
             (let ((next (%advance cur)))
               (if (char=? (%cur-char next) #\#)
                   (if (= depth 1)
                       (%consumed next)
                       (%block-comment (%advance next) start (- depth 1)))
                   (%block-comment next start depth))))
            ((char=? c #\#)
             (let ((next (%advance cur)))
               (if (char=? (%cur-char next) #\|)
                   (%block-comment (%advance next) start (+ depth 1))
                   (%block-comment next start depth))))
            (else (%block-comment (%advance cur) start depth))))))

;;; A cursor that `%skip-atmosphere` produced on seeing `#` followed by
;;; something else carries that something as a fourth element: the `#` has
;;; been consumed, and so has the character after it.
(define (%hash-pending? cur) (pair? (cdddr cur)))

;;; ------------------------------------------------------------------ datum
;;; Every reader returns two values: the datum, and the cursor after it.

(define (%read-datum cur)
  (let ((cur (%need cur)))
  (if (%hash-pending? cur)
      (%read-hash (cadr cur) (cadddr cur))
      (let ((c (%cur-char cur)) (start (%cur-pos cur)))
        (cond ((char=? c #\() (%read-list (%advance cur) start #\)))
              ((char=? c #\[) (%read-list (%advance cur) start #\]))
              ((or (char=? c #\)) (char=? c #\]))
               (%fail cur (string-append "unbalanced `" (string c) "`")))
              ((char=? c #\") (%read-string (%advance cur) start))
              ((char=? c #\#) (%read-hash start (%advance cur)))
              ((char=? c #\') (%read-abbrev (%advance cur) start 'quote))
              ((char=? c #\`) (%read-abbrev (%advance cur) start 'quasiquote))
              ((char=? c #\,)
               (let ((next (%advance cur)))
                 (if (char=? (%cur-char next) #\@)
                     (%read-abbrev (%advance next) start 'unquote-splicing)
                     (%read-abbrev next start 'unquote))))
              (else (%read-atom cur start)))))))

(define (%read-abbrev cur start name)
  (%marking (list 'abbrev start name)
    (let-values (((d cur) (%read-datum (%skip-atmosphere cur))))
      (values (list name d) cur))))

;;; ------------------------------------------------------------------- lists

(define (%read-list cur start close)
  (let loop ((cur cur) (items '()))
    ;; In tail position, so the mark is replaced each time round: it always
    ;; says what has been read so far.
    (%marking (list 'list start close items)
      (let* ((cur (%skip-atmosphere cur)) (c (%cur-char cur)))
        (cond ((and (not (%hash-pending? cur)) (char=? c close))
               (values (reverse items) (%consumed cur)))
              ((and (not (%hash-pending? cur)) (memv c '(#\) #\])))
               (%fail cur (string-append "expected `" (string close) "` but found `" (string c) "`")))
              ((and (not (%hash-pending? cur)) (char=? c #\.))
               (let ((next (%advance cur)))
                 (if (%delimiter? (%cur-char next))
                     (%read-dotted next start close items (%cur-pos cur))
                     (let-values (((d cur) (%read-atom-from next (%cur-pos cur) ".")))
                       (loop cur (cons d items))))))
              (else
               (let-values (((d cur) (%read-datum cur)))
                 (loop cur (cons d items)))))))))

(define (%read-dotted cur start close items dot)
  (%marking (list 'dotted start close items)
    (if (null? items)
        (%fail-at cur dot "`.` must follow at least one element")
        (let ((cur (%skip-atmosphere cur)))
          (if (and (not (%hash-pending? cur)) (char=? (%cur-char cur) close))
              (%fail-at cur dot "expected a datum after `.`")
              (let-values (((tail cur) (%read-datum cur)))
                (let ((cur (%skip-atmosphere cur)))
                  (if (and (not (%hash-pending? cur)) (char=? (%cur-char cur) close))
                      (values (append (reverse items) tail) (%consumed cur))
                      (%fail cur (string-append "expected `" (string close)
                                                "` after the tail of a dotted list"))))))))))

;;; ----------------------------------------------------------------- strings

(define (%read-string cur start)
  (%marking (list 'string start)
    (let loop ((cur cur) (acc '()))
      (let ((c (%cur-char cur)))
        (cond ((char=? c #\") (values (list->string (reverse acc)) (%consumed cur)))
              ((char=? c #\\)
               (let* ((cur (%advance cur)) (e (%cur-char cur)))
                 (case e
                   ((#\n) (loop (%advance cur) (cons #\newline acc)))
                   ((#\t) (loop (%advance cur) (cons #\tab acc)))
                   ((#\r) (loop (%advance cur) (cons #\return acc)))
                   ((#\a) (loop (%advance cur) (cons (integer->char 7) acc)))
                   ((#\b) (loop (%advance cur) (cons (integer->char 8) acc)))
                   ((#\0) (loop (%advance cur) (cons (integer->char 0) acc)))
                   ((#\x #\X)
                    (let hex ((cur (%advance cur)) (digits '()))
                      (let ((h (%cur-char cur)))
                        (cond ((char=? h #\;)
                               (let ((n (string->number (list->string (reverse digits)) 16)))
                                 (if n
                                     (loop (%advance cur) (cons (integer->char n) acc))
                                     (%fail cur "bad `\\x` escape"))))
                              ((%hex-digit? h) (hex (%advance cur) (cons h digits)))
                              (else (%fail cur "expected `;` after `\\x` escape"))))))
                   ((#\newline #\space #\tab)
                    (let gap ((cur (%advance cur)) (seen-newline (char=? e #\newline)))
                      (let ((g (%cur-char cur)))
                        (cond ((and (char=? g #\newline) (not seen-newline)) (gap (%advance cur) #t))
                              ((or (char=? g #\space) (char=? g #\tab)) (gap (%advance cur) seen-newline))
                              (seen-newline (loop cur acc))
                              (else (loop cur (cons e acc)))))))
                   (else (loop (%advance cur) (cons e acc))))))
              (else (loop (%advance cur) (cons c acc))))))))

(define (%hex-digit? c)
  (or (char-numeric? c) (memv (char-downcase c) '(#\a #\b #\c #\d #\e #\f))))

;;; --------------------------------------------------------------- `#` syntax
;;; `start` is where the `#` was; `cur` is at the character after it.

(define (%read-hash start cur)
  (%marking (list 'hash start)
    (let ((c (%cur-char cur)))
      (cond ((char=? c #\() (let-values (((items cur) (%read-list (%advance cur) start #\))))
                              (if (list? items)
                                  (values (list->vector items) cur)
                                  (%fail-at cur start "a vector cannot be a dotted list"))))
            ((char=? c #\\) (%read-char (%advance cur) start))
            ((memv c '(#\t #\f #\T #\F))
             (let-values (((word cur) (%read-word cur)))
               (let ((w (string-downcase word)))
                 (cond ((member w '("t" "true")) (values #t cur))
                       ((member w '("f" "false")) (values #f cur))
                       (else (%fail-at cur start (string-append "unknown `#` syntax: `#" word "`")))))))
            ((memv c '(#\u #\U))
             (let-values (((word cur) (%read-word cur)))
               (cond ((not (string-ci=? word "u8"))
                      (%fail-at cur start (string-append "unknown `#` syntax: `#" word "`")))
                     ((not (char=? (%cur-char cur) #\())
                      (%fail cur "expected `(` after `#u8`"))
                     (else
                      (let-values (((items cur) (%read-list (%advance cur) start #\))))
                        (if (and (list? items)
                                 (let ok ((l items))
                                   (or (null? l)
                                       (and (exact-integer? (car l)) (<= 0 (car l) 255) (ok (cdr l))))))
                            (values (apply bytevector items) cur)
                            ;; The Rust reader points at the element; elements
                            ;; carry no positions here, so this points at `#u8`.
                            (%fail-at cur start "bytevector elements must be exact integers in 0..=255")))))))
            ((memv c '(#\b #\B #\o #\O #\d #\D #\x #\X #\e #\E #\i #\I))
             (%read-atom-from cur start "#"))
            ((char-numeric? c) (%fail-at cur start "datum labels are not supported by the eager reader"))
            (else (%fail-at cur start (string-append "unknown `#` syntax: `#" (string c) "`")))))))

;; The characters up to the next delimiter.
(define (%read-word cur)
  (let loop ((cur cur) (acc '()))
    (let ((c (%cur-char cur)))
      (if (%delimiter? c)
          (values (list->string (reverse acc)) cur)
          (loop (%advance cur) (cons c acc))))))

(define %char-names
  (list (cons "space" #\space) (cons "newline" #\newline) (cons "linefeed" #\newline)
        (cons "nl" #\newline) (cons "tab" #\tab) (cons "return" #\return)
        (cons "null" (integer->char 0)) (cons "nul" (integer->char 0))
        (cons "alarm" (integer->char 7)) (cons "backspace" (integer->char 8))
        (cons "delete" (integer->char 127)) (cons "rubout" (integer->char 127))
        (cons "escape" (integer->char 27)) (cons "altmode" (integer->char 27))
        (cons "esc" (integer->char 27))))

;; `#\c`, `#\space`, `#\x41`. The first character is taken whatever it is --
;; `#\(` is a parenthesis -- and anything after it up to a delimiter makes a
;; name.
(define (%read-char cur start)
  (%marking (list 'char start)
    (let ((first (%cur-char cur)))
      (let-values (((rest cur) (%read-word (%advance cur))))
        (if (string=? rest "")
            (values first cur)
            (let* ((name (string-append (string first) rest))
                   (lower (string-downcase name))
                   (named (assoc lower %char-names)))
              (cond (named (values (cdr named) cur))
                    ((and (char=? (string-ref lower 0) #\x) (> (string-length lower) 1))
                     (let ((n (string->number (substring lower 1 (string-length lower)) 16)))
                       (if n
                           (values (integer->char n) cur)
                           (%fail-at cur start (string-append "bad character name `#\\" name "`")))))
                    (else (%fail-at cur start (string-append "unknown character name `#\\" name "`"))))))))))

;;; ------------------------------------------------------------------- atoms
;;; A symbol or a number: which one can only be decided once the whole token
;;; is in hand -- `+` is a symbol, `+1` a number, `1+` a symbol again.

(define (%read-atom cur start)
  (%read-atom-from cur start ""))

;; `prefix` is text already consumed as part of this token (`.` or `#`).
(define (%read-atom-from cur start prefix)
  (%marking (list 'atom start)
    (let loop ((cur cur) (acc (reverse (string->list prefix))) (escaped #f))
      (let ((c (%cur-char cur)))
        (cond ((char=? c #\|)
               (let bar ((cur (%advance cur)) (acc acc))
                 (%marking (list 'symbol start)
                   (let ((b (%cur-char cur)))
                     (cond ((char=? b #\|) (loop (%advance cur) acc #t))
                           ((char=? b #\\)
                            (let ((cur (%advance cur)))
                              (bar (%advance cur) (cons (%cur-char cur) acc))))
                           (else (bar (%advance cur) (cons b acc))))))))
              ((char=? c #\\)
               (let ((cur (%advance cur)))
                 (loop (%advance cur) (cons (%cur-char cur) acc) #t)))
              ((%delimiter? c)
               (let ((text (list->string (reverse acc))))
                 (cond ((and (string=? text "") (not escaped))
                        (%fail cur (string-append "unexpected `" (string c) "`")))
                       ((and (not escaped) (string->number text)) => (lambda (n) (values n cur)))
                       (else (values (string->symbol text) cur)))))
              (else (loop (%advance cur) (cons c acc) escaped)))))))
