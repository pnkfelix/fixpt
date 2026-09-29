;;; The eager reader, in FX-26.
;;;
;;; A port of `crates/fixpt-scheme/src/eager-reader.scm`, which says what it
;;; is and why: an R7RS reader fed one character at a time, suspending for
;;; the next with a composable continuation captured up to a prompt of its
;;; own, and saying where it is in continuation marks. The structure follows
;;; that file procedure for procedure, so the two can be read side by side;
;;; what differs is what the types make explicit.
;;;
;;; * **Regions.** The reader's own lists and pairs are in @s, its prompt
;;;   tag in @e and its mark key in @m, and all of them are private to this
;;;   program (`private-regions`). Its control effects are on @e, and are
;;;   never masked: a checkpoint is handed back to the caller. That is what
;;;   the licence in `docs/fx26.md` is about — every effect here is on a
;;;   region no other program can name.
;;; * **Data.** What is read is a `syn`: a datum, or a list of `syn`s, with
;;;   where it starts and ends, in characters. `eager-state-syntax` gives
;;;   those; `eager-state-data`, and the marks, give plain `datum`s, opaque
;;;   Scheme data, made from them. The cursor
;;;   and the state, which the Scheme version keeps in lists and a record,
;;;   are pairs with a declared type each.
;;; * **No `values`.** A reading procedure returns a `result`: the datum and
;;;   the cursor after it, in a pair.
;;;
;;; It reads Scheme, from `eager-start`, or FX-26's own lexical syntax, from
;;; `eager-start-fx26`.
;;;
;;; The procedures a caller uses keep the Scheme version's names and
;;; meanings — `eager-start`, `eager-feed`, `eager-status`,
;;; `eager-state-position`, `eager-state-message`, `eager-state-data`,
;;; `eager-context`, `eager-hole-closers` — so the same tests drive both
;;; (lowered, each is the Scheme global `fx:<name>`).

;;; ------------------------------------------------------------------ types

;; The reader's own regions: its data, its prompt tag, its mark key, and the
;; lists it hands back. Each is fresh for this program, and nothing outside
;; it can name one — which is what licenses running it on every keystroke.
(private-regions @s @e @m @c)

;; What a reading procedure may do: allocate, read and write its own data,
;; mark, and suspend or fail through its prompt.
(define-effect reads (maxeff (read @globals) (alloc @s) (read @s) (write @s) (write @m) (read @m) (goto @e) (comefrom @e)))
;; The same, less the control on @e: what a delimited parse does.
(define-effect parsing (maxeff (read @globals) (alloc @s) (read @s) (write @s) (write @m) (read @m)))

(define-type chars (listof char acyclic))
(define-type data (listof datum acyclic))

;; What is read, with where each piece starts and ends. A vector's elements
;; keep theirs; any other datum that is not a list is an `atom`. Each piece
;; also carries the plain datum it reads as, made once, when it was read,
;; from the datums the marks already hold.
(define-datatype syn
  (atom datum int int)
  (lst (listof syn acyclic) datum int int)
  (dotted (listof syn acyclic) syn datum int int)
  (vec (listof syn acyclic) datum int int))
(define-type syns (listof syn acyclic))

(define syn->datum (subr pure (syn) datum)
  (lambda (s)
    (tagcase s
      (atom (d a b) d)
      (lst (items d a b) d)
      (dotted (items tail d a b) d)
      (vec (items d a b) d))))
(define syns->data (subr (maxeff (read @globals) (read @s) (alloc @s)) (syns) data)
  (lambda (xs) (if (null? xs) nil (cons (syn->datum (car xs)) (syns->data (cdr xs))))))

;; What a feed returns: waiting for a character, or stopped at an error.
;; Fields: need?, the continuation (one, when waiting), position, the
;; complete top-level data (newest first), and the message.
(define-type state
  (dletrec ((st (pairof bool (pairof (listof k acyclic) (pairof int (pairof syns string @s) @s) @s) @s))
            (k (composable char st (maxeff parsing spin) @e)))
    st))
(define-type cont (composable char state (maxeff parsing spin) @e))

;; The lookahead character (none once a closing character is consumed), how
;; many characters have been consumed, the top-level data, and — after `#`
;; followed by something that is not a comment — the cursor after that
;; something, which the datum reader takes up.
(define-type cursor (pairof chars (pairof int (pairof syns (listof cursor acyclic) @s) @s) @s))

;; What was read, and the cursor after it.
(define-type result (pairof syn cursor @s))
;; Some characters, and the cursor after them.
(define-type word (pairof string cursor @s))

(define eager-tag (prompt-tag state state (maxeff parsing spin) @e) (make-continuation-prompt-tag))
(define eager-key (mark-key datum @m) (make-continuation-mark-key))

;; Which dialect is being read: #f for Scheme, #t for FX-26 (the profile
;; `fixpt_read::SyntaxProfile::FX26`, which differs in two places: `#u` alone
;; is the unit value, and `[` and `]` are reserved). A mark rather than an
;; argument: it is set once, around the whole parse, and a checkpoint carries
;; it along, since the marks of a captured continuation are part of it.
(define dialect-key (mark-key bool @m) (make-continuation-mark-key))
(define fx26? (subr reads () bool) (lambda () (first-mark dialect-key #f)))

;;; ------------------------------------------------------------- the states

(define make-state (subr (alloc @s) (bool (listof cont acyclic) int syns string) state)
  (lambda (need ks pos data message) (cons need (cons ks (cons pos (cons data message))))))
(define state-need? (subr (read @s) (state) bool) (lambda (st) (car st)))
(define state-ks (subr (read @s) (state) (listof cont acyclic)) (lambda (st) (car (cdr st))))
(define state-position (subr (read @s) (state) int) (lambda (st) (car (cdr (cdr st)))))
(define state-data (subr (read @s) (state) syns) (lambda (st) (car (cdr (cdr (cdr st))))))
(define state-message (subr (read @s) (state) string) (lambda (st) (cdr (cdr (cdr (cdr st))))))

;; Input given ahead (`eager-feed-string`): a string, and where in it the
;; next character is. While there is some, the reader takes its characters
;; from here and runs on; only when there is none left does it suspend.
;; The one thing kept in a variable, as in the Scheme reader, and only
;; while a feed runs, so that states stay values.
(define ahead-text (ref string @s) (new ""))
(define ahead-at (ref int @s) (new 0))

;; The next character: the next one given ahead, or, if there is none,
;; suspend for it.
(define next-char (subr reads (int syns) char)
  (lambda (pos data)
    (let ((i (get ahead-at)) (text (get ahead-text)))
      (if (< i (string-length text))
          (begin (set ahead-at (+ i 1)) (string-ref text i))
          (call-with-composable-continuation
           (lambda (k) (abort-current-continuation eager-tag (make-state #t (cons k nil) pos data "")))
           eager-tag)))))

(define eager-run (subr (maxeff reads spin) ((subr (maxeff reads spin) () state)) state)
  (lambda (thunk) (prompt eager-tag (thunk) (lambda (st) st))))

;;; ------------------------------------------------------------ the cursors

(define make-cursor (subr (alloc @s) (chars int syns (listof cursor acyclic)) cursor)
  (lambda (look pos data pending) (cons look (cons pos (cons data pending)))))
(define cur-look (subr (read @s) (cursor) chars) (lambda (cur) (car cur)))
(define cur-char (subr (read @s) (cursor) char) (lambda (cur) (car (car cur))))
(define cur-pos (subr (read @s) (cursor) int) (lambda (cur) (car (cdr cur))))
(define cur-data (subr (read @s) (cursor) syns) (lambda (cur) (car (cdr (cdr cur)))))
(define cur-pending (subr (read @s) (cursor) (listof cursor acyclic)) (lambda (cur) (cdr (cdr (cdr cur)))))
(define hash-pending? (subr (maxeff (read @globals) (read @s)) (cursor) bool) (lambda (cur) (not (null? (cur-pending cur)))))

(define advance (subr reads (cursor) cursor)
  (lambda (cur)
    (let ((pos (+ (cur-pos cur) 1)) (data (cur-data cur)))
      (make-cursor (cons (next-char pos data) nil) pos data nil))))

(define consumed (subr reads (cursor) cursor)
  (lambda (cur) (make-cursor nil (+ (cur-pos cur) 1) (cur-data cur) nil)))

(define need (subr reads (cursor) cursor)
  (lambda (cur)
    (if (null? (cur-look cur))
        (make-cursor (cons (next-char (cur-pos cur) (cur-data cur)) nil) (cur-pos cur) (cur-data cur) nil)
        cur)))
;; A cursor with `c` in hand at `pos`: what a loop that reads characters
;; itself, keeping only the last and where it is, makes when it is done,
;; one for a token rather than one for each character.
(define cursor-at (subr (maxeff (alloc @s) (read (globals make-cursor))) (char int syns) cursor)
  (lambda (c pos data) (make-cursor (cons c nil) pos data nil)))
;; Past whitespace, the character at `pos` one: the cursor at the first
;; that is not.
(define skip-white (subr (maxeff reads spin) (int syns) cursor)
  (lambda (pos data)
    (let ((c (next-char (+ pos 1) data)))
      (if (char-whitespace? c) (skip-white (+ pos 1) data) (cursor-at c (+ pos 1) data)))))

(define fail-at (subr reads (cursor int string) void)
  (lambda (cur pos message)
    (abort-current-continuation eager-tag (make-state #f nil pos (cur-data cur) message))))
(define fail (subr reads (cursor string) void)
  (lambda (cur message) (fail-at cur (cur-pos cur) message)))

;;; ------------------------------------------------------------------ marks
;;; Each construct marks what it is reading, as data: `(list start close
;;; items)` and the rest, as the Scheme version's marks are.

(define marking (poly ((t type)) (subr (maxeff reads spin) (datum (subr (maxeff reads spin) () t)) t))
  (lambda (what body) (with-mark eager-key what body)))

(define no-data datum (datum-list (the data nil)))
;; Built with `datum-cons`, as data from the start: a list made with
;; `cons` would be copied to make it a datum.
(define entry (subr (read @globals) (datum int) datum)
  (lambda (name start) (datum-cons name (datum-cons (datum-int start) no-data))))
(define top-entry (subr (read @globals) () datum)
  (lambda () (datum-cons (datum-symbol "top") no-data)))
(define abbrev-entry (subr (read @globals) (int string) datum)
  (lambda (start name)
    (datum-cons (datum-symbol "abbrev") (datum-cons (datum-int start) (datum-cons (datum-symbol name) no-data)))))
;; A list's mark: its items so far, newest first, as a datum the reader
;; builds a pair at a time as it reads them, not copied at each.
(define list-entry (subr (read @globals) (datum int char datum) datum)
  (lambda (name start close items)
    (datum-cons name (datum-cons (datum-int start) (datum-cons (datum-char close) (datum-cons items no-data))))))
;; `items`, newest first, in order, onto `done`.
(define datum-reverse-onto (subr (read @globals) (datum datum) datum)
  (lambda (items done)
    (if (datum-null? items) done (datum-reverse-onto (datum-cdr items) (datum-cons (datum-car items) done)))))
;; The marks' names, interned once.
(define m-comment datum (datum-symbol "comment"))
(define m-block-comment datum (datum-symbol "block-comment"))
(define m-string datum (datum-symbol "string"))
(define m-char datum (datum-symbol "char"))
(define m-atom datum (datum-symbol "atom"))
(define m-symbol datum (datum-symbol "symbol"))
(define m-datum-comment datum (datum-symbol "datum-comment"))
(define m-hash datum (datum-symbol "hash"))
(define m-list datum (datum-symbol "list"))
(define m-dotted datum (datum-symbol "dotted"))

;;; -------------------------------------------------------------- strings

(define str3 (subr pure (string string string) string)
  (lambda (a b c) (string-append a (string-append b c))))
(define str5 (subr (read @globals) (string string string string string) string)
  (lambda (a b c d e) (string-append a (string-append b (str3 c d e)))))
(define char-string (subr pure (char) string) (lambda (c) (char->string c)))

(define delimiter? (subr pure (char) bool)
  (lambda (c) (or (char-whitespace? c) (char-in? c "()[]\";'`,"))))

;; Whether an atom starting so may be a number: only then is it parsed as one.
(define number-start? (subr pure (char) bool)
  (lambda (c) (or (char-numeric? c) (char-in? c "+-.#"))))

(define hex-digit? (subr pure (char) bool)
  (lambda (c) (or (char-numeric? c) (char-in? (char-downcase c) "abcdef"))))

;; Feed one character to a waiting state, giving the next state.
(define eager-feed (subr (maxeff reads spin) (state char) state)
  (lambda (st ch)
    (if (state-need? st)
        (begin (set ahead-text "") (set ahead-at 0) (eager-run (lambda () ((car (state-ks st)) ch))))
        st)))

;; The same as feeding each of `text`'s characters in turn, but the reader
;; suspends only when it has read them all, not after each: for text that
;; is all there, such as a file's.
(define eager-feed-string (subr (maxeff reads spin) (state string) state)
  (lambda (st text)
    (if (or (not (state-need? st)) (= (string-length text) 0))
        st
        (begin
          (set ahead-text text)
          (set ahead-at 1)
          (let ((after (eager-run (lambda () ((car (state-ks st)) (string-ref text 0))))))
            (begin (set ahead-text "") (set ahead-at 0) after))))))

(define eager-state-kind (subr (maxeff (read @globals) (read @s)) (state) datum)
  (lambda (st) (if (state-need? st) (datum-symbol "need") (datum-symbol "error"))))
(define eager-state-position (subr (maxeff (read @globals) (read @s)) (state) int) (lambda (st) (state-position st)))
(define eager-state-message (subr (maxeff (read @globals) (read @s)) (state) string) (lambda (st) (state-message st)))
;; The complete top-level data read so far, in order.
(define eager-state-data (subr (maxeff (read @globals) (read @s) (alloc @s)) (state) data)
  (lambda (st) (syns->data (the syns (reverse (state-data st))))))
;; The same, with where each piece is.
(define eager-state-syntax (subr (maxeff (read @globals) (read @s) (alloc @s)) (state) syns)
  (lambda (st) (the syns (reverse (state-data st)))))

;; What the suspended parse is in the middle of, innermost first.
(define eager-context (subr (maxeff (read @globals) (read @s) (read @m) (alloc @c)) (state) (listof datum @c))
  (lambda (st)
    (if (state-need? st)
        (marks-of (car (state-ks st)) eager-key)
        nil)))

(define entry-name (subr pure (datum) string) (lambda (e) (datum-symbol-name (datum-car e))))
(define entry-ref (subr (read @globals) (datum int) datum)
  (lambda (e i) (if (= i 0) (datum-car e) (entry-ref (datum-cdr e) (- i 1)))))

(define settled? (subr (maxeff (read @globals) (read @c) spin) ((listof datum @c)) bool)
  (lambda (ctx)
    (or (null? ctx)
        (and (let ((n (entry-name (car ctx)))) (or (string=? n "top") (string=? n "comment")))
             (settled? (cdr ctx))))))

;; `complete`, `incomplete` or `error`.
(define eager-status (subr (maxeff (read @globals) (read @s) (read @m) (alloc @c) (read @c) spin) (state) datum)
  (lambda (st)
    (cond ((not (state-need? st)) (datum-symbol "error"))
          ((settled? (the (listof datum @c) (eager-context st))) (datum-symbol "complete"))
          (else (datum-symbol "incomplete")))))

(define hole? (subr pure (datum) bool)
  (lambda (d)
    (and (datum-pair? d)
         (datum-symbol? (datum-car d))
         (string=? (datum-symbol-name (datum-car d)) "unquote")
         (datum-pair? (datum-cdr d))
         (datum-symbol? (datum-car (datum-cdr d)))
         (let ((n (datum-symbol-name (datum-car (datum-cdr d))))) (or (string=? n "help") (string=? n "?")))
         (datum-null? (datum-cdr (datum-cdr d))))))

(define closing (subr (maxeff (read @globals) (read @c) (alloc @c) spin) ((listof datum @c) (listof char @c)) datum)
  (lambda (ctx acc)
    (if (null? ctx)
        (datum-bool #f)
        (let ((n (entry-name (car ctx))))
          (cond ((string=? n "top") (datum-string (list->string (the (listof char @c) (reverse acc)))))
                ((or (string=? n "list") (string=? n "dotted"))
                 (closing (cdr ctx) (cons (datum-char-value (entry-ref (car ctx) 2)) acc)))
                ((string=? n "hash") (closing (cdr ctx) acc))
                (else (datum-bool #f)))))))

;; If the newest thing read in the innermost open list is a `,help` hole,
;; the characters that would close every open list; otherwise #f.
(define eager-hole-closers (subr (maxeff (read @globals) (read @s) (read @m) (alloc @c) (read @c) spin) (state) datum)
  (lambda (st)
    (let ((ctx (the (listof datum @c) (eager-context st))))
      (if (and (not (null? ctx))
               (string=? (entry-name (car ctx)) "list")
               (let ((items (entry-ref (car ctx) 3))) (and (datum-pair? items) (hole? (datum-car items)))))
          (closing ctx nil)
          (datum-bool #f)))))

(define line-comment (subr (maxeff reads spin) (cursor) cursor)
  (lambda (cur)
    (marking (entry m-comment (cur-pos cur))
      (lambda ()
        (let ((data (cur-data cur)))
          (letrec ((loop (subr (maxeff (read @globals) reads spin) (char int) cursor)
                     (lambda (c pos)
                       (if (char=? c #\newline)
                           (make-cursor nil (+ pos 1) data nil)
                           (loop (next-char (+ pos 1) data) (+ pos 1))))))
            (loop (next-char (+ (cur-pos cur) 1) data) (+ (cur-pos cur) 1))))))))

;; `#| … |#`, nesting.
(define block-comment (subr (maxeff reads spin) (cursor int int) cursor)
  (lambda (cur start depth)
    (marking (entry m-block-comment start)
      (lambda ()
        (let ((c (cur-char cur)))
          (cond ((char=? c #\|)
                 (let ((next (advance cur)))
                   (if (char=? (cur-char next) #\#)
                       (if (= depth 1) (consumed next) (block-comment (advance next) start (- depth 1)))
                       (block-comment next start depth))))
                ((char=? c #\#)
                 (let ((next (advance cur)))
                   (if (char=? (cur-char next) #\|)
                       (block-comment (advance next) start (+ depth 1))
                       (block-comment next start depth))))
                (else (block-comment (advance cur) start depth))))))))

;;; ----------------------------------------------------------------- strings

(define read-string (subr (maxeff reads spin) (cursor int) result)
  (lambda (cur start)
    (marking (entry m-string start)
      (lambda ()
        (let ((data (cur-data cur)))
        (letrec (;; The character `c` at `pos` in hand, the next read here:
                 ;; a cursor only for an escape, or at the end.
                 (run (subr (maxeff (read @globals) reads spin) (char int chars) result)
                   (lambda (c pos acc)
                     (cond ((char=? c #\")
                            (cons (atom (datum-string (list->string (the chars (reverse acc)))) start (+ pos 1))
                                  (make-cursor nil (+ pos 1) data nil)))
                           ((char=? c #\\) (escape (cursor-at (next-char (+ pos 1) data) (+ pos 1) data) acc))
                           (else (run (next-char (+ pos 1) data) (+ pos 1) (cons c acc))))))
                 (loop (subr (maxeff (read @globals) reads spin) (cursor chars) result)
                   (lambda (cur acc) (run (cur-char cur) (cur-pos cur) acc)))
                 (escape (subr (maxeff (read @globals) reads spin) (cursor chars) result)
                   (lambda (cur acc)
                     (let ((e (cur-char cur)))
                       (cond ((char=? e #\n) (loop (advance cur) (cons #\newline acc)))
                             ((char=? e #\t) (loop (advance cur) (cons (integer->char 9) acc)))
                             ((char=? e #\r) (loop (advance cur) (cons (integer->char 13) acc)))
                             ((char=? e #\a) (loop (advance cur) (cons (integer->char 7) acc)))
                             ((char=? e #\b) (loop (advance cur) (cons (integer->char 8) acc)))
                             ((char=? e #\0) (loop (advance cur) (cons (integer->char 0) acc)))
                             ((char-in? e "xX") (hex (advance cur) acc nil))
                             ((or (char=? e #\newline) (char=? e #\space) (char=? e (integer->char 9)))
                              (gap (advance cur) acc e (char=? e #\newline)))
                             (else (loop (advance cur) (cons e acc)))))))
                 (hex (subr (maxeff (read @globals) reads spin) (cursor chars chars) result)
                   (lambda (cur acc digits)
                     (let ((h (cur-char cur)))
                       (cond ((char=? h #\;)
                              (let ((n (parse-int (list->string (the chars (reverse digits))) 16)))
                                (if (>= n 0)
                                    (loop (advance cur) (cons (integer->char n) acc))
                                    (fail cur "bad `\\x` escape"))))
                             ((hex-digit? h) (hex (advance cur) acc (cons h digits)))
                             (else (fail cur "expected `;` after `\\x` escape"))))))
                 ;; A backslash before a line break: the break and the
                 ;; blanks around it vanish. Before blanks alone, it is
                 ;; the character itself.
                 (gap (subr (maxeff (read @globals) reads spin) (cursor chars char bool) result)
                   (lambda (cur acc e seen-newline)
                     (let ((g (cur-char cur)))
                       (cond ((and (char=? g #\newline) (not seen-newline)) (gap (advance cur) acc e #t))
                             ((or (char=? g #\space) (char=? g (integer->char 9))) (gap (advance cur) acc e seen-newline))
                             (seen-newline (loop cur acc))
                             (else (loop cur (cons e acc))))))))
          (loop cur nil)))))))

;; A proper list of exact integers in 0..=255.
(define bytes? (subr (read @globals) (datum) bool)
  (lambda (d)
    (or (datum-null? d)
        (and (datum-pair? d) (datum-byte? (datum-car d)) (bytes? (datum-cdr d))))))

;; The characters up to the next delimiter.
(define read-word (subr (maxeff reads spin) (cursor) word)
  (lambda (cur)
    (letrec ((loop (subr (maxeff (read @globals) reads spin) (cursor chars) word)
               (lambda (cur acc)
                 (if (delimiter? (cur-char cur))
                     (cons (list->string (the chars (reverse acc))) cur)
                     (loop (advance cur) (cons (cur-char cur) acc))))))
      (loop cur nil))))

;; The character a name stands for, as a code, or -1.
(define char-name (subr pure (string) int)
  (lambda (n)
    (cond ((string=? n "space") 32)
          ((or (string=? n "newline") (string=? n "linefeed") (string=? n "nl")) 10)
          ((string=? n "tab") 9)
          ((string=? n "return") 13)
          ((or (string=? n "null") (string=? n "nul")) 0)
          ((string=? n "alarm") 7)
          ((string=? n "backspace") 8)
          ((or (string=? n "delete") (string=? n "rubout")) 127)
          ((or (string=? n "escape") (string=? n "altmode") (string=? n "esc")) 27)
          (else -1))))

;; `#\c`, `#\space`, `#\x41`. The first character is taken whatever it is,
;; and anything after it up to a delimiter makes a name.
(define read-char (subr (maxeff reads spin) (cursor int) result)
  (lambda (cur start)
    (marking (entry m-char start)
      (lambda ()
        (let* ((first (cur-char cur)) (w (read-word (advance cur))) (rest (car w)) (cur (cdr w)))
          (if (string=? rest "")
              (cons (atom (datum-char first) start (cur-pos cur)) cur)
              (let* ((name (string-append (char-string first) rest))
                     (lower (string-downcase name))
                     (named (char-name lower)))
                (cond ((>= named 0) (cons (atom (datum-char (integer->char named)) start (cur-pos cur)) cur))
                      ((and (char=? (string-ref lower 0) #\x) (> (string-length lower) 1))
                       (let ((n (parse-int (substring lower 1 (string-length lower)) 16)))
                         (if (>= n 0)
                             (cons (atom (datum-char (integer->char n)) start (cur-pos cur)) cur)
                             (fail-at cur start (str3 "bad character name `#\\" name "`")))))
                      (else (fail-at cur start (str3 "unknown character name `#\\" name "`")))))))))))

;;; ------------------------------------------------------------------- atoms
;;; A symbol or a number: which one can only be decided once the whole token
;;; is in hand. `prefix` is text already consumed as part of it (`.` or `#`).

(define read-atom-from (subr (maxeff reads spin) (cursor int string) result)
  (lambda (cur start prefix)
    (marking (entry m-atom start)
      (lambda ()
        (let ((data (cur-data cur)))
            ;; Each loop has the character `c` at `pos` in hand, and reads
          ;; the next itself.
          (letrec ((loop (subr (maxeff (read @globals) reads spin) (char int chars bool) result)
                     (lambda (c pos acc escaped)
                       (cond ((char=? c #\|) (bar (next-char (+ pos 1) data) (+ pos 1) acc))
                             ((char=? c #\\)
                              (let ((e (next-char (+ pos 1) data)))
                                (loop (next-char (+ pos 2) data) (+ pos 2) (cons e acc) #t)))
                             ((delimiter? c) (finish (cursor-at c pos data) (list->string (the chars (reverse acc))) escaped c))
                             (else (loop (next-char (+ pos 1) data) (+ pos 1) (cons c acc) escaped)))))
                   ;; Inside `|…|`.
                   (bar (subr (maxeff (read @globals) reads spin) (char int chars) result)
                     (lambda (b pos acc)
                       (marking (entry m-symbol start)
                         (lambda ()
                           (cond ((char=? b #\|) (loop (next-char (+ pos 1) data) (+ pos 1) acc #t))
                                 ((char=? b #\\)
                                  (let ((e (next-char (+ pos 1) data)))
                                    (bar (next-char (+ pos 2) data) (+ pos 2) (cons e acc))))
                                 (else (bar (next-char (+ pos 1) data) (+ pos 1) (cons b acc))))))))
                   (finish (subr (maxeff (read @globals) reads) (cursor string bool char) result)
                     (lambda (cur text escaped c)
                       (if (and (string=? text "") (not escaped))
                           (fail cur (str3 "unexpected `" (char-string c) "`"))
                           (let ((n (the data (if escaped nil (if (number-start? (string-ref text 0)) (parse-number text 10) nil)))))
                             (if (null? n)
                                 (cons (atom (datum-symbol text) start (cur-pos cur)) cur)
                                 (cons (atom (car n) start (cur-pos cur)) cur)))))))
            (loop (cur-char cur) (cur-pos cur) (the chars (if (string=? prefix "") nil (reverse (the chars (string->list prefix))))) #f)))))))

;;; -------------------------------------------------------------- atmosphere

(define-rec
  (skip-atmosphere (subr (maxeff reads spin) (cursor) cursor)
    (lambda (cur)
      (let* ((cur (need cur)) (c (cur-char cur)))
        (cond ((char-whitespace? c) (skip-atmosphere (skip-white (cur-pos cur) (cur-data cur))))
              ((char=? c #\;) (skip-atmosphere (line-comment cur)))
              ((char=? c #\#)
               (let* ((start (cur-pos cur)) (next (advance cur)) (d (cur-char next)))
                 (cond ((char=? d #\|) (skip-atmosphere (block-comment (advance next) start 1)))
                       ((char=? d #\;)
                        (skip-atmosphere
                         (marking (entry m-datum-comment start)
                           (lambda () (cdr (read-datum (skip-atmosphere (advance next))))))))
                       ;; Not atmosphere after all: the datum reader takes up
                       ;; the `#` and what follows it.
                       (else (make-cursor (cons #\# nil) start (cur-data cur) (cons next nil))))))
              (else cur)))))
  ;;; ------------------------------------------------------------------ datum
  (read-datum (subr (maxeff reads spin) (cursor) result)
    (lambda (cur)
      (let ((cur (need cur)))
        (if (hash-pending? cur)
            (read-hash (cur-pos cur) (car (cur-pending cur)))
            (let ((c (cur-char cur)) (start (cur-pos cur)))
              (cond ((char=? c #\() (read-list (advance cur) start #\)))
                    ((and (char-in? c "[]") (fx26?))
                     (fail cur (str3 "`" (char-string c) "` is reserved: it has no meaning yet")))
                    ((char=? c #\[) (read-list (advance cur) start #\]))
                    ((char-in? c ")]") (fail cur (str3 "unbalanced `" (char-string c) "`")))
                    ((char=? c #\") (read-string (advance cur) start))
                    ((char=? c #\#) (read-hash start (advance cur)))
                    ((char=? c #\') (read-abbrev (advance cur) start "quote"))
                    ((char=? c #\`) (read-abbrev (advance cur) start "quasiquote"))
                    ((char=? c #\,)
                     (let ((next (advance cur)))
                       (if (char=? (cur-char next) #\@)
                           (read-abbrev (advance next) start "unquote-splicing")
                           (read-abbrev next start "unquote"))))
                    (else (read-atom-from cur start ""))))))))
  (read-abbrev (subr (maxeff reads spin) (cursor int string) result)
    (lambda (cur start name)
      (marking (abbrev-entry start name)
        (lambda ()
          (let ((r (read-datum (skip-atmosphere cur))))
            (cons (lst (the syns (cons (atom (datum-symbol name) start (+ start 1)) (cons (car r) nil)))
                       (datum-cons (datum-symbol name) (datum-cons (syn->datum (car r)) no-data))
                       start
                       (cur-pos (cdr r)))
                  (cdr r)))))))
  ;;; ------------------------------------------------------------------- lists
  (read-list (subr (maxeff reads spin) (cursor int char) result)
    (lambda (cur start close)
      (letrec ((loop (subr (maxeff (read @globals) reads spin) (cursor data datum syns) result)
                 (lambda (cur items items-d syns)
                   ;; In tail position, so the mark is replaced each time
                   ;; round: it always says what has been read so far.
                   (marking (list-entry m-list start close items-d)
                     (lambda ()
                       (let* ((cur (skip-atmosphere cur))
                              (c (cur-char cur))
                              (plain (not (hash-pending? cur))))
                         (cond ((and plain (char=? c close))
                                (cons (lst (the syns (reverse syns)) (datum-reverse-onto items-d no-data) start (+ (cur-pos cur) 1))
                                      (consumed cur)))
                               ((and plain (char=? c #\]) (fx26?))
                                (fail cur "`]` is reserved: it has no meaning yet"))
                               ((and plain (char-in? c ")]"))
                                (fail cur (str5 "expected `" (char-string close) "` but found `" (char-string c) "`")))
                               ((and plain (char=? c #\.))
                                (let ((next (advance cur)))
                                  (if (delimiter? (cur-char next))
                                      (read-dotted next start close items items-d syns (cur-pos cur))
                                      (let* ((r (read-atom-from next (cur-pos cur) ".")) (d (syn->datum (car r))))
                                        (loop (cdr r) (cons d items) (datum-cons d items-d) (cons (car r) syns))))))
                               (else
                                (let* ((r (read-datum cur)) (d (syn->datum (car r))))
                                  (loop (cdr r) (cons d items) (datum-cons d items-d) (cons (car r) syns)))))))))))
        (loop cur nil no-data nil))))
  (read-dotted (subr (maxeff reads spin) (cursor int char data datum syns int) result)
    (lambda (cur start close items items-d syns dot)
      (marking (list-entry m-dotted start close items-d)
        (lambda ()
          (if (null? items)
              (fail-at cur dot "`.` must follow at least one element")
              (let ((cur (skip-atmosphere cur)))
                (if (and (not (hash-pending? cur)) (char=? (cur-char cur) close))
                    (fail-at cur dot "expected a datum after `.`")
                    (let* ((r (read-datum cur)) (cur (skip-atmosphere (cdr r))))
                      (if (and (not (hash-pending? cur)) (char=? (cur-char cur) close))
                          (cons (dotted (the syns (reverse syns))
                                        (car r)
                                        (datum-dotted (the data (reverse items)) (syn->datum (car r)))
                                        start
                                        (+ (cur-pos cur) 1))
                                (consumed cur))
                          (fail cur (str3 "expected `" (char-string close) "` after the tail of a dotted list")))))))))))
  ;;; --------------------------------------------------------------- `#` syntax
  ;;; `start` is where the `#` was; `cur` is at the character after it.
  (read-hash (subr (maxeff reads spin) (int cursor) result)
    (lambda (start cur)
      (marking (entry m-hash start)
        (lambda ()
          (let ((c (cur-char cur)))
            (cond ((char=? c #\()
                   (let ((r (read-list (advance cur) start #\))))
                     (tagcase (car r)
                       (lst (items d a b) (cons (vec items (datum-list->vector d) start b) (cdr r)))
                       (else x (fail-at (cdr r) start "a vector cannot be a dotted list")))))
                  ((char=? c #\\) (read-char (advance cur) start))
                  ((char-in? c "tfTF")
                   (let* ((w (read-word cur)) (word (car w)) (lower (string-downcase word)))
                     (cond ((or (string=? lower "t") (string=? lower "true")) (cons (atom (datum-bool #t) start (cur-pos (cdr w))) (cdr w)))
                           ((or (string=? lower "f") (string=? lower "false")) (cons (atom (datum-bool #f) start (cur-pos (cdr w))) (cdr w)))
                           (else (fail-at (cdr w) start (str3 "unknown `#` syntax: `#" word "`"))))))
                  ((char-in? c "uU")
                   (let* ((w (read-word cur)) (word (car w)) (cur (cdr w)))
                     (cond ((and (string-ci=? word "u") (fx26?))
                            ;; FX-26's unit value, beside `#u8(`.
                            (cons (atom (datum-symbol "#u") start (cur-pos cur)) cur))
                           ((not (string-ci=? word "u8"))
                            (fail-at cur start (str3 "unknown `#` syntax: `#" word "`")))
                           ((not (char=? (cur-char cur) #\())
                            (fail cur "expected `(` after `#u8`"))
                           (else
                            (let* ((r (read-list (advance cur) start #\))) (d (syn->datum (car r))))
                              (if (bytes? d)
                                  (cons (atom (datum-list->bytevector d) start (cur-pos (cdr r))) (cdr r))
                                  ;; The Rust reader points at the element; elements
                                  ;; carry no positions here, so this points at `#u8`.
                                  (fail-at (cdr r) start "bytevector elements must be exact integers in 0..=255")))))))
                  ((char-in? c "bBoOdDxXeEiI") (read-atom-from cur start "#"))
                  ((char-numeric? c) (fail-at cur start "datum labels are not supported by the eager reader"))
                  (else (fail-at cur start (str3 "unknown `#` syntax: `#" (char-string c) "`"))))))))))

;;; ------------------------------------------------------------- the driver

(define read-top (subr (maxeff reads spin) (cursor) void)
  (lambda (cur)
    (letrec ((loop (subr (maxeff (read @globals) reads spin) (cursor) void)
               (lambda (cur)
                 (marking (top-entry)
                   (lambda ()
                     (let* ((cur (skip-atmosphere cur)) (r (read-datum cur)) (after (cdr r)))
                       (loop (make-cursor (cur-look after) (cur-pos after) (cons (car r) (cur-data after)) nil))))))))
      (loop cur))))

;; A reader with nothing read yet, for Scheme or for FX-26.
(define start-reading (subr (maxeff reads spin) (bool) state)
  (lambda (fx26)
    (eager-run
     (lambda ()
       (with-mark dialect-key fx26
         (lambda () (read-top (make-cursor (cons (next-char 0 nil) nil) 0 nil nil))))))))
(define eager-start (subr (maxeff reads spin) () state) (lambda () (start-reading #f)))
(define eager-start-fx26 (subr (maxeff reads spin) () state) (lambda () (start-reading #t)))
