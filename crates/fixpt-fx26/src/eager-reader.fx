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
;; mark, and suspend or fail through its prompt. A delimited parse does the
;; same, less the control on @e (`parsing`); looking at the data only reads
;; it (`inspects`).
(define-effect own-data (maxeff (alloc @s) (read @s) (write @s)))
(define-effect marks (maxeff (write @m) (read @m)))
(define-effect parsing (maxeff (read @globals) own-data marks))
(define-effect reads (maxeff parsing (goto @e) (comefrom @e)))
(define-effect inspects (maxeff (read @globals) (read @s)))
;; What most of its procedures do: that, perhaps without end.
(define-effect reading (maxeff reads spin))

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
;; Fields: need?, the continuation (one, when waiting), and then, as a
;; `state-rest`, the position, the complete top-level data (newest first),
;; and the message.
(define-type state-rest (pairof int (pairof syns string @s) @s))
(define-type state
  (dletrec ((st (pairof bool (pairof (listof k acyclic) state-rest @s) @s))
            (k (composable char st (maxeff parsing spin) @e)))
    st))
(define-type cont (composable char state (maxeff parsing spin) @e))

;; The lookahead character (none once a closing character is consumed), how
;; many characters have been consumed, the top-level data, and — after `#`
;; followed by something that is not a comment — the cursor after that
;; something, which the datum reader takes up.
(define-type cursor (pairof chars (pairof int (pairof syns (listof cursor acyclic) @s) @s) @s))
(define-type cursors (listof cursor acyclic))

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
;; The state that waits for a character, to go on in `k`.
(define waiting (subr (maxeff (alloc @s) (read (globals make-state))) (cont int syns) state)
  (lambda (k pos data) (make-state #t (cons k nil) pos data "")))
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
;; Where the text given ahead starts, as the reader counts positions (its
;; first character's), or -1 when there is none: each feed changes it (a
;; later text starts later), so an atom read while it stays the same is all
;; in one text, and is taken from it whole (`read-atom-from`).
(define ahead-origin (ref int @s) (new -1))

;; The next character: the next one given ahead, or, if there is none,
;; suspend for it.
(define next-char (subr reads (int syns) char)
  (lambda (pos data)
    (let ((i (get ahead-at)) (text (get ahead-text)))
      (if (< i (string-length text))
          (begin (set ahead-at (+ i 1)) (string-ref text i))
          (call-with-composable-continuation
           (lambda (k) (abort-current-continuation eager-tag (waiting k pos data)))
           eager-tag)))))

(define eager-run (subr reading ((subr reading () state)) state)
  (lambda (thunk) (prompt eager-tag (thunk) (lambda (st) st))))

;;; ------------------------------------------------------------ the cursors

(define make-cursor (subr (alloc @s) (chars int syns (listof cursor acyclic)) cursor)
  (lambda (look pos data pending) (cons look (cons pos (cons data pending)))))
(define cur-look (subr (read @s) (cursor) chars) (lambda (cur) (car cur)))
(define cur-char (subr (read @s) (cursor) char) (lambda (cur) (car (car cur))))
(define cur-pos (subr (read @s) (cursor) int) (lambda (cur) (car (cdr cur))))
(define cur-data (subr (read @s) (cursor) syns) (lambda (cur) (car (cdr (cdr cur)))))
(define cur-pending (subr (read @s) (cursor) cursors) (lambda (cur) (cdr (cdr (cdr cur)))))
(define hash-pending? (subr inspects (cursor) bool) (lambda (cur) (not (null? (cur-pending cur)))))
;; An atom `d` read from `start` to `cur`, and `cur`.
(define atom-at (subr (maxeff (read @globals) (read @s) (alloc @s)) (datum int cursor) result)
  (lambda (d start cur) (cons (atom d start (cur-pos cur)) cur)))

;; A cursor with `c` in hand at `pos`: what a loop that reads characters
;; itself, keeping only the last and where it is, makes when it is done,
;; one for a token rather than one for each character.
(define cursor-at (subr (maxeff (alloc @s) (read (globals make-cursor))) (char int syns) cursor)
  (lambda (c pos data) (make-cursor (cons c nil) pos data nil)))
;; The cursor at the character after `pos`, read.
(define next-at (subr reads (int syns) cursor)
  (lambda (pos data) (cursor-at (next-char (+ pos 1) data) (+ pos 1) data)))
(define advance (subr reads (cursor) cursor)
  (lambda (cur)
    (let ((pos (+ (cur-pos cur) 1)) (data (cur-data cur)))
      (cursor-at (next-char pos data) pos data))))

(define consumed (subr reads (cursor) cursor)
  (lambda (cur) (make-cursor nil (+ (cur-pos cur) 1) (cur-data cur) nil)))

(define need (subr reads (cursor) cursor)
  (lambda (cur)
    (if (null? (cur-look cur))
        (cursor-at (next-char (cur-pos cur) (cur-data cur)) (cur-pos cur) (cur-data cur))
        cur)))
;; The characters of `text` from `i` to `j`, newest first: an atom's so far,
;; listed once it cannot be taken whole.
(define chars-back (subr (maxeff (read @globals) (alloc @s)) (string int int) chars)
  (lambda (text i j) (the chars (reverse (the chars (string->list (substring text i j)))))))
;; Past whitespace, the character at `pos` one: the cursor at the first
;; that is not.
(define skip-white (subr reading (int syns) cursor)
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

(define marking (poly ((t type)) (subr reading (datum (subr reading () t)) t))
  (lambda (what body) (with-mark eager-key what body)))

(define no-data datum (datum-list (the data nil)))
;; A datum list of two, three or four, built with `datum-cons`, as data from
;; the start: a list made with `cons` would be copied to make it a datum.
(define datum-list2 (subr (read @globals) (datum datum) datum)
  (lambda (a b) (datum-cons a (datum-cons b no-data))))
(define datum-list3 (subr (read @globals) (datum datum datum) datum)
  (lambda (a b c) (datum-cons a (datum-list2 b c))))
(define datum-list4 (subr (read @globals) (datum datum datum datum) datum)
  (lambda (a b c d) (datum-cons a (datum-list3 b c d))))
(define entry (subr (read @globals) (datum int) datum)
  (lambda (name start) (datum-list2 name (datum-int start))))
(define top-entry (subr (read @globals) () datum)
  (lambda () (datum-cons (datum-symbol "top") no-data)))
(define abbrev-entry (subr (read @globals) (int string) datum)
  (lambda (start name) (datum-list3 (datum-symbol "abbrev") (datum-int start) (datum-symbol name))))
;; A list's mark: its items so far, newest first, as a datum the reader
;; builds a pair at a time as it reads them, not copied at each.
(define list-entry (subr (read @globals) (datum int char datum) datum)
  (lambda (name start close items)
    (datum-list4 name (datum-int start) (datum-char close) items)))
;; `items`, newest first, in order, onto `done`.
(define datum-reverse-onto (subr (read @globals) (datum datum) datum)
  (lambda (items done)
    (if (datum-null? items)
        done
        (datum-reverse-onto (datum-cdr items) (datum-cons (datum-car items) done)))))
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
;; Whether `s` is `a` or `b`.
(define either? (subr pure (string string string) bool)
  (lambda (s a b) (or (string=? s a) (string=? s b))))
;; A space or a tab.
(define blank? (subr pure (char) bool)
  (lambda (c) (or (char=? c #\space) (char=? c (integer->char 9)))))
;; What was listed, newest first, as a string.
(define acc->string (subr (read @globals) (chars) string)
  (lambda (acc) (list->string (the chars (reverse acc)))))
;; Whether `i` is a position in `text`.
(define in-text? (subr pure (int string) bool)
  (lambda (i text) (and (>= i 0) (< i (string-length text)))))

;; Feed one character to a waiting state, giving the next state.
(define eager-feed (subr reading (state char) state)
  (lambda (st ch)
    (if (state-need? st)
        (begin (set ahead-text "") (set ahead-at 0)
               (set ahead-origin -1)
               (eager-run (lambda () ((car (state-ks st)) ch))))
        st)))

;; The same as feeding each of `text`'s characters in turn, but the reader
;; suspends only when it has read them all, not after each: for text that
;; is all there, such as a file's.
(define eager-feed-string (subr reading (state string) state)
  (lambda (st text)
    (if (or (not (state-need? st)) (= (string-length text) 0))
        st
        (begin
          (set ahead-text text)
          (set ahead-at 1)
          (set ahead-origin (state-position st))
          (let ((after (eager-run (lambda () ((car (state-ks st)) (string-ref text 0))))))
            (begin (set ahead-text "") (set ahead-at 0) (set ahead-origin -1) after))))))

(define eager-state-kind (subr inspects (state) datum)
  (lambda (st) (if (state-need? st) (datum-symbol "need") (datum-symbol "error"))))
(define eager-state-position (subr inspects (state) int) (lambda (st) (state-position st)))
(define eager-state-message (subr inspects (state) string) (lambda (st) (state-message st)))
;; The complete top-level data read so far, in order.
(define eager-state-data (subr (maxeff (read @globals) (read @s) (alloc @s)) (state) data)
  (lambda (st) (syns->data (the syns (reverse (state-data st))))))
;; The same, with where each piece is.
(define eager-state-syntax (subr (maxeff (read @globals) (read @s) (alloc @s)) (state) syns)
  (lambda (st) (the syns (reverse (state-data st)))))

;; What a suspended parse is in the middle of, as its marks say, in the
;; caller's region @c; what is asked of it.
(define-type context (listof datum @c))
(define-type closers (listof char @c))
(define-effect in-context (maxeff (read @globals) (read @c) (alloc @c) spin))
(define-effect asks (maxeff in-context (read @s) (read @m)))

;; What the suspended parse is in the middle of, innermost first.
(define eager-context (subr (maxeff inspects (read @m) (alloc @c)) (state) context)
  (lambda (st)
    (if (state-need? st)
        (marks-of (car (state-ks st)) eager-key)
        nil)))

(define entry-name (subr pure (datum) string) (lambda (e) (datum-symbol-name (datum-car e))))
(define entry-ref (subr (read @globals) (datum int) datum)
  (lambda (e i) (if (= i 0) (datum-car e) (entry-ref (datum-cdr e) (- i 1)))))

(define settled? (subr (maxeff (read @globals) (read @c) spin) (context) bool)
  (lambda (ctx)
    (or (null? ctx)
        (and (either? (entry-name (car ctx)) "top" "comment")
             (settled? (cdr ctx))))))

;; `complete`, `incomplete` or `error`.
(define eager-status (subr asks (state) datum)
  (lambda (st)
    (cond ((not (state-need? st)) (datum-symbol "error"))
          ((settled? (the context (eager-context st))) (datum-symbol "complete"))
          (else (datum-symbol "incomplete")))))

;; `help` and `?`: what a `,help` hole may say.
(define help-name? (subr (read @globals) (string) bool) (lambda (n) (either? n "help" "?")))
(define hole? (subr (read @globals) (datum) bool)
  (lambda (d)
    (and (datum-pair? d)
         (datum-symbol? (datum-car d))
         (string=? (datum-symbol-name (datum-car d)) "unquote")
         (datum-pair? (datum-cdr d))
         (datum-symbol? (datum-car (datum-cdr d)))
         (help-name? (datum-symbol-name (datum-car (datum-cdr d))))
         (datum-null? (datum-cdr (datum-cdr d))))))

(define closing (subr in-context (context closers) datum)
  (lambda (ctx acc)
    (if (null? ctx)
        (datum-bool #f)
        (let ((n (entry-name (car ctx))))
          (cond ((string=? n "top") (datum-string (list->string (the closers (reverse acc)))))
                ((either? n "list" "dotted")
                 (closing (cdr ctx) (cons (datum-char-value (entry-ref (car ctx) 2)) acc)))
                ((string=? n "hash") (closing (cdr ctx) acc))
                (else (datum-bool #f)))))))

;; Whether the newest item a list's mark `e` holds is a `,help` hole.
(define ends-in-hole? (subr (read @globals) (datum) bool)
  (lambda (e)
    (let ((items (entry-ref e 3))) (and (datum-pair? items) (hole? (datum-car items))))))

;; If the newest thing read in the innermost open list is a `,help` hole,
;; the characters that would close every open list; otherwise #f.
(define eager-hole-closers (subr asks (state) datum)
  (lambda (st)
    (let ((ctx (the context (eager-context st))))
      (if (and (not (null? ctx)) (string=? (entry-name (car ctx)) "list") (ends-in-hole? (car ctx)))
          (closing ctx nil)
          (datum-bool #f)))))

(define line-comment (subr reading (cursor) cursor)
  (lambda (cur)
    (marking (entry m-comment (cur-pos cur))
      (lambda ()
        (let ((data (cur-data cur)))
          (letrec ((loop (subr reading (char int) cursor)
                     (lambda (c pos)
                       (if (char=? c #\newline)
                           (make-cursor nil (+ pos 1) data nil)
                           (loop (next-char (+ pos 1) data) (+ pos 1))))))
            (loop (next-char (+ (cur-pos cur) 1) data) (+ (cur-pos cur) 1))))))))

;; `#| … |#`, nesting.
(define block-comment (subr reading (cursor int int) cursor)
  (lambda (cur start depth)
    (marking (entry m-block-comment start)
      (lambda ()
        (let ((c (cur-char cur)))
          (cond ((char=? c #\|)
                 (let ((next (advance cur)))
                   (if (char=? (cur-char next) #\#)
                       (if (= depth 1)
                           (consumed next)
                           (block-comment (advance next) start (- depth 1)))
                       (block-comment next start depth))))
                ((char=? c #\#)
                 (let ((next (advance cur)))
                   (if (char=? (cur-char next) #\|)
                       (block-comment (advance next) start (+ depth 1))
                       (block-comment next start depth))))
                (else (block-comment (advance cur) start depth))))))))

;;; ----------------------------------------------------------------- strings

;; The character a string's escape `\e` stands for, as a code, or -1.
(define escape-code (subr pure (char) int)
  (lambda (e)
    (cond ((char=? e #\n) 10)
          ((char=? e #\t) 9)
          ((char=? e #\r) 13)
          ((char=? e #\a) 7)
          ((char=? e #\b) 8)
          ((char=? e #\0) 0)
          (else -1))))
(define read-string (subr reading (cursor int) result)
  (lambda (cur start)
    (marking (entry m-string start)
      (lambda ()
        (let ((data (cur-data cur)))
          (letrec (;; The character `c` at `pos` in hand, the next read here:
                   ;; a cursor only for an escape, or at the end.
                   (run (subr reading (char int chars) result)
                     (lambda (c pos acc)
                       (cond ((char=? c #\")
                              (cons (atom (datum-string (acc->string acc)) start (+ pos 1))
                                    (make-cursor nil (+ pos 1) data nil)))
                             ((char=? c #\\) (escape (next-at pos data) acc))
                             (else (run (next-char (+ pos 1) data) (+ pos 1) (cons c acc))))))
                   (loop (subr reading (cursor chars) result)
                     (lambda (cur acc) (run (cur-char cur) (cur-pos cur) acc)))
                   (escape (subr reading (cursor chars) result)
                     (lambda (cur acc)
                       (let* ((e (cur-char cur)) (code (escape-code e)))
                         (cond ((>= code 0) (loop (advance cur) (cons (integer->char code) acc)))
                               ((char-in? e "xX") (hex (advance cur) acc nil))
                               ((or (char=? e #\newline) (blank? e))
                                (gap (advance cur) acc e (char=? e #\newline)))
                               (else (loop (advance cur) (cons e acc)))))))
                   (hex (subr reading (cursor chars chars) result)
                     (lambda (cur acc digits)
                       (let ((h (cur-char cur)))
                         (cond ((char=? h #\;)
                                (let ((n (parse-nat (acc->string digits) 16)))
                                  (if (>= n 0)
                                      (loop (advance cur) (cons (integer->char n) acc))
                                      (fail cur "bad `\\x` escape"))))
                               ((hex-digit? h) (hex (advance cur) acc (cons h digits)))
                               (else (fail cur "expected `;` after `\\x` escape"))))))
                   ;; A backslash before a line break: the break and the
                   ;; blanks around it vanish. Before blanks alone, it is
                   ;; the character itself.
                   (gap (subr reading (cursor chars char bool) result)
                     (lambda (cur acc e seen-newline)
                       (let ((g (cur-char cur)))
                         (cond ((and (char=? g #\newline) (not seen-newline))
                                (gap (advance cur) acc e #t))
                               ((blank? g) (gap (advance cur) acc e seen-newline))
                               (seen-newline (loop cur acc))
                               (else (loop cur (cons e acc))))))))
            (loop cur nil)))))))

;; A proper list of exact integers in 0..=255.
(define bytes? (subr (read @globals) (datum) bool)
  (lambda (d)
    (or (datum-null? d)
        (and (datum-pair? d) (datum-byte? (datum-car d)) (bytes? (datum-cdr d))))))

;; The characters up to the next delimiter.
(define read-word (subr reading (cursor) word)
  (lambda (cur)
    (letrec ((loop (subr reading (cursor chars) word)
               (lambda (cur acc)
                 (if (delimiter? (cur-char cur))
                     (cons (acc->string acc) cur)
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
;; The error that `#\name` is a `what` character name.
(define char-name-fail (subr reads (cursor int string string) void)
  (lambda (cur start what name)
    (fail-at cur start (str3 what " character name `#\\" (string-append name "`")))))

;; `#\c`, `#\space`, `#\x41`. The first character is taken whatever it is,
;; and anything after it up to a delimiter makes a name.
(define read-char (subr reading (cursor int) result)
  (lambda (cur start)
    (marking (entry m-char start)
      (lambda ()
        (let* ((first (cur-char cur)) (w (read-word (advance cur))) (rest (car w)) (cur (cdr w)))
          (if (string=? rest "")
              (atom-at (datum-char first) start cur)
              (let* ((name (string-append (char-string first) rest))
                     (lower (string-downcase name))
                     (named (char-name lower)))
                (cond ((>= named 0) (atom-at (datum-char (integer->char named)) start cur))
                      ((and (char=? (string-ref lower 0) #\x) (> (string-length lower) 1))
                       (let ((n (parse-nat (substring lower 1 (string-length lower)) 16)))
                         (if (>= n 0)
                             (atom-at (datum-char (integer->char n)) start cur)
                             (char-name-fail cur start "bad" name))))
                      (else (char-name-fail cur start "unknown" name))))))))))

;;; ------------------------------------------------------------------- atoms
;;; A symbol or a number: which one can only be decided once the whole token
;;; is in hand. `prefix` is text already consumed as part of it (`.` or `#`).

;;; ------------------------------------------------------------------- atoms
;;; A symbol or a number: which one can only be decided once the whole token
;;; is in hand. `prefix` is text already consumed as part of it (`.` or `#`).

;; Where an atom is being read: where it starts, the data read before it,
;; and the text given ahead when it started, with where that starts. While
;; the atom is all in that text (the origin unchanged, as any feed changes
;; it), its text is taken from there at the end, with no list of its
;; characters.
(define-type atom-in (productof (start int) (data syns) (text string) (origin int)))

;; The atom's characters from its start to `pos`, newest first, from the
;; text given ahead.
(define atom-so-far (subr (maxeff (read @globals) (alloc @s)) (atom-in int) chars)
  (lambda (in pos)
    (let ((origin (extract in origin)))
      (chars-back (extract in text) (- (extract in start) origin) (- pos origin)))))
;; What an atom's loop has listed up to `pos`, in `mode` (`atom-loop`).
(define atom-listed (subr (maxeff (read @globals) (alloc @s)) (atom-in int chars int) chars)
  (lambda (in pos acc mode) (if (= mode 0) (atom-so-far in pos) acc)))
;; The atom's text, up to `pos`.
(define atom-text (subr (maxeff (read @globals) (alloc @s)) (atom-in int chars int) string)
  (lambda (in pos acc mode)
    (if (= mode 0)
        (let ((origin (extract in origin)))
          (substring (extract in text) (- (extract in start) origin) (- pos origin)))
        (acc->string acc))))
;; The number `text` reads as, if it may be one and is not escaped; else none.
(define as-number (subr (read @globals) (string bool) data)
  (lambda (text escaped)
    (if (or escaped (not (number-start? (string-ref text 0)))) nil (parse-number text 10))))
;; The atom that ends as `text`, `c` in hand at `cur`: a symbol, or a number.
(define atom-finish (subr reads (atom-in cursor string bool char) result)
  (lambda (in cur text escaped c)
    (if (and (string=? text "") (not escaped))
        (fail cur (str3 "unexpected `" (char-string c) "`"))
        (let ((n (as-number text escaped)))
          (if (null? n)
              (atom-at (datum-symbol text) (extract in start) cur)
              (atom-at (car n) (extract in start) cur))))))

(define-rec
  ;; Each has the character `c` at `pos` in hand, and reads the next itself.
  ;; `mode`: 0, taken whole at the end; 1, listed in `acc`, newest first; 2,
  ;; listed, with an escape.
  (atom-loop (subr reading (atom-in char int chars int) result)
    (lambda (in c pos acc mode)
      (let ((data (extract in data)))
        (cond ((and (= mode 0) (not (= (get ahead-origin) (extract in origin))))
               ;; Fed anew: listed from here on.
               (atom-loop in c pos (atom-so-far in pos) 1))
              ((char=? c #\|)
               (atom-bar in (next-char (+ pos 1) data) (+ pos 1) (atom-listed in pos acc mode)))
              ((char=? c #\\)
               (let* ((acc (atom-listed in pos acc mode)) (e (next-char (+ pos 1) data)))
                 (atom-loop in (next-char (+ pos 2) data) (+ pos 2) (cons e acc) 2)))
              ((delimiter? c)
               (atom-finish in (cursor-at c pos data) (atom-text in pos acc mode) (= mode 2) c))
              (else
               (let ((acc (if (= mode 0) acc (the chars (cons c acc)))))
                 (atom-loop in (next-char (+ pos 1) data) (+ pos 1) acc mode)))))))
  ;; Inside `|…|`.
  (atom-bar (subr reading (atom-in char int chars) result)
    (lambda (in b pos acc)
      (marking (entry m-symbol (extract in start))
        (lambda ()
          (let ((data (extract in data)))
            (cond ((char=? b #\|) (atom-loop in (next-char (+ pos 1) data) (+ pos 1) acc 2))
                  ((char=? b #\\)
                   (let ((e (next-char (+ pos 1) data)))
                     (atom-bar in (next-char (+ pos 2) data) (+ pos 2) (cons e acc))))
                  (else (atom-bar in (next-char (+ pos 1) data) (+ pos 1) (cons b acc))))))))))

(define read-atom-from (subr reading (cursor int string) result)
  (lambda (cur start prefix)
    (marking (entry m-atom start)
      (lambda ()
        (let* ((text (get ahead-text)) (origin (get ahead-origin))
               (in (product (start start) (data (cur-data cur)) (text text) (origin origin)))
               (given (chars-back prefix 0 (string-length prefix))))
          (if (and (string=? prefix "") (in-text? (- start origin) text))
              (atom-loop in (cur-char cur) (cur-pos cur) nil 0)
              (atom-loop in (cur-char cur) (cur-pos cur) given 1)))))))
;;; ------------------------------------------------------ lists, and errors

;; A list read: its items (newest first) `syns` and `items-d`, closed at
;; `cur`.
(define closed-list (subr reads (syns datum int cursor) result)
  (lambda (syns items-d start cur)
    (cons (lst (the syns (reverse syns))
               (datum-reverse-onto items-d no-data)
               start
               (+ (cur-pos cur) 1))
          (consumed cur))))
;; A dotted list read: its items (newest first) `syns` and `items`, and its
;; tail `r`'s, closed at `cur`.
(define closed-dotted (subr reads (syns result data int cursor) result)
  (lambda (syns r items start cur)
    (cons (dotted (the syns (reverse syns))
                  (car r)
                  (datum-dotted (the data (reverse items)) (syn->datum (car r)))
                  start
                  (+ (cur-pos cur) 1))
          (consumed cur))))
;; Whether `cur` is at `close`, not at a `#` whose datum is pending.
(define closes? (subr inspects (cursor char) bool)
  (lambda (cur close) (and (not (hash-pending? cur)) (char=? (cur-char cur) close))))
;; The error that `close` was expected: `what` says what came instead.
(define fail-expected (subr reads (cursor char string) void)
  (lambda (cur close what) (fail cur (str3 "expected `" (char-string close) what))))
;; What was found instead of it, `c`.
(define found-instead (subr (read @globals) (char) string)
  (lambda (c) (str3 "` but found `" (char-string c) "`")))
;; That `c` is reserved in FX-26.
(define reserved-message (subr (read @globals) (char) string)
  (lambda (c) (str3 "`" (char-string c) "` is reserved: it has no meaning yet")))
;; The error of unknown `#` syntax, `#what`, at `start`.
(define unknown-hash (subr reads (cursor int string) void)
  (lambda (cur start what) (fail-at cur start (str3 "unknown `#` syntax: `#" what "`"))))
(define bytes-message string "bytevector elements must be exact integers in 0..=255")

;; `#t`, `#true`, `#f` or `#false`, `cur` at the letter.
(define read-bool (subr reading (cursor int) result)
  (lambda (cur start)
    (let* ((w (read-word cur)) (word (car w)) (lower (string-downcase word)))
      (cond ((either? lower "t" "true") (atom-at (datum-bool #t) start (cdr w)))
            ((either? lower "f" "false") (atom-at (datum-bool #f) start (cdr w)))
            (else (unknown-hash (cdr w) start word))))))

;;; -------------------------------------------------------------- atmosphere

(define-rec
  (skip-atmosphere (subr reading (cursor) cursor)
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
  (read-datum (subr reading (cursor) result)
    (lambda (cur)
      (let ((cur (need cur)))
        (if (hash-pending? cur)
            (read-hash (cur-pos cur) (car (cur-pending cur)))
            (let ((c (cur-char cur)) (start (cur-pos cur)))
              (cond ((char=? c #\() (read-list (advance cur) start #\)))
                    ((and (char-in? c "[]") (fx26?))
                     (fail cur (reserved-message c)))
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
  (read-abbrev (subr reading (cursor int string) result)
    (lambda (cur start name)
      (marking (abbrev-entry start name)
        (lambda ()
          (let ((r (read-datum (skip-atmosphere cur))))
            (cons (lst (the syns (list (atom (datum-symbol name) start (+ start 1)) (car r)))
                       (datum-list2 (datum-symbol name) (syn->datum (car r)))
                       start
                       (cur-pos (cdr r)))
                  (cdr r)))))))
  (read-list (subr reading (cursor int char) result)
    (lambda (cur start close)
      (letrec ((loop (subr reading (cursor data datum syns) result)
                 (lambda (cur items items-d syns)
                   ;; In tail position, so the mark is replaced each time
                   ;; round: it always says what has been read so far.
                   (marking (list-entry m-list start close items-d)
                     (lambda ()
                       (let* ((cur (skip-atmosphere cur))
                              (c (cur-char cur))
                              (plain (not (hash-pending? cur))))
                         (cond ((and plain (char=? c close)) (closed-list syns items-d start cur))
                               ((and plain (char=? c #\]) (fx26?)) (fail cur (reserved-message c)))
                               ((and plain (char-in? c ")]"))
                                (fail-expected cur close (found-instead c)))
                               ((and plain (char=? c #\.)) (dot cur items items-d syns))
                               (else (more (read-datum cur) items items-d syns))))))))
               ;; One more item read, `r`.
               (more (subr reading (result data datum syns) result)
                 (lambda (r items items-d syns)
                   (let ((d (syn->datum (car r))))
                     (loop (cdr r) (cons d items) (datum-cons d items-d) (cons (car r) syns)))))
               ;; After a `.`: the tail of a dotted list, or an atom that
               ;; starts with one.
               (dot (subr reading (cursor data datum syns) result)
                 (lambda (cur items items-d syns)
                   (let ((next (advance cur)))
                     (if (delimiter? (cur-char next))
                         (read-dotted next start close items items-d syns (cur-pos cur))
                         (more (read-atom-from next (cur-pos cur) ".") items items-d syns))))))
        (loop cur nil no-data nil))))
    (read-dotted (subr reading (cursor int char data datum syns int) result)
      (lambda (cur start close items items-d syns dot)
        (marking (list-entry m-dotted start close items-d)
          (lambda ()
            (if (null? items)
                (fail-at cur dot "`.` must follow at least one element")
                (let ((cur (skip-atmosphere cur)))
                  (if (closes? cur close)
                      (fail-at cur dot "expected a datum after `.`")
                      (let* ((r (read-datum cur)) (cur (skip-atmosphere (cdr r))))
                        (if (closes? cur close)
                            (closed-dotted syns r items start cur)
                            (fail-expected cur close "` after the tail of a dotted list"))))))))))
  ;;; --------------------------------------------------------------- `#` syntax
  ;;; `start` is where the `#` was; `cur` is at the character after it.
  (read-hash (subr reading (int cursor) result)
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
                  ((char-in? c "tfTF") (read-bool cur start))
                  ((char-in? c "uU") (read-bytes start cur))
                  ((char-in? c "bBoOdDxXeEiI") (read-atom-from cur start "#"))
                  ((char-numeric? c)
                   (fail-at cur start "datum labels are not supported by the eager reader"))
                  (else (unknown-hash cur start (char-string c)))))))))
  ;; `#u8(…)`, or FX-26's `#u`: `cur` at the `u`.
  (read-bytes (subr reading (int cursor) result)
    (lambda (start cur)
      (let* ((w (read-word cur)) (word (car w)) (cur (cdr w)))
        (cond ((and (string-ci=? word "u") (fx26?))
               ;; FX-26's unit value, beside `#u8(`.
               (atom-at (datum-symbol "#u") start cur))
              ((not (string-ci=? word "u8")) (unknown-hash cur start word))
              ((not (char=? (cur-char cur) #\()) (fail cur "expected `(` after `#u8`"))
              (else
               (let* ((r (read-list (advance cur) start #\))) (d (syn->datum (car r))))
                 (if (bytes? d)
                     (atom-at (datum-list->bytevector d) start (cdr r))
                     ;; The Rust reader points at the element; elements carry
                     ;; no positions here, so this points at `#u8`.
                     (fail-at (cdr r) start bytes-message)))))))))

;;; ------------------------------------------------------------- the driver

;; The cursor `after`, with `s` added to the top-level data.
(define with-datum (subr (maxeff (read @globals) (read @s) (alloc @s)) (cursor syn) cursor)
  (lambda (after s) (make-cursor (cur-look after) (cur-pos after) (cons s (cur-data after)) nil)))
(define read-top (subr reading (cursor) void)
  (lambda (cur)
    (letrec ((loop (subr reading (cursor) void)
               (lambda (cur)
                 (marking (top-entry)
                   (lambda ()
                     (let* ((cur (skip-atmosphere cur)) (r (read-datum cur)))
                       (loop (with-datum (cdr r) (car r)))))))))
      (loop cur))))

;; A reader with nothing read yet, for Scheme or for FX-26.
(define start-reading (subr reading (bool) state)
  (lambda (fx26)
    (eager-run
     (lambda ()
       (with-mark dialect-key fx26
         (lambda () (read-top (make-cursor (cons (next-char 0 nil) nil) 0 nil nil))))))))
(define eager-start (subr reading () state) (lambda () (start-reading #f)))
(define eager-start-fx26 (subr reading () state) (lambda () (start-reading #t)))
