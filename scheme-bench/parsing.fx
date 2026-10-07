;;; PARSING -- Parsing benchmark: a generated scanner and LL(1) parser that
;;; parse the text of nboyer.sch.
;;;
;;; Copyright 2006 William D Clinger.
;;;
;;; Permission to copy this software, in whole or in part, to use this
;;; software for any lawful purpose, and to redistribute this software
;;; is granted subject to the restriction that all copies made of this
;;; software must include this copyright notice in full.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/parsing.scm),
;;; ported to FX-26. Larceny's input: (parsing-benchmark 2500
;;; "inputs/parsing.data"), which parses the file's text 2500 times.
;;; Answer: (should return this list), the last datum in the text.
;;;
;;; What changed:
;;; - The original reads inputs/parsing.data (28 300 characters, the text of
;;;   nboyer.sch) into a string before timing begins; here that string is
;;;   in this file, `input-string` below, exactly the file's text. The
;;;   timed work, parsing the string 2500 times, is the same.
;;; - The data the parser builds are FX-26 `datum`s: `datum-cons` for
;;;   `cons`, `datum-symbol` for `string->symbol`, and so on. The symbols the
;;;   action procedures return (`'quote` ...) are global data, made once, as
;;;   Scheme's constants are.
;;; - The mutable local variables are refs. The token buffer
;;;   (`string_accumulator`, a `make-string` written with `string-set!`) is
;;;   an array of characters, FX-26's strings being immutable; `(substring
;;;   string_accumulator 0 n)` makes the string from a list of those
;;;   characters.
;;; - `case` on characters is `char=?` and `char-in?`; `case` on token kinds
;;;   is `symbol=?` and a search of a list made once, at `acyclic`, which
;;;   nothing writes: so the compilers unroll the search into the tests a
;;;   `case` makes (`TODO.md` §44).
;;; - `string->number` is `parse-nat`: nboyer.sch's numbers are all decimal
;;;   integers with no sign.
;;; - `(char? c)` in state12 is always true, and is #t here.
;;; - The error procedures stop the run with an error (an index out of
;;;   range, since FX-26 has no `error`) and print nothing, FX-26 having no
;;;   output; the parse of this text never calls them.

(define-effect pe (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)))

(define-type syms (listof symbol acyclic))
(define* syms5 (subr (alloc acyclic) (symbol symbol symbol symbol symbol) syms)
  (lambda (a b c d e) (list a b c d e)))
(define* one-of? (subr spin (symbol syms) bool)
  (lambda (t l) (if (null? l) #f (if (symbol=? t (car l)) #t (one-of? t (cdr l))))))

;; The kinds of token each `case` of the parser tests for.
(define k-compound syms (cons 'splicing (syms5 'comma 'backquote 'quote 'lparen 'vecstart)))
(define k-simple syms (syms5 'boolean 'number 'character 'string 'id))
(define k-list syms (list 'lparen 'quote 'backquote 'comma 'splicing))
(define k-abbrev syms (list 'splicing 'comma 'backquote 'quote))
(define k-datum-start syms
  (list 'id 'string 'character 'number 'boolean
        'vecstart 'lparen 'quote 'backquote 'comma 'splicing))
(define k-list3 syms (cons 'rparen (cons 'period k-datum-start)))
(define k-rparen-period syms (list 'rparen 'period))
(define k-valued syms (syms5 'boolean 'character 'id 'number 'string))
(define k-expected syms (list 'backquote 'boolean 'character 'comma 'id 'lparen
                              'number 'quote 'splicing 'string 'vecstart))

(define datum-nil datum (datum-list (the (listof datum @heap) nil)))
(define sym-quasiquote datum (datum-symbol "quasiquote"))
(define sym-quote datum (datum-symbol "quote"))
(define sym-unquote-splicing datum (datum-symbol "unquote-splicing"))
(define sym-unquote datum (datum-symbol "unquote"))
(define sym-eof datum (datum-symbol "eof"))

(define no-chars (arrayof char @heap) (make-array 0 #\space))
(define* error (subr (read @heap) (string) unit)
  (lambda (msg) (begin (array-ref no-chars 0) #u)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; The parser used for benchmarking.
;
; Given a string containing Scheme code, parses the entire
; string and returns the last <datum> read from the string.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define* parse-string (subr pe (string) datum)
  (lambda (input-string)

  ; Constants and local variables.

  (let* (; Constants.

         ; Any character that doesn't appear within nboyer.sch
         ; (or the input file, if different) can be used to
         ; represent end-of-file.

         (eof #\~)

         ; length of longest token allowed
         ; (this allows static allocation in C)

         (max_token_size 1024)

         ; Encodings of error messages.

         (errLongToken 1)                 ; extremely long token
         (errincompletetoken 2)      ; any lexical error, really
         (errLexGenBug 3)                         ; can't happen

         ; State for one-token buffering in lexical analyzer.

         (kindOfNextToken (the (ref symbol @heap) (new 'z1)))      ; valid iff nextTokenIsReady
         (nextTokenIsReady (the (ref bool @heap) (new #f)))

         (tokenValue (the (ref string @heap) (new "")))  ; string associated with current token

         (totalErrors (the (ref int @heap) (new 0)))                         ; errors so far
         (lineNumber (the (ref int @heap) (new 1)))       ; rudimentary source code location
         (lineNumberOfLastError (the (ref int @heap) (new 0)))                       ; ditto

         ; A string buffer for the characters of the current token.

         (string_accumulator (the (arrayof char @heap) (make-array max_token_size #\space)))

         ; Number of characters in string_accumulator.

         (string_accumulator_length (the (ref int @heap) (new 0)))

         ; A single character of buffering.
         ; nextCharacter is valid iff nextCharacterIsReady

         (nextCharacter (the (ref char @heap) (new #\space)))
         (nextCharacterIsReady (the (ref bool @heap) (new #f)))

         ; Index of next character to be read from input-string.

         (input-index (the (ref int @heap) (new 0)))

         (input-length (string-length input-string))
        )

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; LexGen generated the code for the state machine.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (letrec (
    (scanner0 (subr pe () symbol)
      (lambda ()
        (begin
          (letrec ((loop (subr pe (char) unit)
                     (lambda (c)
                       (if (char-whitespace? c)
                           (begin
                             (consumechar)
                             (set string_accumulator_length 0)
                             (loop (scanchar)))
                           #u))))
            (loop (scanchar)))
          (let ((c (scanchar)))
            (if (char=? c eof) (accept 'eof) (state0 c))))))

    (state0 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\`) (begin (consumechar) (accept 'backquote)))
          ((char=? c #\') (begin (consumechar) (accept 'quote)))
          ((char=? c #\)) (begin (consumechar) (accept 'rparen)))
          ((char=? c #\() (begin (consumechar) (accept 'lparen)))
          ((char=? c #\;) (begin (consumechar) (state29 (scanchar))))
          ((char-in? c "+-") (begin (consumechar) (state28 (scanchar))))
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state27 (scanchar))))
          ((char=? c #\.) (begin (consumechar) (state16 (scanchar))))
          ((char-in? c "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!$%&*/:<=>?^_~")
           (begin (consumechar)
                  (state14 (scanchar))))
          ((char=? c #\#) (begin (consumechar) (state13 (scanchar))))
          ((char=? c #\") (begin (consumechar) (state2 (scanchar))))
          ((char=? c #\,) (begin (consumechar) (state1 (scanchar))))
          (else
           (if (char-whitespace? c)
               (begin (consumechar) (state30 (scanchar)))
               (scannererror errincompletetoken))))))
    (state1 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\@) (begin (consumechar) (accept 'splicing)))
          (else (accept 'comma)))))
    (state2 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\") (begin (consumechar) (accept 'string)))
          (else
           (if (isnotdoublequote? c)
               (begin (consumechar) (state2 (scanchar)))
               (scannererror errincompletetoken))))))
    (state3 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\n) (begin (consumechar) (state8 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state4 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\i) (begin (consumechar) (state3 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state5 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\l) (begin (consumechar) (state4 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state6 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\w) (begin (consumechar) (state5 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state7 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\e) (begin (consumechar) (state6 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state8 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\e) (begin (consumechar) (accept 'character)))
          (else (scannererror errincompletetoken)))))
    (state9 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\c) (begin (consumechar) (state8 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state10 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\a) (begin (consumechar) (state9 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state11 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\p) (begin (consumechar) (state10 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state12 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\s) (begin (consumechar) (state11 (scanchar))))
          ((char=? c #\n) (begin (consumechar) (state7 (scanchar))))
          (else
           (if #t
               (begin (consumechar) (accept 'character))
               (scannererror errincompletetoken))))))
    (state13 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\() (begin (consumechar) (accept 'vecstart)))
          ((char-in? c "tf") (begin (consumechar) (accept 'boolean)))
          ((char=? c #\\) (begin (consumechar) (state12 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state14 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!$%&*/:<=>?^_~0123456789+-.@")
           (begin (consumechar)
                  (state14 (scanchar))))
          (else (accept 'id)))))
    (state15 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\.) (begin (consumechar) (accept 'id)))
          (else (scannererror errincompletetoken)))))
    (state16 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state18 (scanchar))))
          ((char=? c #\.) (begin (consumechar) (state15 (scanchar))))
          (else (accept 'period)))))
    (state17 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state18 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state18 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "esfdl")
           (begin (consumechar)
                  (state22 (scanchar))))
          ((char=? c #\#) (begin (consumechar) (state19 (scanchar))))
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state18 (scanchar))))
          (else (accept 'number)))))
    (state19 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "esfdl")
           (begin (consumechar)
                  (state22 (scanchar))))
          ((char=? c #\#) (begin (consumechar) (state19 (scanchar))))
          (else (accept 'number)))))
    (state20 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state20 (scanchar))))
          (else (accept 'number)))))
    (state21 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state20 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state22 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "+-") (begin (consumechar) (state21 (scanchar))))
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state20 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state23 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\#) (begin (consumechar) (state23 (scanchar))))
          (else (accept 'number)))))
    (state24 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state24 (scanchar))))
          ((char=? c #\#) (begin (consumechar) (state23 (scanchar))))
          (else (accept 'number)))))
    (state25 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state24 (scanchar))))
          (else (scannererror errincompletetoken)))))
    (state26 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\#) (begin (consumechar) (state26 (scanchar))))
          ((char=? c #\/) (begin (consumechar) (state25 (scanchar))))
          ((char-in? c "esfdl")
           (begin (consumechar)
                  (state22 (scanchar))))
          ((char=? c #\.) (begin (consumechar) (state19 (scanchar))))
          (else (accept 'number)))))
    (state27 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state27 (scanchar))))
          ((char=? c #\#) (begin (consumechar) (state26 (scanchar))))
          ((char=? c #\/) (begin (consumechar) (state25 (scanchar))))
          ((char-in? c "esfdl")
           (begin (consumechar)
                  (state22 (scanchar))))
          ((char=? c #\.) (begin (consumechar) (state18 (scanchar))))
          (else (accept 'number)))))
    (state28 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char-in? c "0123456789")
           (begin (consumechar)
                  (state27 (scanchar))))
          ((char=? c #\.) (begin (consumechar) (state17 (scanchar))))
          (else (accept 'id)))))
    (state29 (subr pe (char) symbol)
      (lambda (c)
        (cond
          ((char=? c #\newline)
           (begin
             (consumechar)
             (begin
               (set string_accumulator_length 0)
               (state0 (scanchar)))))
          (else
           (if (isnotnewline? c)
               (begin (consumechar) (state29 (scanchar)))
               (scannererror errincompletetoken))))))
    (state30 (subr pe (char) symbol)
      (lambda (c)
        (cond
          (else
           (if (char-whitespace? c)
               (begin (consumechar) (state30 (scanchar)))
               (begin
                 (set string_accumulator_length 0)
                 (state0 (scanchar))))))))
    (state31 (subr pe (char) symbol)
      (lambda (c)
        (cond
          (else
           (begin
             (set string_accumulator_length 0)
             (state0 (scanchar)))))))
    (state32 (subr pe (char) symbol) (lambda (c) (cond (else (accept 'id)))))
    (state33 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'boolean)))))
    (state34 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'character)))))
    (state35 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'vecstart)))))
    (state36 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'string)))))
    (state37 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'lparen)))))
    (state38 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'rparen)))))
    (state39 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'quote)))))
    (state40 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'backquote)))))
    (state41 (subr pe (char) symbol)
      (lambda (c)
        (cond (else (accept 'splicing)))))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; End of state machine generated by LexGen.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; ParseGen generated the code for the strong LL(1) parser.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (parse-datum (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((one-of? t k-compound)
             (let ((ast1 (parse-compound-datum)))
               (identity ast1)))
            ((one-of? t k-simple)
             (let ((ast1 (parse-simple-datum)))
               (identity ast1)))
            (else
             (parse-error
               '<datum>
               k-expected))))))

    (parse-simple-datum (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((symbol=? t 'id)
             (let ((ast1 (parse-symbol))) (identity ast1)))
            ((symbol=? t 'string) (begin (consume-token!) (makeString)))
            ((symbol=? t 'character) (begin (consume-token!) (makeChar)))
            ((symbol=? t 'number) (begin (consume-token!) (makeNum)))
            ((symbol=? t 'boolean) (begin (consume-token!) (makeBool)))
            (else
             (parse-error
               '<simple-datum>
               k-simple))))))

    (parse-symbol (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((symbol=? t 'id) (begin (consume-token!) (makeSym)))
            (else (parse-error '<symbol> k-simple))))))

    (parse-compound-datum (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((symbol=? t 'vecstart)
             (let ((ast1 (parse-vector))) (identity ast1)))
            ((one-of? t k-list)
             (let ((ast1 (parse-list))) (identity ast1)))
            (else
             (parse-error
               '<compound-datum>
               k-compound))))))

    (parse-list (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((one-of? t k-abbrev)
             (let ((ast1 (parse-abbreviation)))
               (identity ast1)))
            ((symbol=? t 'lparen)
             (begin
               (consume-token!)
               (let ((ast1 (parse-list2))) (identity ast1))))
            (else
             (parse-error
               '<list>
               k-list))))))

    (parse-list2 (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((one-of? t k-datum-start)
             (let ((ast1 (parse-datum)))
               (let ((ast2 (parse-list3))) (datum-cons ast1 ast2))))
            ((symbol=? t 'rparen) (begin (consume-token!) (emptyList)))
            (else
             (parse-error
               '<list2>
               k-expected))))))

    (parse-list3 (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((one-of? t k-list3)
             (let ((ast1 (parse-data)))
               (let ((ast2 (parse-list4)))
                 (pseudoAppend ast1 ast2))))
            (else
             (parse-error
               '<list3>
               k-list3))))))

    (parse-list4 (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((symbol=? t 'period)
             (begin
               (consume-token!)
               (let ((ast1 (parse-datum)))
                 (if (symbol=? (next-token) 'rparen)
                     (begin (consume-token!) (identity ast1))
                     (parse-error '<list4> k-rparen-period)))))
            ((symbol=? t 'rparen) (begin (consume-token!) (emptyList)))
            (else (parse-error '<list4> k-rparen-period))))))

    (parse-abbreviation (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((one-of? t k-abbrev)
             (let ((ast1 (parse-abbrev-prefix)))
               (let ((ast2 (parse-datum))) (datum-cons ast1 (datum-cons ast2 datum-nil)))))
            (else
             (parse-error
               '<abbreviation>
               k-abbrev))))))

    (parse-abbrev-prefix (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((symbol=? t 'splicing)
             (begin (consume-token!) (symSplicing)))
            ((symbol=? t 'comma) (begin (consume-token!) (symUnquote)))
            ((symbol=? t 'backquote)
             (begin (consume-token!) (symBackquote)))
            ((symbol=? t 'quote) (begin (consume-token!) (symQuote)))
            (else
             (parse-error
               '<abbrev-prefix>
               k-abbrev))))))

    (parse-vector (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((symbol=? t 'vecstart)
             (begin
               (consume-token!)
               (let ((ast1 (parse-data)))
                 (if (symbol=? (next-token) 'rparen)
                     (begin (consume-token!) (list2vector ast1))
                     (parse-error '<vector> k-rparen-period)))))
            (else (parse-error '<vector> k-compound))))))

    (parse-data (subr pe () datum)
      (lambda ()
        (let ((t (next-token)))
          (cond
            ((one-of? t k-datum-start)
             (let ((ast1 (parse-datum)))
               (let ((ast2 (parse-data))) (datum-cons ast1 ast2))))
            ((one-of? t k-rparen-period) (emptyList))
            (else
             (parse-error
               '<data>
               k-list3))))))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; End of LL(1) parser generated by ParseGen.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; Help predicates used by the lexical analyzer's state machine.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (isnotdoublequote? (subr pe (char) bool) (lambda (c) (not (char=? c #\"))))
    (isnotnewline? (subr pe (char) bool) (lambda (c) (not (char=? c #\newline))))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; Lexical analyzer.
    ;
    ; This code is adapted from the quirk23 lexical analyzer written
    ; by Will Clinger for a compiler course.
    ;
    ; The scanner and parser were generated automatically and then
    ; printed using an R5RS Scheme pretty-printer, so they do not
    ; preserve case.  In preparation for the case-sensitivity of
    ; R6RS Scheme, several identifiers and constants have been
    ; lower-cased in the hand-written code to match the generated
    ; code.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ; next-token and consume-token! are called by the parser.

    ; Returns the current token.

    (next-token (subr pe () symbol)
      (lambda ()
        (if (get nextTokenIsReady)
            (get kindOfNextToken)
            (begin (set string_accumulator_length 0)
                   (scanner0)))))

    ; Consumes the current token.

    (consume-token! (subr pe () unit)
      (lambda ()
        (set nextTokenIsReady #f)))

    ; Called by the lexical analyzer's state machine,
    ; hence the unfortunate lower case.

    (scannererror (subr pe (int) symbol)
      (lambda (msg)
        (let ((msgtxt
               (cond ((= msg errLongToken)
                      "Amazingly long token")
                     ((= msg errincompletetoken)
                      "in line ")
                     ((= msg errLexGenBug)
                      "Bug in lexical analyzer (generated)")
                     (else "Bug in lexical analyzer"))))
          (begin
            (error (string-append "Lexical Error: " msgtxt))
            (set nextTokenIsReady #f)
            (set nextCharacterIsReady #f)
            (next-token)))))

    ; Accepts a token of the given kind, returning that kind.
    ;
    ; For some kinds of tokens, a value for the token must also be
    ; recorded in tokenValue.

    (accept (subr pe (symbol) symbol)
      (lambda (t)
        (begin
          (if (one-of? t k-valued)
              (set tokenValue
                   (accumulated-string (get string_accumulator_length)))
              #u)
          (set kindOfNextToken t)
          (set nextTokenIsReady #t)
          t)))

    ;; (substring string_accumulator 0 n)
    (accumulated-string (subr pe (int) string)
      (lambda (n)
        (letrec ((chars (subr pe (int (listof char @heap)) (listof char @heap))
                   (lambda (i acc)
                     (if (< i 0) acc (chars (- i 1) (cons (array-ref string_accumulator i) acc))))))
          (list->string (chars (- n 1) nil)))))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; Character i/o, so to speak.
    ; Uses the input-string as input.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    ; Returns the current character from the input.

    (scanchar (subr pe () char)
      (lambda ()
        (if (get nextCharacterIsReady)
            (get nextCharacter)
            (begin (if (< (get input-index) input-length)
                       (begin (set nextCharacter
                                   (string-ref input-string (get input-index)))
                              (set input-index (+ (get input-index) 1)))
                       (set nextCharacter eof))
                   (set nextCharacterIsReady #t)
                   (scanchar)))))

    ; Consumes the current character, and returns the next.

    (consumechar (subr pe () unit)
      (lambda ()
        (begin
          (if (not (get nextCharacterIsReady))
              (begin (scanchar) #u)
              #u)
          (if (< (get string_accumulator_length) max_token_size)
              (begin (set nextCharacterIsReady #f)
                     (if (char=? (get nextCharacter) #\newline)
                         (set lineNumber (+ (get lineNumber) 1))
                         #u)
                     (array-set! string_accumulator
                                 (get string_accumulator_length)
                                 (get nextCharacter))
                     (set string_accumulator_length
                          (+ (get string_accumulator_length) 1)))
              (begin (scannererror errLongToken) #u)))))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; Action procedures called by the parser.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (emptyList (subr pe () datum) (lambda () datum-nil))

    (identity (subr pe (datum) datum) (lambda (x) x))

    (list2vector (subr pe (datum) datum) (lambda (vals) (datum-list->vector vals)))

    (makeBool (subr pe () datum)
      (lambda ()
        (datum-bool (string=? (get tokenValue) "#t"))))

    (makeChar (subr pe () datum)
      (lambda ()
        (datum-char (string-ref (get tokenValue) 0))))

    (makeNum (subr pe () datum)
      (lambda ()
        (datum-int (parse-nat (get tokenValue) 10))))

    (makeString (subr pe () datum)
      (lambda ()
        ; Must strip off outer double quotes.
        ; Ought to process escape characters also, but we won't.
        (datum-string (substring (get tokenValue) 1 (- (string-length (get tokenValue)) 1)))))

    (makeSym (subr pe () datum)
      (lambda ()
        (datum-symbol (get tokenValue))))

    ; Like append, but allows the last argument to be a non-list.

    (pseudoAppend (subr pe (datum datum) datum)
      (lambda (vals terminus)
        (if (datum-null? vals)
            terminus
            (datum-cons (datum-car vals)
                        (pseudoAppend (datum-cdr vals) terminus)))))

    (symBackquote (subr pe () datum) (lambda () sym-quasiquote))
    (symQuote (subr pe () datum) (lambda () sym-quote))
    (symSplicing (subr pe () datum) (lambda () sym-unquote-splicing))
    (symUnquote (subr pe () datum) (lambda () sym-unquote))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; Error procedure called by the parser.
    ; As a hack, this error procedure recovers from end-of-file.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (parse-error (subr pe (symbol syms) datum)
      (lambda (nonterminal expected-terminals)
        (if (symbol=? 'eof (next-token))
            sym-eof
            (begin
              (error "Syntax error")
              sym-eof))))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;
    ; Parses repeatedly, returning the last <datum> parsed.
    ;
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (do-loop (subr pe (datum datum) datum)
      (lambda (x y)
        (if (and (datum-symbol? x) (string=? (datum-symbol-name x) "eof"))
            y
            (do-loop (parse-datum) x)))))

    (do-loop (parse-datum) sym-eof)))))

(define* parsing-benchmark (subr pe (int string) datum)
  (lambda (n input-string)
    (letrec ((loop (subr pe (int datum) datum)
               (lambda (i result)
                 (if (= i n)
                     result
                     (loop (+ i 1) (parse-string input-string))))))
      (loop 0 datum-nil))))

;; The text of inputs/parsing.data, which the original reads into a string
;; before timing begins.
(define input-string string ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; File:         nboyer.sch
; Description:  The Boyer benchmark
; Author:       Bob Boyer
; Created:      5-Apr-85
; Modified:     10-Apr-85 14:52:20 (Bob Shaw)
;               22-Jul-87 (Will Clinger)
;               2-Jul-88 (Will Clinger -- distinguished #f and the empty list)
;               13-Feb-97 (Will Clinger -- fixed bugs in unifier and rules,
;                          rewrote to eliminate property lists, and added
;                          a scaling parameter suggested by Bob Boyer)
;               19-Mar-99 (Will Clinger -- cleaned up comments)
;               4-Apr-01 (Will Clinger -- changed four 1- symbols to sub1)
; Language:     Scheme
; Status:       Public Domain
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; NBOYER -- Logic programming benchmark, originally written by Bob Boyer.
;;; Fairly CONS intensive.

; Note:  The version of this benchmark that appears in Dick Gabriel's book
; contained several bugs that are corrected here.  These bugs are discussed
; by Henry Baker, \"The Boyer Benchmark Meets Linear Logic\", ACM SIGPLAN Lisp
; Pointers 6(4), October-December 1993, pages 3-10.  The fixed bugs are:
;
;    The benchmark now returns a boolean result.
;    FALSEP and TRUEP use TERM-MEMBER? rather than MEMV (which is called MEMBER
;         in Common Lisp)
;    ONE-WAY-UNIFY1 now treats numbers correctly
;    ONE-WAY-UNIFY1-LST now treats empty lists correctly
;    Rule 19 has been corrected (this rule was not touched by the original
;         benchmark, but is used by this version)
;    Rules 84 and 101 have been corrected (but these rules are never touched
;         by the benchmark)
;
; According to Baker, these bug fixes make the benchmark 10-25% slower.
; Please do not compare the timings from this benchmark against those of
; the original benchmark.
;
; This version of the benchmark also prints the number of rewrites as a sanity
; check, because it is too easy for a buggy version to return the correct
; boolean result.  The correct number of rewrites is
;
;     n      rewrites       peak live storage (approximate, in bytes)
;     0         95024           520,000
;     1        591777         2,085,000
;     2       1813975         5,175,000
;     3       5375678
;     4      16445406
;     5      51507739

; Nboyer is a 2-phase benchmark.
; The first phase attaches lemmas to symbols.  This phase is not timed,
; but it accounts for very little of the runtime anyway.
; The second phase creates the test problem, and tests to see
; whether it is implied by the lemmas.

(define (nboyer-benchmark . args)
  (let ((n (if (null? args) 0 (car args))))
    (setup-boyer)
    (run-benchmark (string-append \"nboyer\"
                                  (number->string n))
                   1
                   (lambda () (test-boyer n))
                   (lambda (rewrites)
                     (and (number? rewrites)
                          (case n
                           ((0)  (= rewrites 95024))
                           ((1)  (= rewrites 591777))
                           ((2)  (= rewrites 1813975))
                           ((3)  (= rewrites 5375678))
                           ((4)  (= rewrites 16445406))
                           ((5)  (= rewrites 51507739))
                           ; If it works for n <= 5, assume it works.
                           (else #t)))))))

(define (setup-boyer) #t) ; assigned below
(define (test-boyer) #t)  ; assigned below

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; The first phase.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In the original benchmark, it stored a list of lemmas on the
; property lists of symbols.
; In the new benchmark, it maintains an association list of
; symbols and symbol-records, and stores the list of lemmas
; within the symbol-records.

(let ()
  
  (define (setup)
    (add-lemma-lst
     (quote ((equal (compile form)
                    (reverse (codegen (optimize form)
                                      (nil))))
             (equal (eqp x y)
                    (equal (fix x)
                           (fix y)))
             (equal (greaterp x y)
                    (lessp y x))
             (equal (lesseqp x y)
                    (not (lessp y x)))
             (equal (greatereqp x y)
                    (not (lessp x y)))
             (equal (boolean x)
                    (or (equal x (t))
                        (equal x (f))))
             (equal (iff x y)
                    (and (implies x y)
                         (implies y x)))
             (equal (even1 x)
                    (if (zerop x)
                        (t)
                        (odd (sub1 x))))
             (equal (countps- l pred)
                    (countps-loop l pred (zero)))
             (equal (fact- i)
                    (fact-loop i 1))
             (equal (reverse- x)
                    (reverse-loop x (nil)))
             (equal (divides x y)
                    (zerop (remainder y x)))
             (equal (assume-true var alist)
                    (cons (cons var (t))
                          alist))
             (equal (assume-false var alist)
                    (cons (cons var (f))
                          alist))
             (equal (tautology-checker x)
                    (tautologyp (normalize x)
                                (nil)))
             (equal (falsify x)
                    (falsify1 (normalize x)
                              (nil)))
             (equal (prime x)
                    (and (not (zerop x))
                         (not (equal x (add1 (zero))))
                         (prime1 x (sub1 x))))
             (equal (and p q)
                    (if p (if q (t)
                                (f))
                          (f)))
             (equal (or p q)
                    (if p (t)
                          (if q (t)
                                (f))))
             (equal (not p)
                    (if p (f)
                          (t)))
             (equal (implies p q)
                    (if p (if q (t)
                                (f))
                          (t)))
             (equal (fix x)
                    (if (numberp x)
                        x
                        (zero)))
             (equal (if (if a b c)
                        d e)
                    (if a (if b d e)
                          (if c d e)))
             (equal (zerop x)
                    (or (equal x (zero))
                        (not (numberp x))))
             (equal (plus (plus x y)
                          z)
                    (plus x (plus y z)))
             (equal (equal (plus a b)
                           (zero))
                    (and (zerop a)
                         (zerop b)))
             (equal (difference x x)
                    (zero))
             (equal (equal (plus a b)
                           (plus a c))
                    (equal (fix b)
                           (fix c)))
             (equal (equal (zero)
                           (difference x y))
                    (not (lessp y x)))
             (equal (equal x (difference x y))
                    (and (numberp x)
                         (or (equal x (zero))
                             (zerop y))))
             (equal (meaning (plus-tree (append x y))
                             a)
                    (plus (meaning (plus-tree x)
                                   a)
                          (meaning (plus-tree y)
                                   a)))
             (equal (meaning (plus-tree (plus-fringe x))
                             a)
                    (fix (meaning x a)))
             (equal (append (append x y)
                            z)
                    (append x (append y z)))
             (equal (reverse (append a b))
                    (append (reverse b)
                            (reverse a)))
             (equal (times x (plus y z))
                    (plus (times x y)
                          (times x z)))
             (equal (times (times x y)
                           z)
                    (times x (times y z)))
             (equal (equal (times x y)
                           (zero))
                    (or (zerop x)
                        (zerop y)))
             (equal (exec (append x y)
                          pds envrn)
                    (exec y (exec x pds envrn)
                            envrn))
             (equal (mc-flatten x y)
                    (append (flatten x)
                            y))
             (equal (member x (append a b))
                    (or (member x a)
                        (member x b)))
             (equal (member x (reverse y))
                    (member x y))
             (equal (length (reverse x))
                    (length x))
             (equal (member a (intersect b c))
                    (and (member a b)
                         (member a c)))
             (equal (nth (zero)
                         i)
                    (zero))
             (equal (exp i (plus j k))
                    (times (exp i j)
                           (exp i k)))
             (equal (exp i (times j k))
                    (exp (exp i j)
                         k))
             (equal (reverse-loop x y)
                    (append (reverse x)
                            y))
             (equal (reverse-loop x (nil))
                    (reverse x))
             (equal (count-list z (sort-lp x y))
                    (plus (count-list z x)
                          (count-list z y)))
             (equal (equal (append a b)
                           (append a c))
                    (equal b c))
             (equal (plus (remainder x y)
                          (times y (quotient x y)))
                    (fix x))
             (equal (power-eval (big-plus1 l i base)
                                base)
                    (plus (power-eval l base)
                          i))
             (equal (power-eval (big-plus x y i base)
                                base)
                    (plus i (plus (power-eval x base)
                                  (power-eval y base))))
             (equal (remainder y 1)
                    (zero))
             (equal (lessp (remainder x y)
                           y)
                    (not (zerop y)))
             (equal (remainder x x)
                    (zero))
             (equal (lessp (quotient i j)
                           i)
                    (and (not (zerop i))
                         (or (zerop j)
                             (not (equal j 1)))))
             (equal (lessp (remainder x y)
                           x)
                    (and (not (zerop y))
                         (not (zerop x))
                         (not (lessp x y))))
             (equal (power-eval (power-rep i base)
                                base)
                    (fix i))
             (equal (power-eval (big-plus (power-rep i base)
                                          (power-rep j base)
                                          (zero)
                                          base)
                                base)
                    (plus i j))
             (equal (gcd x y)
                    (gcd y x))
             (equal (nth (append a b)
                         i)
                    (append (nth a i)
                            (nth b (difference i (length a)))))
             (equal (difference (plus x y)
                                x)
                    (fix y))
             (equal (difference (plus y x)
                                x)
                    (fix y))
             (equal (difference (plus x y)
                                (plus x z))
                    (difference y z))
             (equal (times x (difference c w))
                    (difference (times c x)
                                (times w x)))
             (equal (remainder (times x z)
                               z)
                    (zero))
             (equal (difference (plus b (plus a c))
                                a)
                    (plus b c))
             (equal (difference (add1 (plus y z))
                                z)
                    (add1 y))
             (equal (lessp (plus x y)
                           (plus x z))
                    (lessp y z))
             (equal (lessp (times x z)
                           (times y z))
                    (and (not (zerop z))
                         (lessp x y)))
             (equal (lessp y (plus x y))
                    (not (zerop x)))
             (equal (gcd (times x z)
                         (times y z))
                    (times z (gcd x y)))
             (equal (value (normalize x)
                           a)
                    (value x a))
             (equal (equal (flatten x)
                           (cons y (nil)))
                    (and (nlistp x)
                         (equal x y)))
             (equal (listp (gopher x))
                    (listp x))
             (equal (samefringe x y)
                    (equal (flatten x)
                           (flatten y)))
             (equal (equal (greatest-factor x y)
                           (zero))
                    (and (or (zerop y)
                             (equal y 1))
                         (equal x (zero))))
             (equal (equal (greatest-factor x y)
                           1)
                    (equal x 1))
             (equal (numberp (greatest-factor x y))
                    (not (and (or (zerop y)
                                  (equal y 1))
                              (not (numberp x)))))
             (equal (times-list (append x y))
                    (times (times-list x)
                           (times-list y)))
             (equal (prime-list (append x y))
                    (and (prime-list x)
                         (prime-list y)))
             (equal (equal z (times w z))
                    (and (numberp z)
                         (or (equal z (zero))
                             (equal w 1))))
             (equal (greatereqp x y)
                    (not (lessp x y)))
             (equal (equal x (times x y))
                    (or (equal x (zero))
                        (and (numberp x)
                             (equal y 1))))
             (equal (remainder (times y x)
                               y)
                    (zero))
             (equal (equal (times a b)
                           1)
                    (and (not (equal a (zero)))
                         (not (equal b (zero)))
                         (numberp a)
                         (numberp b)
                         (equal (sub1 a)
                                (zero))
                         (equal (sub1 b)
                                (zero))))
             (equal (lessp (length (delete x l))
                           (length l))
                    (member x l))
             (equal (sort2 (delete x l))
                    (delete x (sort2 l)))
             (equal (dsort x)
                    (sort2 x))
             (equal (length (cons x1
                                  (cons x2
                                        (cons x3 (cons x4
                                                       (cons x5
                                                             (cons x6 x7)))))))
                    (plus 6 (length x7)))
             (equal (difference (add1 (add1 x))
                                2)
                    (fix x))
             (equal (quotient (plus x (plus x y))
                              2)
                    (plus x (quotient y 2)))
             (equal (sigma (zero)
                           i)
                    (quotient (times i (add1 i))
                              2))
             (equal (plus x (add1 y))
                    (if (numberp y)
                        (add1 (plus x y))
                        (add1 x)))
             (equal (equal (difference x y)
                           (difference z y))
                    (if (lessp x y)
                        (not (lessp y z))
                        (if (lessp z y)
                            (not (lessp y x))
                            (equal (fix x)
                                   (fix z)))))
             (equal (meaning (plus-tree (delete x y))
                             a)
                    (if (member x y)
                        (difference (meaning (plus-tree y)
                                             a)
                                    (meaning x a))
                        (meaning (plus-tree y)
                                 a)))
             (equal (times x (add1 y))
                    (if (numberp y)
                        (plus x (times x y))
                        (fix x)))
             (equal (nth (nil)
                         i)
                    (if (zerop i)
                        (nil)
                        (zero)))
             (equal (last (append a b))
                    (if (listp b)
                        (last b)
                        (if (listp a)
                            (cons (car (last a))
                                  b)
                            b)))
             (equal (equal (lessp x y)
                           z)
                    (if (lessp x y)
                        (equal (t) z)
                        (equal (f) z)))
             (equal (assignment x (append a b))
                    (if (assignedp x a)
                        (assignment x a)
                        (assignment x b)))
             (equal (car (gopher x))
                    (if (listp x)
                        (car (flatten x))
                        (zero)))
             (equal (flatten (cdr (gopher x)))
                    (if (listp x)
                        (cdr (flatten x))
                        (cons (zero)
                              (nil))))
             (equal (quotient (times y x)
                              y)
                    (if (zerop y)
                        (zero)
                        (fix x)))
             (equal (get j (set i val mem))
                    (if (eqp j i)
                        val
                        (get j mem)))))))
  
  (define (add-lemma-lst lst)
    (cond ((null? lst)
           #t)
          (else (add-lemma (car lst))
                (add-lemma-lst (cdr lst)))))
  
  (define (add-lemma term)
    (cond ((and (pair? term)
                (eq? (car term)
                     (quote equal))
                (pair? (cadr term)))
           (put (car (cadr term))
                (quote lemmas)
                (cons
                 (translate-term term)
                 (get (car (cadr term)) (quote lemmas)))))
          (else (error \"ADD-LEMMA did not like term:  \" term))))
  
  ; Translates a term by replacing its constructor symbols by symbol-records.
  
  (define (translate-term term)
    (cond ((not (pair? term))
           term)
          (else (cons (symbol->symbol-record (car term))
                      (translate-args (cdr term))))))
  
  (define (translate-args lst)
    (cond ((null? lst)
           '())
          (else (cons (translate-term (car lst))
                      (translate-args (cdr lst))))))
  
  ; For debugging only, so the use of MAP does not change
  ; the first-order character of the benchmark.
  
  (define (untranslate-term term)
    (cond ((not (pair? term))
           term)
          (else (cons (get-name (car term))
                      (map untranslate-term (cdr term))))))
  
  ; A symbol-record is represented as a vector with two fields:
  ; the symbol (for debugging) and
  ; the list of lemmas associated with the symbol.
  
  (define (put sym property value)
    (put-lemmas! (symbol->symbol-record sym) value))
  
  (define (get sym property)
    (get-lemmas (symbol->symbol-record sym)))
  
  (define (symbol->symbol-record sym)
    (let ((x (assq sym *symbol-records-alist*)))
      (if x
          (cdr x)
          (let ((r (make-symbol-record sym)))
            (set! *symbol-records-alist*
                  (cons (cons sym r)
                        *symbol-records-alist*))
            r))))
  
  ; Association list of symbols and symbol-records.
  
  (define *symbol-records-alist* '())
  
  ; A symbol-record is represented as a vector with two fields:
  ; the symbol (for debugging) and
  ; the list of lemmas associated with the symbol.
  
  (define (make-symbol-record sym)
    (vector sym '()))
  
  (define (put-lemmas! symbol-record lemmas)
    (vector-set! symbol-record 1 lemmas))
  
  (define (get-lemmas symbol-record)
    (vector-ref symbol-record 1))
  
  (define (get-name symbol-record)
    (vector-ref symbol-record 0))
  
  (define (symbol-record-equal? r1 r2)
    (eq? r1 r2))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;
  ; The second phase.
  ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  (define (test n)
    (let ((term
           (apply-subst
            (translate-alist
             (quote ((x f (plus (plus a b)
                                (plus c (zero))))
                     (y f (times (times a b)
                                 (plus c d)))
                     (z f (reverse (append (append a b)
                                           (nil))))
                     (u equal (plus a b)
                              (difference x y))
                     (w lessp (remainder a b)
                              (member a (length b))))))
            (translate-term
             (do ((term
                   (quote (implies (and (implies x y)
                                        (and (implies y z)
                                             (and (implies z u)
                                                  (implies u w))))
                                   (implies x w)))
                   (list 'or term '(f)))
                  (n n (- n 1)))
                 ((zero? n) term))))))
    (tautp term)))
  
  (define (translate-alist alist)
    (cond ((null? alist)
           '())
          (else (cons (cons (caar alist)
                            (translate-term (cdar alist)))
                      (translate-alist (cdr alist))))))
  
  (define (apply-subst alist term)
    (cond ((not (pair? term))
           (let ((temp-temp (assq term alist)))
             (if temp-temp
                 (cdr temp-temp)
                 term)))
          (else (cons (car term)
                      (apply-subst-lst alist (cdr term))))))
  
  (define (apply-subst-lst alist lst)
    (cond ((null? lst)
           '())
          (else (cons (apply-subst alist (car lst))
                      (apply-subst-lst alist (cdr lst))))))
  
  (define (tautp x)
    (tautologyp (rewrite x)
                '() '()))
  
  (define (tautologyp x true-lst false-lst)
    (cond ((truep x true-lst)
           #t)
          ((falsep x false-lst)
           #f)
          ((not (pair? x))
           #f)
          ((eq? (car x) if-constructor)
           (cond ((truep (cadr x)
                         true-lst)
                  (tautologyp (caddr x)
                              true-lst false-lst))
                 ((falsep (cadr x)
                          false-lst)
                  (tautologyp (cadddr x)
                              true-lst false-lst))
                 (else (and (tautologyp (caddr x)
                                        (cons (cadr x)
                                              true-lst)
                                        false-lst)
                            (tautologyp (cadddr x)
                                        true-lst
                                        (cons (cadr x)
                                              false-lst))))))
          (else #f)))
  
  (define if-constructor '*) ; becomes (symbol->symbol-record 'if)
  
  (define rewrite-count 0) ; sanity check
  
  (define (rewrite term)
    (set! rewrite-count (+ rewrite-count 1))
    (cond ((not (pair? term))
           term)
          (else (rewrite-with-lemmas (cons (car term)
                                           (rewrite-args (cdr term)))
                                     (get-lemmas (car term))))))
  
  (define (rewrite-args lst)
    (cond ((null? lst)
           '())
          (else (cons (rewrite (car lst))
                      (rewrite-args (cdr lst))))))
  
  (define (rewrite-with-lemmas term lst)
    (cond ((null? lst)
           term)
          ((one-way-unify term (cadr (car lst)))
           (rewrite (apply-subst unify-subst (caddr (car lst)))))
          (else (rewrite-with-lemmas term (cdr lst)))))
  
  (define unify-subst '*)
  
  (define (one-way-unify term1 term2)
    (begin (set! unify-subst '())
           (one-way-unify1 term1 term2)))
  
  (define (one-way-unify1 term1 term2)
    (cond ((not (pair? term2))
           (let ((temp-temp (assq term2 unify-subst)))
             (cond (temp-temp
                    (term-equal? term1 (cdr temp-temp)))
                   ((number? term2)          ; This bug fix makes
                    (equal? term1 term2))    ; nboyer 10-25% slower!
                   (else
                    (set! unify-subst (cons (cons term2 term1)
                                            unify-subst))
                    #t))))
          ((not (pair? term1))
           #f)
          ((eq? (car term1)
                (car term2))
           (one-way-unify1-lst (cdr term1)
                               (cdr term2)))
          (else #f)))
  
  (define (one-way-unify1-lst lst1 lst2)
    (cond ((null? lst1)
           (null? lst2))
          ((null? lst2)
           #f)
          ((one-way-unify1 (car lst1)
                           (car lst2))
           (one-way-unify1-lst (cdr lst1)
                               (cdr lst2)))
          (else #f)))
  
  (define (falsep x lst)
    (or (term-equal? x false-term)
        (term-member? x lst)))
  
  (define (truep x lst)
    (or (term-equal? x true-term)
        (term-member? x lst)))
  
  (define false-term '*)  ; becomes (translate-term '(f))
  (define true-term '*)   ; becomes (translate-term '(t))
  
  ; The next two procedures were in the original benchmark
  ; but were never used.
  
  (define (trans-of-implies n)
    (translate-term
     (list (quote implies)
           (trans-of-implies1 n)
           (list (quote implies)
                 0 n))))
  
  (define (trans-of-implies1 n)
    (cond ((equal? n 1)
           (list (quote implies)
                 0 1))
          (else (list (quote and)
                      (list (quote implies)
                            (- n 1)
                            n)
                      (trans-of-implies1 (- n 1))))))
  
  ; Translated terms can be circular structures, which can't be
  ; compared using Scheme's equal? and member procedures, so we
  ; use these instead.
  
  (define (term-equal? x y)
    (cond ((pair? x)
           (and (pair? y)
                (symbol-record-equal? (car x) (car y))
                (term-args-equal? (cdr x) (cdr y))))
          (else (equal? x y))))
  
  (define (term-args-equal? lst1 lst2)
    (cond ((null? lst1)
           (null? lst2))
          ((null? lst2)
           #f)
          ((term-equal? (car lst1) (car lst2))
           (term-args-equal? (cdr lst1) (cdr lst2)))
          (else #f)))
  
  (define (term-member? x lst)
    (cond ((null? lst)
           #f)
          ((term-equal? x (car lst))
           #t)
          (else (term-member? x (cdr lst)))))
  
  (set! setup-boyer
        (lambda ()
          (set! *symbol-records-alist* '())
          (set! if-constructor (symbol->symbol-record 'if))
          (set! false-term (translate-term '(f)))
          (set! true-term  (translate-term '(t)))
          (setup)))
  
  (set! test-boyer
        (lambda (n)
          (set! rewrite-count 0)
          (let ((answer (test n)))
            (write rewrite-count)
            (display \" rewrites\")
            (newline)
            (if answer
                rewrite-count
                #f)))))

(should return this list)
")

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define iterations int 2500)

(parsing-benchmark iterations input-string)
