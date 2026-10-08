;;; EARLEY -- Earley's parser, written by Marc Feeley.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/earley.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of
;;; (test (vector->list (make-vector 15 'a))).
;;; Answer: 2674440.
;;;
;;; The parser's tables are arrays, as the original's vectors are, and
;;; its descriptions (the parser's, and the parse `make-parser`'s parser
;;; returns, whose last three fields are procedures) are products, whose
;;; fields `extract` names where the original's `vector-ref` numbers them.
;;; The original's vectors of mixed contents become arrays of one type:
;;; - a state, a vector of the configuration list's head (an int) then
;;;   configuration sets or `#f`, is an array of arrays of ints whose
;;;   slot 0 is an array of one int, the head, and whose `#f` is the empty
;;;   array `no-set` (a set is never empty);
;;; - a configuration set, a vector of ints or `#f`, is an array of ints
;;;   whose `#f` is `no`, -2, which no slot holds otherwise (they hold -1,
;;;   -3 and indexes);
;;; - `ind`'s `#f`, for a non-terminal not there, is -1; `steps`, whose
;;;   every slot is set before it is read, starts at 0, not `#f`.
;;; `conf-set-member?`'s value is only ever tested, so it is a boolean.
;;; The derivation trees and the rules' names, lists of symbols, numbers
;;; and trees, are `datum`s; a token's user information becomes a datum
;;; once, when the token is transformed (`comp-tok`), and a name `#f`,
;;; for a configuration not at the start of a rule, is `#f`.
;;; The lists of trees, and every other list, are FX-26 lists. The
;;; grammar, `((s (a) (s s)))`, is built in the file; its non-terminals
;;; are symbols, and `equal?` of them `symbol=?`. The parser's internal
;;; procedures that use no variable of `make-parser` (all but `ind`,
;;; which is the same as `make-parser`'s own) are top-level definitions,
;;; each after what it calls; and so are the two `ind`s, one definition.
;;; `map`, `member`, `list->vector`, `append` and `length` are written
;;; out; `deriv-trees*`'s `append`, of a list of millions of trees, is
;;; `reverse` then a loop consing it back on, in constant stack, since the
;;; native machine's stack overflows on a recursion that deep (below); `deriv-trees*`, for a non-terminal not in the grammar, gives
;;; `nil` where the original gives `#f`, and `nb-deriv-trees*` 0.

; (make-parser grammar lexer) is used to create a parser from the grammar
; description `grammar' and the lexer function `lexer'.
;
; A grammar is a list of definitions.  Each definition defines a non-terminal
; by a set of rules.  Thus a definition has the form: (nt rule1 rule2...).
; A given non-terminal can only be defined once.  The first non-terminal
; defined is the grammar's goal.  Each rule is a possibly empty list of
; non-terminals.  Thus a rule has the form: (nt1 nt2...).  A non-terminal
; can be any scheme value.  Note that all grammar symbols are treated as
; non-terminals.  This is fine though because the lexer will be outputing
; non-terminals.
;
; The lexer defines what a token is and the mapping between tokens and
; the grammar's non-terminals.  It is a function of one argument, the input,
; that returns the list of tokens corresponding to the input.  Each token is
; represented by a list.  The first element is some `user-defined' information
; associated with the token and the rest represents the token's class(es) (as a
; list of non-terminals that this token corresponds to).
;
; The result of `make-parser' is a function that parses the single input it
; is given into the grammar's goal.  The result is a `parse' which can be
; manipulated with the procedures: `parse->parsed?', `parse->trees'
; and `parse->nb-trees' (see below).
;
; Let's assume that we want a parser for the grammar
;
;  S -> x = E
;  E -> E + E | V
;  V -> V y |
;
; and that the input to the parser is a string of characters.  Also, assume we
; would like to map the characters `x', `y', `+' and `=' into the corresponding
; non-terminals in the grammar.  Such a parser could be created with
;
; (make-parser
;   '(
;      (s (x = e))
;      (e (e + e) (v))
;      (v (v y) ())
;    )
;   (lambda (str)
;     (map (lambda (char)
;            (list char ; user-info = the character itself
;                  (case char
;                    ((#\x) 'x)
;                    ((#\y) 'y)
;                    ((#\+) '+)
;                    ((#\=) '=)
;                    (else (fatal-error "lexer error")))))
;          (string->list str)))
; )
;
; An alternative definition (that does not check for lexical errors) is
;
; (make-parser
;   '(
;      (s (#\x #\= e))
;      (e (e #\+ e) (v))
;      (v (v #\y) ())
;    )
;   (lambda (str) (map (lambda (char) (list char char)) (string->list str)))
; )
;
; To help with the rest of the discussion, here are a few definitions:
;
; An input pointer (for an input of `n' tokens) is a value between 0 and `n'.
; It indicates a point between two input tokens (0 = beginning, `n' = end).
; For example, if `n' = 4, there are 5 input pointers:
;
;   input                   token1     token2     token3     token4
;   input pointers       0          1          2          3          4
;
; A configuration indicates the extent to which a given rule is parsed (this
; is the common `dot notation').  For simplicity, a configuration is
; represented as an integer, with successive configurations in the same
; rule associated with successive integers.  It is assumed that the grammar
; has been extended with rules to aid scanning.  These rules are of the
; form `nt ->', and there is one such rule for every non-terminal.  Note
; that these rules are special because they only apply when the corresponding
; non-terminal is returned by the lexer.
;
; A configuration set is a configuration grouped with the set of input pointers
; representing where the head non-terminal of the configuration was predicted.
;
; Here are the rules and configurations for the grammar given above:
;
;  S -> .         \
;       0          |
;  x -> .          |
;       1          |
;  = -> .          |
;       2          |
;  E -> .          |
;       3           > special rules (for scanning)
;  + -> .          |
;       4          |
;  V -> .          |
;       5          |
;  y -> .          |
;       6         /
;  S -> .  x  .  =  .  E  .
;       7     8     9     10
;  E -> .  E  .  +  .  E  .
;       11    12    13    14
;  E -> .  V  .
;       15    16
;  V -> .  V  .  y  .
;       17    18    19
;  V -> .
;       20
;
; Starters of the non-terminal `nt' are configurations that are leftmost
; in a non-special rule for `nt'.  Enders of the non-terminal `nt' are
; configurations that are rightmost in any rule for `nt'.  Predictors of the
; non-terminal `nt' are configurations that are directly to the left of `nt'
; in any rule.
;
; For the grammar given above,
;
;   Starters of V   = (17 20)
;   Enders of V     = (5 19 20)
;   Predictors of V = (15 17)

(define-type ints (listof int @heap))
(define-type iarr (arrayof int @heap))
(define-type state (arrayof iarr @heap))
(define-type states (arrayof state @heap))
(define-type classes (arrayof ints @heap))
(define-type ntv (arrayof symbol @heap))
(define-type tok (pairof datum ints @heap))
(define-type toks (arrayof tok @heap))
(define-type names (arrayof datum @heap))
(define-type symbols (listof symbol @heap))
(define-type grammar (listof (pairof symbol (listof symbols @heap) @heap) @heap))
(define-type trees (listof datum @heap))

;; What the parser does: read, write and build its tables and trees,
;; loop, and call its procedures.
(define-effect ear
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals no no-set map member list->vector datum-append length ind
                         non-terminals nb-configurations setup-tables
                         comp-tok input->tokens make-states conf-set-get conf-set-get*
                         conf-set-merge-new! conf-set-head conf-set-next conf-set-member?
                         conf-set-adjoin conf-set-adjoin* conf-set-adjoin** conf-set-union
                         forw forward produce back backward parsed? deriv-trees deriv-trees*
                         nb-deriv-trees nb-deriv-trees* make-parser))))

(define-type lexer (subr ear (symbols) (listof symbols @heap)))
(define-type parse
  (productof (nts ntv) (starters classes) (enders classes) (predictors classes)
             (steps iarr) (names names) (toks toks) (states states)
             (parsed? (subr ear (symbol int int ntv classes states) bool))
             (deriv-trees* (subr ear (symbol int int ntv classes iarr names toks states) trees))
             (nb-deriv-trees* (subr ear (symbol int int ntv classes iarr toks states) int))))

;; `#f`, in a configuration set; and a state's `#f` set.
(define no int -2)
(define no-set iarr (make-array 0 0))

(define map
  (poly ((s type) (t type) (e effect))
    (subr (maxeff e (read @heap) (alloc @heap) spin) ((subr e (s) t) (listof s @heap)) (listof t @heap)))
  (plambda ((s type) (t type) (e effect))
    (lambda (f l)
      (letrec ((loop (subr (maxeff e (read @heap) (alloc @heap) spin) ((listof s @heap)) (listof t @heap))
                 (lambda (l) (if (null? l) nil (cons (f (car l)) (loop (cdr l)))))))
        (loop l)))))

(define* member (subr (maxeff (read @heap) spin) (symbol symbols) bool)
  (lambda (x l)
    (cond ((null? l) #f)
          ((symbol=? x (car l)) #t)
          (else (member x (cdr l))))))

(define length
  (poly ((t type)) (subr (maxeff (read @heap) spin) ((listof t @heap)) int))
  (plambda ((t type))
    (lambda (l)
      (letrec ((loop (subr (maxeff (read @heap) spin) ((listof t @heap) int) int)
                 (lambda (l n) (if (null? l) n (loop (cdr l) (+ n 1))))))
        (loop l 0)))))

(define list->vector
  (poly ((t type))
    (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read (globals length))) ((listof t @heap) t) (arrayof t @heap)))
  (plambda ((t type))
    (lambda (l fill)                    ; `fill`: what the array is made with
      (let ((v (the (arrayof t @heap) (make-array (length l) fill))))
        (letrec ((loop (subr (maxeff (read @heap) (write @heap) spin) ((listof t @heap) int) (arrayof t @heap))
                   (lambda (l i)
                     (if (null? l) v (begin (array-set! v i (car l)) (loop (cdr l) (+ i 1)))))))
          (loop l 0))))))

;; `append` of two lists, as data.
(define* datum-append (subr spin (datum datum) datum)
  (lambda (xs ys)
    (if (null? xs) ys (cons (car xs) (datum-append (cdr xs) ys)))))

(define* non-terminals (subr ear (grammar) ntv) ; return vector of non-terminals in grammar
  (lambda (grammar)
    (letrec ((add-nt (subr ear (symbol symbols) symbols)
               (lambda (nt nts)
                 (if (member nt nts) nts (cons nt nts)))) ; use equal? for equality tests
             (def-loop (subr ear (grammar symbols) ntv)
               (lambda (defs nts)
                 (if (not (null? defs))
                     (let* ((def (car defs))
                            (head (car def)))
                       (letrec ((rule-loop (subr ear ((listof symbols @heap) symbols) ntv)
                                  (lambda (rules nts)
                                    (if (not (null? rules))
                                        (let ((rule (car rules)))
                                          (letrec ((loop (subr ear (symbols symbols) ntv)
                                                     (lambda (l nts)
                                                       (if (not (null? l))
                                                           (let ((nt (car l)))
                                                             (loop (cdr l) (add-nt nt nts)))
                                                           (rule-loop (cdr rules) nts)))))
                                            (loop rule nts)))
                                        (def-loop (cdr defs) nts)))))
                         (rule-loop (cdr def) (add-nt head nts))))
                     (list->vector (the symbols (reverse nts)) 'none))))) ; goal non-terminal must be at index 0
      (def-loop grammar nil))))

(define* ind (subr (read @heap) (symbol ntv) int) ; return index of non-terminal `nt' in `nts'
  (lambda (nt nts)
    (letrec ((loop (subr (read @heap) (int) int)
               (lambda (i)
                 (if (>= i 0)
                     (if (symbol=? (array-ref nts i) nt) i (loop (- i 1)))
                     -1))))
      (loop (- (array-length nts) 1)))))

(define* nb-configurations (subr ear (grammar) int) ; return nb of configurations in grammar
  (lambda (grammar)
    (letrec ((def-loop (subr ear (grammar int) int)
               (lambda (defs nb-confs)
                 (if (not (null? defs))
                     (let ((def (car defs)))
                       (letrec ((rule-loop (subr ear ((listof symbols @heap) int) int)
                                  (lambda (rules nb-confs)
                                    (if (not (null? rules))
                                        (let ((rule (car rules)))
                                          (letrec ((loop (subr ear (symbols int) int)
                                                     (lambda (l nb-confs)
                                                       (if (not (null? l))
                                                           (loop (cdr l) (+ nb-confs 1))
                                                           (rule-loop (cdr rules) (+ nb-confs 1))))))
                                            (loop rule nb-confs)))
                                        (def-loop (cdr defs) nb-confs)))))
                         (rule-loop (cdr def) nb-confs)))
                     nb-confs))))
      (def-loop grammar 0))))

; First, associate a numeric identifier to every non-terminal in the
; grammar (with the goal non-terminal associated with 0).
;
; So, for the grammar given above we get:
;
; s -> 0   x -> 1   = -> 4   e ->3    + -> 4   v -> 5   y -> 6

(define* setup-tables (subr ear (grammar ntv classes classes classes iarr names) unit)
  (lambda (grammar nts starters enders predictors steps names)
    (letrec ((add-conf (subr ear (int symbol ntv classes) unit)
               (lambda (conf nt nts class)
                 (let ((i (ind nt nts)))
                   (array-set! class i (cons conf (array-ref class i)))))))
      (let ((nb-nts (array-length nts)))
        (letrec ((nt-loop (subr ear (int) unit)
                   (lambda (i)
                     (if (>= i 0)
                         (begin
                           (array-set! steps i (- i nb-nts))
                           (array-set! names i (cons (string->symbol (symbol->string (array-ref nts i)))
                                                     (cons 0
                                                           nil)))
                           (array-set! enders i (cons i nil))
                           (nt-loop (- i 1)))
                         #u)))
                 (def-loop (subr ear (grammar int) unit)
                   (lambda (defs conf)
                     (if (not (null? defs))
                         (let* ((def (car defs))
                                (head (car def)))
                           (letrec ((rule-loop (subr ear ((listof symbols @heap) int int) unit)
                                      (lambda (rules conf rule-num)
                                        (if (not (null? rules))
                                            (let ((rule (car rules)))
                                              (begin
                                                (array-set! names conf (cons (string->symbol (symbol->string head))
                                                                             (cons rule-num
                                                                                   nil)))
                                                (add-conf conf head nts starters)
                                                (letrec ((loop (subr ear (symbols int) unit)
                                                           (lambda (l conf)
                                                             (if (not (null? l))
                                                                 (let ((nt (car l)))
                                                                   (begin
                                                                     (array-set! steps conf (ind nt nts))
                                                                     (add-conf conf nt nts predictors)
                                                                     (loop (cdr l) (+ conf 1))))
                                                                 (begin
                                                                   (array-set! steps conf (- (ind head nts) nb-nts))
                                                                   (add-conf conf head nts enders)
                                                                   (rule-loop (cdr rules) (+ conf 1) (+ rule-num 1)))))))
                                                  (loop rule conf))))
                                            (def-loop (cdr defs) conf)))))
                             (rule-loop (cdr def) conf 1)))
                         #u))))
          (begin
            (nt-loop (- nb-nts 1))
            (def-loop grammar (array-length nts))))))))

;; The parser's procedures.

(define* comp-tok (subr ear (symbols ntv) tok) ; transform token to parsing format
  (lambda (tok nts)
    (letrec ((loop (subr ear (symbols ints) tok)
               (lambda (l1 l2)
                 (if (not (null? l1))
                     (let ((i (ind (car l1) nts)))
                       (if (>= i 0)
                           (loop (cdr l1) (cons i l2))
                           (loop (cdr l1) l2)))
                     (cons (string->symbol (symbol->string (car tok))) (the ints (reverse l2)))))))
      (loop (cdr tok) nil))))

(define* input->tokens (subr ear (symbols lexer ntv) toks)
  (lambda (input lexer nts)
    (let ((l (map (lambda (tok) (comp-tok tok nts)) (lexer input))))
      (if (null? l)
          (the toks (make-array 0 (cons #f nil)))
          (list->vector l (car l))))))

(define* make-states (subr ear (int int) states)
  (lambda (nb-toks nb-confs)
    (let ((states (the states (make-array (+ nb-toks 1) (the state (make-array 0 no-set))))))
      (letrec ((loop (subr ear (int) states)
                 (lambda (i)
                   (if (>= i 0)
                       (let ((v (the state (make-array (+ nb-confs 1) no-set))))
                         (begin
                           (array-set! v 0 (make-array 1 -1))
                           (array-set! states i v)
                           (loop (- i 1))))
                       states))))
        (loop nb-toks)))))

(define* conf-set-get (subr (read @heap) (state int) iarr)
  (lambda (state conf)
    (array-ref state (+ conf 1))))

(define* conf-set-get* (subr ear (state int int) iarr)
  (lambda (state state-num conf)
    (let ((conf-set (conf-set-get state conf)))
      (if (> (array-length conf-set) 0)
          conf-set
          (let ((conf-set (the iarr (make-array (+ state-num 6) no))))
            (begin
              (array-set! conf-set 1 -3) ; old elems tail (points to head)
              (array-set! conf-set 2 -1) ; old elems head
              (array-set! conf-set 3 -1) ; new elems tail (points to head)
              (array-set! conf-set 4 -1) ; new elems head
              (array-set! state (+ conf 1) conf-set)
              conf-set))))))

(define* conf-set-merge-new! (subr (maxeff (read @heap) (write @heap)) (iarr) unit)
  (lambda (conf-set)
    (begin
      (array-set! conf-set
                  (+ (array-ref conf-set 1) 5)
                  (array-ref conf-set 4))
      (array-set! conf-set 1 (array-ref conf-set 3))
      (array-set! conf-set 3 -1)
      (array-set! conf-set 4 -1))))

(define* conf-set-head (subr (read @heap) (iarr) int)
  (lambda (conf-set)
    (array-ref conf-set 2)))

(define* conf-set-next (subr (read @heap) (iarr int) int)
  (lambda (conf-set i)
    (array-ref conf-set (+ i 5))))

(define* conf-set-member? (subr ear (state int int) bool)
  (lambda (state conf i)
    (let ((conf-set (array-ref state (+ conf 1))))
      (if (> (array-length conf-set) 0)
          (not (= (conf-set-next conf-set i) no))
          #f))))

(define* conf-set-adjoin (subr ear (state iarr int int) unit)
  (lambda (state conf-set conf i)
    (let ((tail (array-ref conf-set 3))) ; put new element at tail
      (begin
        (array-set! conf-set (+ i 5) -1)
        (array-set! conf-set (+ tail 5) i)
        (array-set! conf-set 3 i)
        (if (< tail 0)
            (begin
              (array-set! conf-set 0 (array-ref (array-ref state 0) 0))
              (array-set! (array-ref state 0) 0 conf))
            #u)))))

(define* conf-set-adjoin* (subr ear (states int ints int) unit)
  (lambda (states state-num l i)
    (let ((state (array-ref states state-num)))
      (letrec ((loop (subr ear (ints) unit)
                 (lambda (l1)
                   (if (not (null? l1))
                       (let* ((conf (car l1))
                              (conf-set (conf-set-get* state state-num conf)))
                         (if (= (conf-set-next conf-set i) no)
                             (begin
                               (conf-set-adjoin state conf-set conf i)
                               (loop (cdr l1)))
                             (loop (cdr l1))))
                       #u))))
        (loop l)))))

(define* conf-set-adjoin** (subr ear (states states int int int) bool)
  (lambda (states states* state-num conf i)
    (let ((state (array-ref states state-num)))
      (if (conf-set-member? state conf i)
          (let* ((state* (array-ref states* state-num))
                 (conf-set* (conf-set-get* state* state-num conf)))
            (begin
              (if (= (conf-set-next conf-set* i) no)
                  (conf-set-adjoin state* conf-set* conf i)
                  #u)
              #t))
          #f))))

(define* conf-set-union (subr ear (state iarr int iarr) unit)
  (lambda (state conf-set conf other-set)
    (letrec ((loop (subr ear (int) unit)
               (lambda (i)
                 (if (>= i 0)
                     (if (= (conf-set-next conf-set i) no)
                         (begin
                           (conf-set-adjoin state conf-set conf i)
                           (loop (conf-set-next other-set i)))
                         (loop (conf-set-next other-set i)))
                     #u))))
      (loop (conf-set-head other-set)))))

(define* forw (subr ear (states int classes classes classes iarr ntv) unit)
  (lambda (states state-num starters enders predictors steps nts)
    (letrec ((predict (subr ear (state int iarr int int classes classes) unit)
               (lambda (state state-num conf-set conf nt starters enders)

                 ; add configurations which start the non-terminal `nt' to the
                 ; right of the dot

                 (letrec ((loop1 (subr ear (ints) unit)
                            (lambda (l)
                              (if (not (null? l))
                                  (let* ((starter (car l))
                                         (starter-set (conf-set-get* state state-num starter)))
                                    (if (= (conf-set-next starter-set state-num) no)
                                        (begin
                                          (conf-set-adjoin state starter-set starter state-num)
                                          (loop1 (cdr l)))
                                        (loop1 (cdr l))))
                                  #u)))

                          ; check for possible completion of the non-terminal `nt' to the
                          ; right of the dot

                          (loop2 (subr ear (ints) unit)
                            (lambda (l)
                              (if (not (null? l))
                                  (let ((ender (car l)))
                                    (if (conf-set-member? state ender state-num)
                                        (let* ((next (+ conf 1))
                                               (next-set (conf-set-get* state state-num next)))
                                          (begin
                                            (conf-set-union state next-set next conf-set)
                                            (loop2 (cdr l))))
                                        (loop2 (cdr l))))
                                  #u))))
                   (begin
                     (loop1 (array-ref starters nt))
                     (loop2 (array-ref enders nt))))))

             (reduce (subr ear (states state int iarr int ints) unit)
               (lambda (states state state-num conf-set head preds)

                 ; a non-terminal is now completed so check for reductions that
                 ; are now possible at the configurations `preds'

                 (letrec ((loop1 (subr ear (ints) unit)
                            (lambda (l)
                              (if (not (null? l))
                                  (let ((pred (car l)))
                                    (letrec ((loop2 (subr ear (int) unit)
                                               (lambda (i)
                                                 (if (>= i 0)
                                                     (let ((pred-set (conf-set-get (array-ref states i) pred)))
                                                       (begin
                                                         (if (> (array-length pred-set) 0)
                                                             (let* ((next (+ pred 1))
                                                                    (next-set (conf-set-get* state state-num next)))
                                                               (conf-set-union state next-set next pred-set))
                                                             #u)
                                                         (loop2 (conf-set-next conf-set i))))
                                                     (loop1 (cdr l))))))
                                      (loop2 head)))
                                  #u))))
                   (loop1 preds)))))

      (let ((state (array-ref states state-num))
            (nb-nts (array-length nts)))
        (letrec ((loop (subr ear () unit)
                   (lambda ()
                     (let ((conf (array-ref (array-ref state 0) 0)))
                       (if (>= conf 0)
                           (let* ((step (array-ref steps conf))
                                  (conf-set (array-ref state (+ conf 1)))
                                  (head (array-ref conf-set 4)))
                             (begin
                               (array-set! (array-ref state 0) 0 (array-ref conf-set 0))
                               (conf-set-merge-new! conf-set)
                               (if (>= step 0)
                                   (predict state state-num conf-set conf step starters enders)
                                   (let ((preds (array-ref predictors (+ step nb-nts))))
                                     (reduce states state state-num conf-set head preds)))
                               (loop)))
                           #u)))))
          (loop))))))

(define* forward (subr ear (classes classes classes iarr ntv toks) states)
  (lambda (starters enders predictors steps nts toks)
    (let* ((nb-toks (array-length toks))
           (nb-confs (array-length steps))
           (states (make-states nb-toks nb-confs))
           (goal-starters (array-ref starters 0)))
      (begin
        (conf-set-adjoin* states 0 goal-starters 0) ; predict goal
        (forw states 0 starters enders predictors steps nts)
        (letrec ((loop (subr ear (int) unit)
                   (lambda (i)
                     (if (< i nb-toks)
                         (let ((tok-nts (cdr (array-ref toks i))))
                           (begin
                             (conf-set-adjoin* states (+ i 1) tok-nts i) ; scan token
                             (forw states (+ i 1) starters enders predictors steps nts)
                             (loop (+ i 1))))
                         #u))))
          (loop 0))
        states))))

(define* produce (subr ear (int int int classes iarr toks states states int) unit)
  (lambda (conf i j enders steps toks states states* nb-nts)
    (let ((prev (- conf 1)))
      (if (and (>= conf nb-nts) (>= (array-ref steps prev) 0))
          (letrec ((loop1 (subr ear (ints) unit)
                     (lambda (l)
                       (if (not (null? l))
                           (let* ((ender (car l))
                                  (ender-set (conf-set-get (array-ref states j)
                                                           ender)))
                             (if (> (array-length ender-set) 0)
                                 (letrec ((loop2 (subr ear (int) unit)
                                            (lambda (k)
                                              (if (>= k 0)
                                                  (begin
                                                    (and (>= k i)
                                                         (conf-set-adjoin** states states* k prev i)
                                                         (conf-set-adjoin** states states* j ender k))
                                                    (loop2 (conf-set-next ender-set k)))
                                                  (loop1 (cdr l))))))
                                   (loop2 (conf-set-head ender-set)))
                                 (loop1 (cdr l))))
                           #u))))
            (loop1 (array-ref enders (array-ref steps prev))))
          #u))))

(define* back (subr ear (states states int classes iarr int toks) unit)
  (lambda (states states* state-num enders steps nb-nts toks)
    (let ((state* (array-ref states* state-num)))
      (letrec ((loop1 (subr ear () unit)
                 (lambda ()
                   (let ((conf (array-ref (array-ref state* 0) 0)))
                     (if (>= conf 0)
                         (let* ((conf-set (array-ref state* (+ conf 1)))
                                (head (array-ref conf-set 4)))
                           (begin
                             (array-set! (array-ref state* 0) 0 (array-ref conf-set 0))
                             (conf-set-merge-new! conf-set)
                             (letrec ((loop2 (subr ear (int) unit)
                                        (lambda (i)
                                          (if (>= i 0)
                                              (begin
                                                (produce conf i state-num enders steps
                                                         toks states states* nb-nts)
                                                (loop2 (conf-set-next conf-set i)))
                                              (loop1)))))
                               (loop2 head))))
                         #u)))))
        (loop1)))))

(define* backward (subr ear (states classes iarr ntv toks) states)
  (lambda (states enders steps nts toks)
    (let* ((nb-toks (array-length toks))
           (nb-confs (array-length steps))
           (nb-nts (array-length nts))
           (states* (make-states nb-toks nb-confs))
           (goal-enders (array-ref enders 0)))
      (begin
        (letrec ((loop1 (subr ear (ints) unit)
                   (lambda (l)
                     (if (not (null? l))
                         (let ((conf (car l)))
                           (begin
                             (conf-set-adjoin** states states* nb-toks conf 0)
                             (loop1 (cdr l))))
                         #u))))
          (loop1 goal-enders))
        (letrec ((loop2 (subr ear (int) unit)
                   (lambda (i)
                     (if (>= i 0)
                         (begin
                           (back states states* i enders steps nb-nts toks)
                           (loop2 (- i 1)))
                         #u))))
          (loop2 nb-toks))
        states*))))

(define* parsed? (subr ear (symbol int int ntv classes states) bool)
  (lambda (nt i j nts enders states)
    (let ((nt* (ind nt nts)))
      (if (>= nt* 0)
          (let ((nb-nts (array-length nts)))
            (letrec ((loop (subr ear (ints) bool)
                       (lambda (l)
                         (if (not (null? l))
                             (let ((conf (car l)))
                               (if (conf-set-member? (array-ref states j) conf i)
                                   #t
                                   (loop (cdr l))))
                             #f))))
              (loop (array-ref enders nt*))))
          #f))))

(define* deriv-trees (subr ear (int int int classes iarr names toks states int) trees)
  (lambda (conf i j enders steps names toks states nb-nts)
    (let ((name (array-ref names conf)))

      (if (not (bool? name)) ; `conf' is at the start of a rule (either special or not)
          (if (< conf nb-nts)
              (cons (cons name (cons (car (array-ref toks i)) nil))
                    nil)
              (cons (cons name nil)
                    nil))

          (let ((prev (- conf 1)))
            (letrec ((loop1 (subr ear (ints trees) trees)
                       (lambda (l1 l2)
                         (if (not (null? l1))
                             (let* ((ender (car l1))
                                    (ender-set (conf-set-get (array-ref states j)
                                                             ender)))
                               (if (> (array-length ender-set) 0)
                                   (letrec ((loop2 (subr ear (int trees) trees)
                                              (lambda (k l2)
                                                (if (>= k 0)
                                                    (if (and (>= k i)
                                                             (conf-set-member? (array-ref states k)
                                                                               prev i))
                                                        (let ((prev-trees
                                                               (deriv-trees prev i k enders steps names
                                                                            toks states nb-nts))
                                                              (ender-trees
                                                               (deriv-trees ender k j enders steps names
                                                                            toks states nb-nts)))
                                                          (letrec ((loop3 (subr ear (trees trees) trees)
                                                                     (lambda (l3 l2)
                                                                       (if (not (null? l3))
                                                                           (let ((ender-tree (the datum (cons (car l3) nil))))
                                                                             (letrec ((loop4 (subr ear (trees trees) trees)
                                                                                        (lambda (l4 l2)
                                                                                          (if (not (null? l4))
                                                                                              (loop4 (cdr l4)
                                                                                                     (cons (datum-append (car l4)
                                                                                                                         ender-tree)
                                                                                                           l2))
                                                                                              (loop3 (cdr l3) l2)))))
                                                                               (loop4 prev-trees l2)))
                                                                           (loop2 (conf-set-next ender-set k) l2)))))
                                                            (loop3 ender-trees l2)))
                                                        (loop2 (conf-set-next ender-set k) l2))
                                                    (loop1 (cdr l1) l2)))))
                                     (loop2 (conf-set-head ender-set) l2))
                                   (loop1 (cdr l1) l2)))
                             l2))))
              (loop1 (array-ref enders (array-ref steps prev)) nil)))))))

(define* deriv-trees* (subr ear (symbol int int ntv classes iarr names toks states) trees)
  (lambda (nt i j nts enders steps names toks states)
    (let ((nt* (ind nt nts)))
      (if (>= nt* 0)
          (let ((nb-nts (array-length nts)))
            (letrec ((loop (subr ear (ints trees) trees)
                       (lambda (l trees)
                         (if (not (null? l))
                             (let ((conf (car l)))
                               (if (conf-set-member? (array-ref states j) conf i)
                                   (loop (cdr l)
                                         (letrec ((rev-append (subr ear (trees trees) trees)
                                                    (lambda (xs ys) (if (null? xs) ys (rev-append (cdr xs) (cons (car xs) ys))))))
                                           ;; (append l trees), in constant stack
                                           (rev-append (the trees (reverse (deriv-trees conf i j enders steps names
                                                                                        toks states nb-nts)))
                                                       trees)))
                                   (loop (cdr l) trees)))
                             trees))))
              (loop (array-ref enders nt*) nil)))
          nil))))

(define* nb-deriv-trees (subr ear (int int int classes iarr toks states int) int)
  (lambda (conf i j enders steps toks states nb-nts)
    (let ((prev (- conf 1)))
      (if (or (< conf nb-nts) (< (array-ref steps prev) 0))
          1
          (letrec ((loop1 (subr ear (ints int) int)
                     (lambda (l n)
                       (if (not (null? l))
                           (let* ((ender (car l))
                                  (ender-set (conf-set-get (array-ref states j)
                                                           ender)))
                             (if (> (array-length ender-set) 0)
                                 (letrec ((loop2 (subr ear (int int) int)
                                            (lambda (k n)
                                              (if (>= k 0)
                                                  (if (and (>= k i)
                                                           (conf-set-member? (array-ref states k)
                                                                             prev i))
                                                      (let ((nb-prev-trees
                                                             (nb-deriv-trees prev i k enders steps
                                                                             toks states nb-nts))
                                                            (nb-ender-trees
                                                             (nb-deriv-trees ender k j enders steps
                                                                             toks states nb-nts)))
                                                        (loop2 (conf-set-next ender-set k)
                                                               (+ n (* nb-prev-trees nb-ender-trees))))
                                                      (loop2 (conf-set-next ender-set k) n))
                                                  (loop1 (cdr l) n)))))
                                   (loop2 (conf-set-head ender-set) n))
                                 (loop1 (cdr l) n)))
                           n))))
            (loop1 (array-ref enders (array-ref steps prev)) 0))))))

(define* nb-deriv-trees* (subr ear (symbol int int ntv classes iarr toks states) int)
  (lambda (nt i j nts enders steps toks states)
    (let ((nt* (ind nt nts)))
      (if (>= nt* 0)
          (let ((nb-nts (array-length nts)))
            (letrec ((loop (subr ear (ints int) int)
                       (lambda (l nb-trees)
                         (if (not (null? l))
                             (let ((conf (car l)))
                               (if (conf-set-member? (array-ref states j) conf i)
                                   (loop (cdr l)
                                         (+ (nb-deriv-trees conf i j enders steps
                                                            toks states nb-nts)
                                            nb-trees))
                                   (loop (cdr l) nb-trees)))
                             nb-trees))))
              (loop (array-ref enders nt*) 0)))
          0))))

(define* make-parser (subr ear (grammar lexer) (subr ear (symbols) parse))
  (lambda (grammar lexer)
    (let* ((nts (non-terminals grammar))          ; id map = list of non-terms
           (nb-nts (array-length nts))           ; the number of non-terms
           (nb-confs (+ (nb-configurations grammar) nb-nts)) ; the nb of confs
           (starters (the classes (make-array nb-nts nil)))    ; starters for every non-term
           (enders (the classes (make-array nb-nts nil)))      ; enders for every non-term
           (predictors (the classes (make-array nb-nts nil)))  ; predictors for every non-term
           (steps (the iarr (make-array nb-confs 0)))      ; what to do in a given conf
           (names (the names (make-array nb-confs #f)))) ; name of rules

      ; Now, for each non-terminal, compute the starters, enders and predictors and
      ; the names and steps tables.

      (begin
        (setup-tables grammar nts starters enders predictors steps names)

        ; Build the parser description

        (let ((parser-descr (product (lexer lexer)
                                     (nts nts)
                                     (starters starters)
                                     (enders enders)
                                     (predictors predictors)
                                     (steps steps)
                                     (names names))))
          (lambda ((input symbols))
            (let* ((lexer      (extract parser-descr lexer))
                   (nts        (extract parser-descr nts))
                   (starters   (extract parser-descr starters))
                   (enders     (extract parser-descr enders))
                   (predictors (extract parser-descr predictors))
                   (steps      (extract parser-descr steps))
                   (names      (extract parser-descr names))
                   (toks       (input->tokens input lexer nts)))

              (product (nts nts)
                       (starters starters)
                       (enders enders)
                       (predictors predictors)
                       (steps steps)
                       (names names)
                       (toks toks)
                       (states (backward (forward starters enders predictors steps nts toks)
                                         enders steps nts toks))
                       (parsed? parsed?)
                       (deriv-trees* deriv-trees*)
                       (nb-deriv-trees* nb-deriv-trees*)))))))))

(define* parse->parsed? (subr ear (parse symbol int int) bool)
  (lambda (parse nt i j)
    (let* ((nts     (extract parse nts))
           (enders  (extract parse enders))
           (states  (extract parse states))
           (parsed? (extract parse parsed?)))
      (parsed? nt i j nts enders states))))

(define* parse->trees (subr ear (parse symbol int int) trees)
  (lambda (parse nt i j)
    (let* ((nts          (extract parse nts))
           (enders       (extract parse enders))
           (steps        (extract parse steps))
           (names        (extract parse names))
           (toks         (extract parse toks))
           (states       (extract parse states))
           (deriv-trees* (extract parse deriv-trees*)))
      (deriv-trees* nt i j nts enders steps names toks states))))

(define* parse->nb-trees (subr ear (parse symbol int int) int)
  (lambda (parse nt i j)
    (let* ((nts             (extract parse nts))
           (enders          (extract parse enders))
           (steps           (extract parse steps))
           (toks            (extract parse toks))
           (states          (extract parse states))
           (nb-deriv-trees* (extract parse nb-deriv-trees*)))
      (nb-deriv-trees* nt i j nts enders steps toks states))))

(define* test (subr (maxeff ear (read (globals parse->trees))) (symbols) int)
  (lambda (input)
    (let ((p (make-parser (cons (cons 's (list (cons 'a nil) (list 's 's))) nil) ; '( (s (a) (s s)) )
                          (lambda (l) (map (lambda (x) (list x x)) l)))))
      (let ((x (p input))
            (n (length input)))
        (length (parse->trees x 's 0 n))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 15)
(define iterations int 1)

;; (vector->list (make-vector input1 'a))
(define* make-input (subr (maxeff (alloc @heap) spin) (int) symbols)
  (lambda (n) (if (= n 0) nil (cons 'a (make-input (- n 1))))))

(define* run (subr (maxeff ear (read (globals test parse->trees input1 make-input))) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (test (make-input input1))))))
(run iterations 0)
