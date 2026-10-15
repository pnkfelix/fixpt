;;; A native convention as data a generator reads (`TODO.md` §97,
;;; `docs/research/declared-conventions.md`, step 6): a declaration's
;;; clauses, as `native-convention` gives them (canonical: atoms apart by one
;;; space, integers in decimal), read into a `convention`
;;; (`convention-types.fx`), whose registers, offsets and routines' entries a
;;; generator takes rather than numbers copied out of fixpt. So a generator
;;; is parametric in the convention it is given.
;;;
;;; Reading is total: what a clause does not say reads as 0, or -1 for a
;;; register. Then the convention is printed back, and a declaration it does
;;; not print back to, clause for clause, is refused, naming the first such
;;; clause: one a `convention` cannot hold, or misread, is never handed on.
;;; The rules a declaration states besides its numbers (nothing kept across
;;; a call but the pinned registers, the map stored before every call, …)
;;; are what a `convention` means, and are printed as they are.

;; A file of one expression (`load-input`): the module, of no state and
;; given nothing. Its types (`convention-types.fx`) are loaded around it, so
;; that they are not among its values.
(let ((convention-types (load-module "fx26:convention-types.fx")))
  (module
(hide (include convention-types))

;;; ------------------------------------------------------------ reading

;; The character at `i` of `t`, as a string.
(define cv-ch (subr pure (string int) string) (lambda (t i) (substring t i (+ i 1))))
;; Where the atom from `i` of `t` ends: at a space, a parenthesis or the end.
(define cv-atom-end (subr cvr (string int) int)
  (lambda (t i)
    (if (or (>= i (string-length t)) (string=? (cv-ch t i) " ") (string=? (cv-ch t i) "(")
            (string=? (cv-ch t i) ")"))
        i
        (cv-atom-end t (+ i 1)))))
;; The decimal digits of `s` from `i`, after `acc`; -1 if one is no digit.
(define cv-digits (subr cvr (string int int) int)
  (lambda (s i acc)
    (cond ((= i (string-length s)) acc)
          ((char-numeric? (string-ref s i))
           (cv-digits s (+ i 1) (+ (* acc 10) (- (char->integer (string-ref s i)) 48))))
          (else -1))))
;; An atom: an integer, in decimal, perhaps negative; else a name.
(define cv-atom (subr cvr (string) cv-sx)
  (lambda (a)
    (let* ((neg (and (> (string-length a) 1) (string=? (substring a 0 1) "-")))
           (n (if (= (string-length a) 0) -1 (cv-digits a (if neg 1 0) 0))))
      (cond ((< n 0) (cx-name a))
            (neg (cx-int (- 0 n)))
            (else (cx-int n))))))
(define-rec
  ;; What is at `i` of `t`, and where it ends.
  (cv-read-at (subr cvr (string int) cv-at)
    (lambda (t i)
      (cond ((>= i (string-length t)) (product (x (cx-list nil)) (at i)))
            ((string=? (cv-ch t i) "(")
             (let ((r (cv-read-items t (+ i 1))))
               (product (x (cx-list (extract r xs))) (at (extract r at)))))
            (else (let ((e (cv-atom-end t i)))
                    (product (x (cv-atom (substring t i e))) (at e)))))))
  ;; The items from `i` of `t` to the `)` that ends them, and the place past it.
  (cv-read-items (subr cvr (string int) cv-sxs-at)
    (lambda (t i)
      (cond ((>= i (string-length t)) (product (xs nil) (at i)))
            ((string=? (cv-ch t i) ")") (product (xs nil) (at (+ i 1))))
            ((string=? (cv-ch t i) " ") (cv-read-items t (+ i 1)))
            (else (let* ((r (cv-read-at t i)) (rest (cv-read-items t (extract r at))))
                    (product (xs (the cv-sxs (cons (extract r x) (extract rest xs))))
                             (at (extract rest at)))))))))

;;; ------------------------------------------------------------ looking up

;; A list's items; none of anything else.
(define cx-items (subr pure (cv-sx) cv-sxs)
  (lambda (x) (tagcase x (cx-list (xs) xs) (else y nil))))
;; A name, or "".
(define cx-name-of (subr pure (cv-sx) string)
  (lambda (x) (tagcase x (cx-name (n) n) (else y ""))))
;; An integer, or 0.
(define cx-int-of (subr pure (cv-sx) int)
  (lambda (x) (tagcase x (cx-int (n) n) (else y 0))))
;; A clause's role: the name it begins with.
(define cx-role (subr cvr (cv-sx) string)
  (lambda (x) (let ((xs (cx-items x))) (if (null? xs) "" (cx-name-of (car xs))))))
;; What follows `role` in the first of `xs` that is `(role …)`; none if none is.
(define cx-get (subr cvr (cv-sxs string) cv-sxs)
  (lambda (xs role)
    (cond ((null? xs) nil)
          ((string=? (cx-role (car xs)) role) (cdr (cx-items (car xs))))
          (else (cx-get (cdr xs) role)))))
;; Whether one of `xs` is `(role …)`.
(define cx-has? (subr cvr (cv-sxs string) bool)
  (lambda (xs role)
    (cond ((null? xs) #f) ((string=? (cx-role (car xs)) role) #t) (else (cx-has? (cdr xs) role)))))
;; The `k`th of `xs`, from 0; an empty list past the end.
(define cx-nth (subr cvr (cv-sxs int) cv-sx)
  (lambda (xs k)
    (cond ((null? xs) (cx-list nil)) ((= k 0) (car xs)) (else (cx-nth (cdr xs) (- k 1))))))
;; In `xs`, `(role n …)`'s `n`; `(role a n …)`'s.
(define cx-int-at (subr cvr (cv-sxs string) int)
  (lambda (xs role) (cx-int-of (cx-nth (cx-get xs role) 0))))
(define cx-int2-at (subr cvr (cv-sxs string) int)
  (lambda (xs role) (cx-int-of (cx-nth (cx-get xs role) 1))))
;; A register's number: `xN` N, `sp` 31; -1 for anything else.
(define cx-reg (subr cvr (cv-sx) int)
  (lambda (x)
    (let ((n (cx-name-of x)))
      (cond ((string=? n "sp") 31)
            ((and (> (string-length n) 1) (string=? (substring n 0 1) "x")) (cv-digits n 1 0))
            (else -1)))))
(define cx-reg-at (subr cvr (cv-sxs string) int)
  (lambda (xs role) (cx-reg (cx-nth (cx-get xs role) 0))))
(define cx-regs (subr cvr (cv-sxs) cv-ints)
  (lambda (xs) (if (null? xs) nil (the cv-ints (cons (cx-reg (car xs)) (cx-regs (cdr xs)))))))
;; `((name n) …)`, each name and its number; `((n name) …)`, a trap's kinds.
(define cx-names (subr cvr (cv-sxs) cv-names)
  (lambda (xs)
    (if (null? xs)
        nil
        (let ((i (cx-items (car xs))))
          (the cv-names
               (cons (product (name (cx-name-of (cx-nth i 0))) (number (cx-int-of (cx-nth i 1))))
                              (cx-names (cdr xs))))))))
(define cx-numbered (subr cvr (cv-sxs) cv-names)
  (lambda (xs)
    (if (null? xs)
        nil
        (let ((i (cx-items (car xs))))
          (the cv-names
               (cons (product (name (cx-name-of (cx-nth i 1))) (number (cx-int-of (cx-nth i 0))))
                              (cx-numbered (cdr xs))))))))
;; `((name at width) …)`: a header's fields.
(define cx-bits (subr cvr (cv-sxs) cv-bits)
  (lambda (xs)
    (if (null? xs)
        nil
        (let ((i (cx-items (car xs))))
          (the cv-bits (cons (product (name (cx-name-of (cx-nth i 0))) (at (cx-int-of (cx-nth i 1)))
                                      (width (cx-int-of (cx-nth i 2))))
                             (cx-bits (cdr xs))))))))
;; `((role register …) …)`: a routine's inputs.
(define cx-in (subr cvr (cv-sxs) cv-regs)
  (lambda (xs)
    (if (null? xs)
        nil
        (let ((i (cx-items (car xs))))
          (the cv-regs (cons (product (name (cx-name-of (car i))) (registers (cx-regs (cdr i))))
                             (cx-in (cdr xs))))))))
;; The offset of the state's field that `(role state field …)` in `xs` names.
(define cx-state-at (subr cvr (cv-sxs string cv-sxs) int)
  (lambda (xs role st) (cx-int-at st (cx-name-of (cx-nth (cx-get xs role) 1)))))

;;; ------------------------------------------------------------ the clauses

(define cv-registers-of (subr cvr (cv-sxs) cv-registers)
  (lambda (rg)
    (let ((pin (cx-get rg "pinned")))
      (product (arguments (cx-regs (cx-get rg "arguments"))) (rest-in (cx-reg-at rg "rest-in"))
               (count (cx-reg-at rg "count")) (result (cx-reg-at rg "result"))
               (closure (cx-reg-at rg "closure")) (link (cx-reg-at rg "link"))
               (frame (cx-reg-at rg "frame")) (state (cx-reg-at pin "state"))
               (fuel (cx-reg-at pin "fuel")) (stack-limit (cx-reg-at pin "stack-limit"))
               (code-distance (cx-reg-at pin "code-distance"))))))
(define cv-values-of (subr cvr (cv-sxs) cv-values)
  (lambda (vs)
    (let ((fx (cx-get vs "fixnum")) (ch (cx-get vs "character")) (pr (cx-get vs "pair"))
          (bl (cx-get vs "bloblet")))
      (product (tags (cx-names (cx-get vs "tags"))) (fixnum-shift (cx-int-at fx "shift"))
               (fixnum-bits (cx-int-at fx "bits")) (immediates (cx-names (cx-get vs "immediates")))
               (char-subtag (cx-int-at ch "subtag"))
               (char-payload-shift (cx-int-at ch "payload-shift"))
               (car (cx-int-at pr "car")) (cdr (cx-int-at pr "cdr"))
               (bloblet-past-suffix (cx-int2-at bl "reference"))
               (field-k-before-suffix (cx-int-at bl "field-k-before-suffix"))
               (header (cx-bits (cx-get vs "header"))) (kinds (cx-names (cx-get vs "kinds")))))))
(define cv-closures-of (subr cvr (cv-sxs cv-sxs) cv-closures)
  (lambda (cl st)
    (product (kind (cx-int-at cl "kind")) (code-field (cx-int-at cl "code-field"))
             (first-free-field (cx-int-at cl "first-free-field"))
             (native-when-code-at-least
              (cx-int-at st (cx-name-of (cx-nth (cx-get cl "native-when-code-at-least") 0)))))))
(define cv-frames-of (subr cvr (cv-sxs) cv-frames)
  (lambda (fr)
    (let ((m (cx-get fr "map")))
      (product (align (cx-int-at fr "align")) (header (cx-int2-at fr "header"))
               (link (cx-int2-at fr "link")) (return (cx-int2-at fr "return"))
               (map (cx-int-of (cx-nth m 1))) (values-from (cx-int2-at fr "values-from"))
               (live-below (cx-int-at m "live-slots-below"))
               (fields-above (cx-int-at m "fields-above"))
               (stub (cx-int-at fr "stub"))))))
(define cv-state-of (subr cvr (cv-sxs) cv-state)
  (lambda (st)
    (let ((at (lambda ((n string)) (cx-int-at st n))))
      (product (fuel (at "fuel")) (reserve (at "reserve")) (trap (at "trap")) (pc (at "pc"))
               (args (at "args")) (nargs (at "nargs")) (aux (at "aux")) (callout (at "callout"))
               (rust-sp (at "rust-sp")) (native-sp (at "native-sp")) (fp (at "fp")) (top (at "top"))
               (words (at "words")) (alloc-limit (at "alloc-limit")) (code (at "code"))
               (clo (at "clo"))
               (delta (at "delta")) (code-lo (at "code-lo")) (trap-stub (at "trap-stub"))
               (foreign (at "foreign")) (closure (at "closure")) (cards (at "cards"))
               (stack-limit (at "stack-limit")) (overflow (at "overflow")) (poll (at "poll"))
               (cons (at "cons")) (bloblet (at "bloblet"))))))
(define cv-routine-of (subr cvr (cv-sxs cv-sxs) cv-routine)
  (lambda (r st)
    (product (entry (cx-state-at r "entry" st)) (in (cx-in (cx-get r "in")))
             (out (if (cx-has? r "out") (cx-reg-at r "out") -1))
             (may-collect (cx-has? r "may-collect")))))
(define cv-overflow-of (subr cvr (cv-sxs cv-sxs) cv-overflow)
  (lambda (o st)
    (let* ((in (cx-get o "in")) (info (cx-get in "info")) (held (cx-get info "arguments-held")))
      (product (entry (cx-state-at o "entry" st)) (code (cx-reg-at in "code"))
               (info (cx-reg (cx-nth info 0))) (held-at (cx-int-of (cx-nth held 0)))
               (held-width (cx-int-of (cx-nth held 1)))
               (closure-read (cx-int-at info "closure-read"))
               (variadic (cx-int-at info "variadic")) (keeps (cx-regs (cx-get o "keeps")))))))
(define cv-routines-of (subr cvr (cv-sxs cv-sxs) cv-routines)
  (lambda (rt st)
    (let ((t (cx-get rt "trap")))
      (product (foreign (cv-routine-of (cx-get rt "foreign") st))
               (overflow (cv-overflow-of (cx-get rt "overflow") st))
               (poll (cv-routine-of (cx-get rt "poll") st))
               (cons (cv-routine-of (cx-get rt "cons") st))
               (bloblet (cv-routine-of (cx-get rt "bloblet") st))
               (trap (product (entry (cx-state-at t "entry" st))
                              (kind (cx-reg-at (cx-get t "in") "kind"))
                              (kinds (cx-numbered (cx-get t "kinds")))))))))
;; A declaration's clauses, read.
(define cv-of (subr cvr (cv-sxs) convention)
  (lambda (cs)
    (let ((st (cx-get cs "state")) (fu (cx-get cs "fuel")) (ba (cx-get cs "barrier")))
      (product (target (cx-name-of (cx-nth (cx-get cs "target") 0)))
               (registers (cv-registers-of (cx-get cs "registers")))
               (values (cv-values-of (cx-get cs "values")))
               (closures (cv-closures-of (cx-get cs "closures") st))
               (code (product (field-k-before-code (cx-int-at (cx-get cs "code")
                                                              "field-k-before-code"))))
               (frames (cv-frames-of (cx-get cs "frames"))) (state (cv-state-of st))
               (routines (cv-routines-of (cx-get cs "routines") st))
               (fuel (product (register (cx-reg-at fu "register"))
                              (subtract (cx-int-at fu "subtract"))))
               (barrier (product (cards (cx-state-at ba "cards" st))
                                 (card-shift (cx-int-at ba "card-shift"))
                                 (mark (cx-int-at ba "mark"))))))))

;;; ------------------------------------------------------------ printing

;; `xs` apart by one space.
(define cv-cat (subr cvr (cv-strs) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (car xs))
          (else (string-append (car xs) " " (cv-cat (cdr xs)))))))
;; `(role part …)`; `(role n)`.
(define cv-par (subr cvr (string cv-strs) string)
  (lambda (role parts) (string-append "(" (cv-cat (the cv-strs (cons role parts))) ")")))
(define cv-kv (subr cvr (string int) string)
  (lambda (role n) (cv-par role (list (int->string n)))))
(define cv-reg (subr pure (int) string)
  (lambda (r) (if (= r 31) "sp" (string-append "x" (int->string r)))))
(define cv-pr-regs (subr cvr (cv-ints) cv-strs)
  (lambda (rs) (if (null? rs) nil (the cv-strs (cons (cv-reg (car rs)) (cv-pr-regs (cdr rs)))))))
(define cv-pr-names (subr cvr (cv-names) cv-strs)
  (lambda (ns)
    (if (null? ns)
        nil
        (the cv-strs
             (cons (cv-kv (extract (car ns) name) (extract (car ns) number))
                   (cv-pr-names (cdr ns)))))))
(define cv-pr-numbered (subr cvr (cv-names) cv-strs)
  (lambda (ns)
    (if (null? ns)
        nil
        (the cv-strs
             (cons (cv-par (int->string (extract (car ns) number)) (list (extract (car ns) name)))
                           (cv-pr-numbered (cdr ns)))))))
;; The state's fields, each its name and offset, in the declaration's order.
(define cv-state-names (subr cvr (cv-state) cv-names)
  (lambda (s)
    (let ((f (lambda ((n string) (k int)) (product (name n) (number k)))))
      (list (f "fuel" (extract s fuel)) (f "reserve" (extract s reserve))
            (f "trap" (extract s trap))
            (f "pc" (extract s pc)) (f "args" (extract s args)) (f "nargs" (extract s nargs))
            (f "aux" (extract s aux)) (f "callout" (extract s callout))
            (f "rust-sp" (extract s rust-sp))
            (f "native-sp" (extract s native-sp)) (f "fp" (extract s fp)) (f "top" (extract s top))
            (f "words" (extract s words)) (f "alloc-limit" (extract s alloc-limit))
            (f "code" (extract s code)) (f "clo" (extract s clo)) (f "delta" (extract s delta))
            (f "code-lo" (extract s code-lo)) (f "trap-stub" (extract s trap-stub))
            (f "foreign" (extract s foreign)) (f "closure" (extract s closure))
            (f "cards" (extract s cards)) (f "stack-limit" (extract s stack-limit))
            (f "overflow" (extract s overflow)) (f "poll" (extract s poll))
            (f "cons" (extract s cons)) (f "bloblet" (extract s bloblet))))))
;; The name of the field at `k` in `ns`; "" if none is.
(define cv-name-at (subr cvr (cv-names int) string)
  (lambda (ns k)
    (cond ((null? ns) "")
          ((= (extract (car ns) number) k) (extract (car ns) name))
          (else (cv-name-at (cdr ns) k)))))

(define cv-pr-registers (subr cvr (cv-registers) string)
  (lambda (r)
    (let ((one (lambda ((role string) (n int)) (cv-par role (list (cv-reg n))))))
      (cv-par "registers"
              (list (cv-par "arguments" (cv-pr-regs (extract r arguments)))
                    (one "rest-in" (extract r rest-in))
                    (one "count" (extract r count)) (one "result" (extract r result))
                    (one "closure" (extract r closure)) (one "link" (extract r link))
                    (one "frame" (extract r frame))
                    (cv-par "pinned"
                            (list (one "state" (extract r state)) (one "fuel" (extract r fuel))
                                           (one "stack-limit" (extract r stack-limit))
                                           (one "code-distance" (extract r code-distance))))
                    "(lost-across-calls all-but-pinned)")))))
(define cv-pr-bits (subr cvr (cv-bits) cv-strs)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((b (car bs)))
          (the cv-strs (cons (cv-par (extract b name) (list (int->string (extract b at))
                                                            (int->string (extract b width))))
                             (cv-pr-bits (cdr bs))))))))
(define cv-pr-values (subr cvr (cv-values) string)
  (lambda (v)
    (cv-par "values"
            (list (cv-par "tags" (cv-pr-names (extract v tags)))
                  (cv-par "fixnum" (list (cv-kv "shift" (extract v fixnum-shift))
                                         (cv-kv "bits" (extract v fixnum-bits))))
                  (cv-par "immediates" (cv-pr-names (extract v immediates)))
                  (cv-par "character" (list (cv-kv "subtag" (extract v char-subtag))
                                            (cv-kv "payload-shift" (extract v char-payload-shift))))
                  (cv-par "pair" (list (cv-kv "car" (extract v car)) (cv-kv "cdr" (extract v cdr))))
                  (cv-par "bloblet"
                          (list (cv-par "reference"
                                        (list "suffix"
                                              (int->string (extract v bloblet-past-suffix))))
                                (cv-kv "field-k-before-suffix" (extract v field-k-before-suffix))))
                  (cv-par "header" (cv-pr-bits (extract v header)))
                  (cv-par "kinds" (cv-pr-names (extract v kinds)))))))
(define cv-pr-frames (subr cvr (cv-frames int int) string)
  (lambda (f fp lr)
    (let ((at (lambda ((role string) (k int)) (cv-par role (list (cv-reg fp) (int->string k))))))
      (cv-par "frames"
              (list (cv-kv "align" (extract f align)) (at "header" (extract f header))
                    (at "link" (extract f link)) (at "return" (extract f return))
                    (cv-par "map" (list (cv-reg fp) (int->string (extract f map))
                                        (cv-kv "live-slots-below" (extract f live-below))
                                        (cv-par "fields-above"
                                                (list (int->string (extract f fields-above))
                                                      "link" "return" "map" "values"))
                                        "(all-live negative)"))
                    (at "values-from" (extract f values-from)) "(raw-after-values)"
                    "(keeps-its-code)" "(map-stored-before calls routines-that-collect)"
                    (cv-par "made" (list "sub" "sp" "stp" (cv-reg fp) (cv-reg lr) "add" (cv-reg fp)
                                         "sp" (int->string (- 0 (extract f header)))))
                    (cv-kv "stub" (extract f stub)))))))
;; `(entry state field)`, the field's name from its offset.
(define cv-pr-entry (subr cvr (cv-names int) string)
  (lambda (sn k) (cv-par "entry" (list "state" (cv-name-at sn k)))))
(define cv-pr-in (subr cvr (cv-regs) cv-strs)
  (lambda (rs)
    (if (null? rs)
        nil
        (the cv-strs
             (cons (cv-par (extract (car rs) name) (cv-pr-regs (extract (car rs) registers)))
                           (cv-pr-in (cdr rs)))))))
;; A routine, `more` after what every routine says.
(define cv-pr-routine (subr cvr (string cv-routine cv-names cv-strs) string)
  (lambda (name r sn more)
    (let* ((tail (if (extract r may-collect) (the cv-strs (cons "(may-collect)" more)) more))
           (tail (if (< (extract r out) 0)
                     tail
                     (the cv-strs (cons (cv-par "out" (list (cv-reg (extract r out)))) tail)))))
      (cv-par name (the cv-strs (cons (cv-pr-entry sn (extract r entry))
                                      (cons (cv-par "in" (cv-pr-in (extract r in))) tail)))))))
(define cv-pr-overflow (subr cvr (cv-overflow cv-names int int) string)
  (lambda (o sn limit lr)
    (cv-par "overflow"
            (list (cv-par "when" (list "sp" "below" (cv-reg limit) "after-frame-made"))
                  (cv-par "entry" (list "state" (cv-name-at sn (extract o entry)) "by" (cv-reg lr)))
                  (cv-par "in"
                          (list (cv-par "code" (list (cv-reg (extract o code))))
                                (cv-par "info"
                                        (list (cv-reg (extract o info))
                                              (cv-par "arguments-held"
                                                      (list (int->string (extract o held-at))
                                                            (int->string (extract o held-width))))
                                              (cv-kv "closure-read" (extract o closure-read))
                                              (cv-kv "variadic" (extract o variadic))))))
                  (cv-par "keeps" (cv-pr-regs (extract o keeps)))))))
(define cv-pr-routines (subr cvr (convention) string)
  (lambda (c)
    (let ((rs (extract c routines)) (sn (cv-state-names (extract c state)))
          (rg (extract c registers)))
      (cv-par "routines"
              (list (cv-pr-routine "foreign" (extract rs foreign) sn nil)
                    (cv-pr-overflow (extract rs overflow) sn (extract rg stack-limit)
                                    (extract rg link))
                    (cv-pr-routine "poll" (extract rs poll) sn (list "(traps-when-spent 1)"))
                    (cv-pr-routine "cons" (extract rs cons) sn nil)
                    (cv-pr-routine "bloblet" (extract rs bloblet) sn
                                   (list "(makes (kind bloblet) (trailer 1) zeroed)"
                                         "(traps-when-refused 3)"))
                    (let ((t (extract rs trap)))
                      (cv-par "trap"
                              (list (cv-pr-entry sn (extract t entry))
                                    (cv-par "in"
                                            (list (cv-par "kind" (list (cv-reg (extract t kind))))))
                                    (cv-par "kinds" (cv-pr-numbered (extract t kinds)))))))))))
;; A convention's clauses, as a declaration says them, in fixpt's order.
(define cv-print (subr cvr (convention) cv-strs)
  (lambda (c)
    (let ((rg (extract c registers)) (cl (extract c closures))
          (sn (cv-state-names (extract c state))) (fu (extract c fuel)) (ba (extract c barrier)))
      (list (cv-par "target" (list (extract c target)))
            (cv-pr-registers rg)
            (cv-pr-values (extract c values))
            (cv-par "closures"
                    (list (cv-kv "kind" (extract cl kind))
                          (cv-kv "code-field" (extract cl code-field))
                          (cv-kv "first-free-field" (extract cl first-free-field))
                          (cv-par "native-when-code-at-least"
                                  (list (cv-name-at sn (extract cl native-when-code-at-least))))))
            (cv-par "code"
                    (list (cv-par "runs-at"
                                  (list "reference" "plus" (cv-reg (extract rg code-distance))))
                          (cv-kv "field-k-before-code"
                                 (extract (extract c code) field-k-before-code))))
            (cv-pr-frames (extract c frames) (extract rg frame) (extract rg link))
            (cv-par "state" (cv-pr-names sn))
            (cv-pr-routines c)
            (cv-par "fuel" (list (cv-par "register" (list (cv-reg (extract fu register))))
                                 (cv-kv "subtract" (extract fu subtract)) "(on entry back-edge)"
                                 "(borrow poll)"))
            (cv-par "barrier"
                    (list (cv-par "cards" (list "state" (cv-name-at sn (extract ba cards))))
                          (cv-kv "card-shift" (extract ba card-shift))
                          (cv-kv "mark" (extract ba mark))))))))

;;; ------------------------------------------------------------ reading back

;; A clause's role, from its text: up to its first space or `)`.
(define cv-role-of (subr cvr (string) string)
  (lambda (t) (substring t 1 (cv-atom-end t 1))))
;; The clause of `ts` whose role is `role`; "" if none is.
(define cv-clause (subr cvr (cv-strs string) string)
  (lambda (ts role)
    (cond ((null? ts) "")
          ((string=? (cv-role-of (car ts)) role) (car ts))
          (else (cv-clause (cdr ts) role)))))
;; Why `ts`, declared, is not `back`, printed: "" if it is.
(define cv-differs (subr cvr (cv-strs cv-strs) string)
  (lambda (ts back)
    (if (null? back)
        ""
        (let* ((b (car back)) (role (cv-role-of b)) (t (cv-clause ts role)))
          (cond ((string=? t "") (string-append "no `" role "` clause"))
                ((string=? t b) (cv-differs ts (cdr back)))
                (else (string-append "the `" role "` clause is not one a convention holds: "
                                     t)))))))
;; A clause of `ts` none of `back` has the role of: "" if none.
(define cv-extra (subr cvr (cv-strs cv-strs) string)
  (lambda (ts back)
    (cond ((null? ts) "")
          ((string=? (cv-clause back (cv-role-of (car ts))) "")
           (string-append "a `" (cv-role-of (car ts))
                          "` clause, which a convention has no room for"))
          (else (cv-extra (cdr ts) back)))))
(define cv-parse-all (subr cvr (cv-strs) cv-sxs)
  (lambda (ts)
    (if (null? ts)
        nil
        (the cv-sxs (cons (extract (cv-read-at (car ts) 0) x) (cv-parse-all (cdr ts)))))))
;; A declaration's clauses, read: the convention, or why not.
(define cv-read-clauses (subr cvr (cv-strs) cv-read)
  (lambda (ts)
    (let* ((c (cv-of (cv-parse-all ts))) (back (cv-print c))
           (why (let ((d (cv-differs ts back))) (if (string=? d "") (cv-extra ts back) d))))
      (if (string=? why "") (sum ok c) (sum refused why)))))
;; fixpt's own native convention, read.
(define cv-native (subr cvr () cv-read)
  (lambda () (cv-read-clauses (the cv-strs (native-convention)))))))
