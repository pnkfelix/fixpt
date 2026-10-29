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

;; The character at `i` of `t`: a character, not a string of it, which each
;; test would allocate (`TODO.md` §172).
(define cv-ch (->* (string int) char) (lambda (t i) (string-ref t i)))
;; Where the atom from `i` of `t` ends: at a space, a parenthesis or the end.
(define cv-atom-end (->* (string int) int)
  (lambda (t i)
    (if (or (>= i (string-length t)) (char=? (cv-ch t i) #\space) (char=? (cv-ch t i) #\()
            (char=? (cv-ch t i) #\)))
        i
        (cv-atom-end t (+ i 1)))))
;; The decimal digits of `s` from `i`, after `acc`; -1 if one is no digit.
(define cv-digits (->* (string int int) int)
  (lambda (s i acc)
    (cond ((= i (string-length s)) acc)
          ((char-numeric? (string-ref s i))
           (cv-digits s (+ i 1) (+ (* acc 10) (- (char->integer (string-ref s i)) 48))))
          (else -1))))
;; An atom: an integer, in decimal, perhaps negative; else a name.
(define cv-atom (->* (string) cv-sx)
  (lambda (a)
    (let* ((neg (and (> (string-length a) 1) (char=? (string-ref a 0) #\-)))
           (n (if (= (string-length a) 0) -1 (cv-digits a (if neg 1 0) 0))))
      (cond ((< n 0) (cx-name a))
            (neg (cx-int (- 0 n)))
            (else (cx-int n))))))
(define-rec
  ;; What is at `i` of `t`, and where it ends.
  (cv-read-at (->* (string int) cv-at)
    (lambda (t i)
      (cond ((>= i (string-length t)) (product (x (cx-list nil)) (at i)))
            ((char=? (cv-ch t i) #\()
             (let ((r (cv-read-items t (+ i 1))))
               (product (x (cx-list (extract r xs))) (at (extract r at)))))
            (else (let ((e (cv-atom-end t i)))
                    (product (x (cv-atom (substring t i e))) (at e)))))))
  ;; The items from `i` of `t` to the `)` that ends them, and the place past it.
  (cv-read-items (->* (string int) cv-sxs-at)
    (lambda (t i)
      (cond ((>= i (string-length t)) (product (xs nil) (at i)))
            ((char=? (cv-ch t i) #\)) (product (xs nil) (at (+ i 1))))
            ((char=? (cv-ch t i) #\space) (cv-read-items t (+ i 1)))
            (else (let* ((r (cv-read-at t i)) (rest (cv-read-items t (extract r at))))
                    (product (xs (the cv-sxs (cons (extract r x) (extract rest xs))))
                             (at (extract rest at)))))))))

;;; ------------------------------------------------------------ looking up

;; A list's items; none of anything else.
(define cx-items (->* (cv-sx) cv-sxs)
  (lambda (x) (tagcase x (cx-list (xs) xs) (else y nil))))
;; A name, or "".
(define cx-name-of (->* (cv-sx) string)
  (lambda (x) (tagcase x (cx-name (n) n) (else y ""))))
;; An integer, or 0.
(define cx-int-of (->* (cv-sx) int)
  (lambda (x) (tagcase x (cx-int (n) n) (else y 0))))
;; A clause's role: the name it begins with.
(define cx-role (->* (cv-sx) string)
  (lambda (x) (let ((xs (cx-items x))) (if (null? xs) "" (cx-name-of (car xs))))))
;; What follows `role` in the first of `xs` that is `(role …)`; none if none is.
(define cx-get (->* (cv-sxs string) cv-sxs)
  (lambda (xs role)
    (cond ((null? xs) nil)
          ((string=? (cx-role (car xs)) role) (cdr (cx-items (car xs))))
          (else (cx-get (cdr xs) role)))))
;; Whether one of `xs` is `(role …)`.
(define cx-has? (->* (cv-sxs string) bool)
  (lambda (xs role)
    (cond ((null? xs) #f) ((string=? (cx-role (car xs)) role) #t) (else (cx-has? (cdr xs) role)))))
;; The `k`th of `xs`, from 0; an empty list past the end.
(define cx-nth (->* (cv-sxs int) cv-sx)
  (lambda (xs k)
    (cond ((null? xs) (cx-list nil)) ((= k 0) (car xs)) (else (cx-nth (cdr xs) (- k 1))))))
;; In `xs`, `(role n …)`'s `n`; `(role a n …)`'s.
(define cx-int-at (->* (cv-sxs string) int)
  (lambda (xs role) (cx-int-of (cx-nth (cx-get xs role) 0))))
(define cx-int2-at (->* (cv-sxs string) int)
  (lambda (xs role) (cx-int-of (cx-nth (cx-get xs role) 1))))
;; Where a place in the state starts (`convention-types.fx`).
(define cv-in-state int 4096)
;; x86_64's registers, as the hardware numbers them.
(define cv-x86-regs (->* () cv-strs)
  (lambda ()
    (list "rax" "rcx" "rdx" "rbx" "rsp" "rbp" "rsi" "rdi" "r8" "r9" "r10" "r11" "r12" "r13"
          "r14" "r15")))
;; Where `n` is in `ns`, from `k`; -1 if it is not.
(define cv-index (->* (cv-strs string int) int)
  (lambda (ns n k)
    (cond ((null? ns) -1) ((string=? (car ns) n) k) (else (cv-index (cdr ns) n (+ k 1))))))
;; A place (`convention-types.fx`): `xN` N, `sp` 31, x86_64's by number,
;; `(state field)` past `cv-in-state` by the field's offset in `st`,
;; `pushed` -2; -1 for anything else.
(define cx-reg (->* (cv-sxs cv-sx) int)
  (lambda (st x)
    (let ((n (cx-name-of x)))
      (cond ((string=? (cx-role x) "state")
             (+ cv-in-state (cx-int-at st (cx-name-of (cx-nth (cx-items x) 1)))))
            ((string=? n "sp") 31)
            ((string=? n "pushed") -2)
            ((and (> (string-length n) 1) (char=? (string-ref n 0) #\x)) (cv-digits n 1 0))
            (else (cv-index (cv-x86-regs) n 0))))))
(define cx-reg-at (->* (cv-sxs cv-sxs string) int)
  (lambda (st xs role) (cx-reg st (cx-nth (cx-get xs role) 0))))
(define cx-regs (->* (cv-sxs cv-sxs) cv-ints)
  (lambda (st xs)
    (if (null? xs) nil (the cv-ints (cons (cx-reg st (car xs)) (cx-regs st (cdr xs)))))))
;; `((name n) …)`, each name and its number; `((n name) …)`, a trap's kinds.
(define cx-names (->* (cv-sxs) cv-names)
  (lambda (xs)
    (if (null? xs)
        nil
        (let ((i (cx-items (car xs))))
          (the cv-names
               (cons (product (name (cx-name-of (cx-nth i 0))) (number (cx-int-of (cx-nth i 1))))
                              (cx-names (cdr xs))))))))
(define cx-numbered (->* (cv-sxs) cv-names)
  (lambda (xs)
    (if (null? xs)
        nil
        (let ((i (cx-items (car xs))))
          (the cv-names
               (cons (product (name (cx-name-of (cx-nth i 1))) (number (cx-int-of (cx-nth i 0))))
                              (cx-numbered (cdr xs))))))))
;; `((name at width) …)`: a header's fields.
(define cx-bits (->* (cv-sxs) cv-bits)
  (lambda (xs)
    (if (null? xs)
        nil
        (let ((i (cx-items (car xs))))
          (the cv-bits (cons (product (name (cx-name-of (cx-nth i 0))) (at (cx-int-of (cx-nth i 1)))
                                      (width (cx-int-of (cx-nth i 2))))
                             (cx-bits (cdr xs))))))))
;; `((role place …) …)`: a routine's inputs.
(define cx-in (->* (cv-sxs cv-sxs) cv-regs)
  (lambda (st xs)
    (if (null? xs)
        nil
        (let ((i (cx-items (car xs))))
          (the cv-regs (cons (product (name (cx-name-of (car i))) (registers (cx-regs st (cdr i))))
                             (cx-in st (cdr xs))))))))
;; The first of `xs` that is `(role …)`; an empty list if none is.
(define cx-find (->* (cv-sxs string) cv-sx)
  (lambda (xs role)
    (cond ((null? xs) (cx-list nil))
          ((string=? (cx-role (car xs)) role) (car xs))
          (else (cx-find (cdr xs) role)))))
;; The offset of the state's field that `(role state field …)` in `xs` names.
(define cx-state-at (->* (cv-sxs string cv-sxs) int)
  (lambda (xs role st) (cx-int-at st (cx-name-of (cx-nth (cx-get xs role) 1)))))

;;; ------------------------------------------------------------ the clauses

(define cv-registers-of (->* (cv-sxs cv-sxs) cv-registers)
  (lambda (rg st)
    (let ((pin (cx-get rg "pinned"))
          (at (lambda ((xs cv-sxs) (role string)) (cx-reg-at st xs role))))
      (product (arguments (cx-regs st (cx-get rg "arguments"))) (rest-in (at rg "rest-in"))
               (count (at rg "count")) (result (at rg "result"))
               (closure (at rg "closure")) (link (at rg "link"))
               (frame (at rg "frame")) (state (at pin "state"))
               (fuel (at pin "fuel")) (stack-limit (at pin "stack-limit"))
               (code-distance (at pin "code-distance"))))))
(define cv-values-of (->* (cv-sxs) cv-values)
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
(define cv-closures-of (->* (cv-sxs cv-sxs) cv-closures)
  (lambda (cl st)
    (product (kind (cx-int-at cl "kind")) (code-field (cx-int-at cl "code-field"))
             (first-free-field (cx-int-at cl "first-free-field"))
             (native-when-code-at-least
              (if (cx-has? cl "code-always-runs")
                  (cx-int-at st "code-lo")
                  (cx-int-at st
                             (cx-name-of (cx-nth (cx-get cl "native-when-code-at-least") 0)))))
             (code-always-runs (cx-has? cl "code-always-runs")))))
(define cv-frames-of (->* (cv-sxs) cv-frames)
  (lambda (fr)
    (let ((m (cx-get fr "map")))
      (product (align (cx-int-at fr "align")) (header (cx-int2-at fr "header"))
               (link (cx-int2-at fr "link")) (return (cx-int2-at fr "return"))
               (map (cx-int-of (cx-nth m 1))) (values-from (cx-int2-at fr "values-from"))
               (live-below (cx-int-at m "live-slots-below"))
               (fields-above (cx-int-at m "fields-above"))
               (stub (cx-int-at fr "stub"))))))
(define cv-state-of (->* (cv-sxs) cv-state)
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
               (cons (at "cons")) (bloblet (at "bloblet")) (reg4 (at "reg4"))))))
(define cv-routine-of (->* (cv-sxs cv-sxs) cv-routine)
  (lambda (r st)
    (product (entry (cx-state-at r "entry" st)) (in (cx-in st (cx-get r "in")))
             (out (if (cx-has? r "out") (cx-reg-at st r "out") -1))
             (may-collect (cx-has? r "may-collect")))))
(define cv-overflow-of (->* (cv-sxs cv-sxs) cv-overflow)
  (lambda (o st)
    (let* ((in (cx-get o "in")) (info (cx-get in "info")) (held (cx-get info "arguments-held")))
      (product (entry (cx-state-at o "entry" st)) (code (cx-reg-at st in "code"))
               (info (cx-reg st (cx-nth info 0))) (held-at (cx-int-of (cx-nth held 0)))
               (held-width (cx-int-of (cx-nth held 1)))
               (closure-read (cx-int-at info "closure-read"))
               (variadic (cx-int-at info "variadic")) (keeps (cx-regs st (cx-get o "keeps")))))))
(define cv-routines-of (->* (cv-sxs cv-sxs) cv-routines)
  (lambda (rt st)
    (let ((t (cx-get rt "trap")))
      (product (foreign (cv-routine-of (cx-get rt "foreign") st))
               (overflow (cv-overflow-of (cx-get rt "overflow") st))
               (poll (cv-routine-of (cx-get rt "poll") st))
               (cons (cv-routine-of (cx-get rt "cons") st))
               (bloblet (cv-routine-of (cx-get rt "bloblet") st))
               (trap (product (entry (cx-state-at t "entry" st))
                              (kind (cx-reg-at st (cx-get t "in") "kind"))
                              (kinds (cx-numbered (cx-get t "kinds")))))))))
;; A declaration's clauses, read.
(define cv-of (->* (cv-sxs) convention)
  (lambda (cs)
    (let ((st (cx-get cs "state")) (fu (cx-get cs "fuel")) (ba (cx-get cs "barrier")))
      (product (target (cx-name-of (cx-nth (cx-get cs "target") 0)))
               (registers (cv-registers-of (cx-get cs "registers") st))
               (values (cv-values-of (cx-get cs "values")))
               (closures (cv-closures-of (cx-get cs "closures") st))
               (code (product (field-k-before-code (cx-int-at (cx-get cs "code")
                                                              "field-k-before-code"))))
               (frames (cv-frames-of (cx-get cs "frames"))) (state (cv-state-of st))
               (routines (cv-routines-of (cx-get cs "routines") st))
               ;; In a register, or, x86_64's, in the state.
               (fuel (product (register (if (cx-has? fu "register")
                                            (cx-reg-at st fu "register")
                                            (cx-reg st (cx-find fu "state"))))
                              (subtract (cx-int-at fu "subtract"))))
               (barrier (product (cards (cx-state-at ba "cards" st))
                                 (card-shift (cx-int-at ba "card-shift"))
                                 (mark (cx-int-at ba "mark"))))))))

;;; ------------------------------------------------------------ printing

;; `xs` apart by one space.
(define cv-cat (->* (cv-strs) string)
  (lambda (xs)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (car xs))
          (else (string-append (car xs) " " (cv-cat (cdr xs)))))))
;; `(role part …)`; `(role n)`.
(define cv-par (->* (string cv-strs) string)
  (lambda (role parts) (string-append "(" (cv-cat (the cv-strs (cons role parts))) ")")))
(define cv-kv (->* (string int) string)
  (lambda (role n) (cv-par role (list (int->string n)))))
;; The `k`th of `ns`, from 0; "" past the end.
(define cv-str-at (->* (cv-strs int) string)
  (lambda (ns k) (cond ((null? ns) "") ((= k 0) (car ns)) (else (cv-str-at (cdr ns) (- k 1))))))
;; The name of the field at `k` in `ns`; "" if none is.
(define cv-name-at (->* (cv-names int) string)
  (lambda (ns k)
    (cond ((null? ns) "")
          ((= (extract (car ns) number) k) (extract (car ns) name))
          (else (cv-name-at (cdr ns) k)))))
;; A place, as `nm` names it.
(define cv-reg (->* (cv-nm int) string)
  (lambda (nm r)
    (cond ((>= r cv-in-state)
           (cv-par "state" (list (cv-name-at (extract nm sn) (- r cv-in-state)))))
          ((= r -2) "pushed")
          ((extract nm x86) (cv-str-at (cv-x86-regs) r))
          ((= r 31) "sp")
          (else (string-append "x" (int->string r))))))
;; The stack's register.
(define cv-sp (->* (cv-nm) string) (lambda (nm) (cv-reg nm (if (extract nm x86) 4 31))))
(define cv-pr-regs (->* (cv-nm cv-ints) cv-strs)
  (lambda (nm rs)
    (if (null? rs) nil (the cv-strs (cons (cv-reg nm (car rs)) (cv-pr-regs nm (cdr rs)))))))
(define cv-pr-names (->* (cv-names) cv-strs)
  (lambda (ns)
    (if (null? ns)
        nil
        (the cv-strs
             (cons (cv-kv (extract (car ns) name) (extract (car ns) number))
                   (cv-pr-names (cdr ns)))))))
(define cv-pr-numbered (->* (cv-names) cv-strs)
  (lambda (ns)
    (if (null? ns)
        nil
        (the cv-strs
             (cons (cv-par (int->string (extract (car ns) number)) (list (extract (car ns) name)))
                           (cv-pr-numbered (cdr ns)))))))
;; x86_64's REG4 … REG`k`, REG4 at `at`, before `acc`; none if `at` is 0.
(define cv-reg-names (->* (int int cv-names) cv-names)
  (lambda (at k acc)
    (if (or (= at 0) (< k 4))
        acc
        (cv-reg-names at (- k 1)
                      (the cv-names
                           (cons (product (name (string-append "reg" (int->string k)))
                                          (number (+ at (* 8 (- k 4)))))
                                 acc))))))
;; The state's fields, each its name and offset, in the declaration's order.
(define cv-state-names (->* (cv-state) cv-names)
  (lambda (s)
    (let ((f (lambda ((n string) (k int)) (product (name n) (number k)))))
      (append
       (list (f "fuel" (extract s fuel)) (f "reserve" (extract s reserve))
             (f "trap" (extract s trap))
             (f "pc" (extract s pc)) (f "args" (extract s args)) (f "nargs" (extract s nargs))
             (f "aux" (extract s aux)) (f "callout" (extract s callout))
             (f "rust-sp" (extract s rust-sp))
             (f "native-sp" (extract s native-sp)) (f "fp" (extract s fp))
             (f "top" (extract s top))
             (f "words" (extract s words)) (f "alloc-limit" (extract s alloc-limit))
             (f "code" (extract s code)) (f "clo" (extract s clo)) (f "delta" (extract s delta))
             (f "code-lo" (extract s code-lo)) (f "trap-stub" (extract s trap-stub))
             (f "foreign" (extract s foreign)) (f "closure" (extract s closure))
             (f "cards" (extract s cards)) (f "stack-limit" (extract s stack-limit))
             (f "overflow" (extract s overflow)) (f "poll" (extract s poll))
             (f "cons" (extract s cons)) (f "bloblet" (extract s bloblet)))
       (cv-reg-names (extract s reg4) 8 nil)))))

(define cv-pr-registers (->* (cv-nm cv-registers) string)
  (lambda (nm r)
    (let ((one (lambda ((role string) (n int)) (cv-par role (list (cv-reg nm n))))))
      (cv-par "registers"
              (list (cv-par "arguments" (cv-pr-regs nm (extract r arguments)))
                    (one "rest-in" (extract r rest-in))
                    (one "count" (extract r count)) (one "result" (extract r result))
                    (one "closure" (extract r closure)) (one "link" (extract r link))
                    (one "frame" (extract r frame))
                    (cv-par "pinned"
                            (list (one "state" (extract r state)) (one "fuel" (extract r fuel))
                                           (one "stack-limit" (extract r stack-limit))
                                           (one "code-distance" (extract r code-distance))))
                    "(lost-across-calls all-but-pinned)")))))
(define cv-pr-bits (->* (cv-bits) cv-strs)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((b (car bs)))
          (the cv-strs (cons (cv-par (extract b name) (list (int->string (extract b at))
                                                            (int->string (extract b width))))
                             (cv-pr-bits (cdr bs))))))))
(define cv-pr-values (->* (cv-values) string)
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
;; How a frame is made: arm64's `sub`, `stp` and `add`; x86_64's return
;; address popped, the link and it stored, and the frame's register set.
(define cv-pr-made (->* (cv-nm cv-frames int int) string)
  (lambda (nm f fp lr)
    (let ((sp (cv-sp nm)) (above (lambda ((k int)) (int->string (- k (extract f header))))))
      (cv-par "made"
              (if (extract nm x86)
                  (list "pop" "return" "sub" sp "store" (cv-reg nm fp) sp (above (extract f link))
                        "store" "return" sp (above (extract f return)) "lea" (cv-reg nm fp) sp
                        (above 0))
                  (list "sub" sp "stp" (cv-reg nm fp) (cv-reg nm lr) "add" (cv-reg nm fp) sp
                        (above 0)))))))
(define cv-pr-frames (->* (cv-nm cv-frames int int) string)
  (lambda (nm f fp lr)
    (let ((at (lambda ((role string) (k int)) (cv-par role (list (cv-reg nm fp) (int->string k))))))
      (cv-par "frames"
              (list (cv-kv "align" (extract f align)) (at "header" (extract f header))
                    (at "link" (extract f link)) (at "return" (extract f return))
                    (cv-par "map" (list (cv-reg nm fp) (int->string (extract f map))
                                        (cv-kv "live-slots-below" (extract f live-below))
                                        (cv-par "fields-above"
                                                (list (int->string (extract f fields-above))
                                                      "link" "return" "map" "values"))
                                        "(all-live negative)"))
                    (at "values-from" (extract f values-from)) "(raw-after-values)"
                    "(keeps-its-code)" "(map-stored-before calls routines-that-collect)"
                    (cv-pr-made nm f fp lr)
                    (cv-kv "stub" (extract f stub)))))))
;; `(entry state field)`, the field's name from its offset.
(define cv-pr-entry (->* (cv-names int) string)
  (lambda (sn k) (cv-par "entry" (list "state" (cv-name-at sn k)))))
(define cv-pr-in (->* (cv-nm cv-regs) cv-strs)
  (lambda (nm rs)
    (if (null? rs)
        nil
        (the cv-strs
             (cons (cv-par (extract (car rs) name) (cv-pr-regs nm (extract (car rs) registers)))
                           (cv-pr-in nm (cdr rs)))))))
;; A routine, `more` after what every routine says.
(define cv-pr-routine (->* (string cv-routine cv-nm cv-strs) string)
  (lambda (name r nm more)
    (let* ((tail (if (extract r may-collect) (the cv-strs (cons "(may-collect)" more)) more))
           (tail (if (= (extract r out) -1)
                     tail
                     (the cv-strs (cons (cv-par "out" (list (cv-reg nm (extract r out)))) tail)))))
      (cv-par name (the cv-strs (cons (cv-pr-entry (extract nm sn) (extract r entry))
                                      (cons (cv-par "in" (cv-pr-in nm (extract r in))) tail)))))))
(define cv-pr-overflow (->* (cv-overflow cv-nm int int) string)
  (lambda (o nm limit lr)
    (cv-par "overflow"
            (list (cv-par "when" (list (cv-sp nm) "below" (cv-reg nm limit) "after-frame-made"))
                  (cv-par "entry" (list "state" (cv-name-at (extract nm sn) (extract o entry)) "by"
                                        (if (= lr -2) "call" (cv-reg nm lr))))
                  (cv-par "in"
                          (list (cv-par "code" (list (cv-reg nm (extract o code))))
                                (cv-par "info"
                                        (list (cv-reg nm (extract o info))
                                              (cv-par "arguments-held"
                                                      (list (int->string (extract o held-at))
                                                            (int->string (extract o held-width))))
                                              (cv-kv "closure-read" (extract o closure-read))
                                              (cv-kv "variadic" (extract o variadic))))))
                  (cv-par "keeps" (cv-pr-regs nm (extract o keeps)))))))
(define cv-pr-routines (->* (convention cv-nm) string)
  (lambda (c nm)
    (let ((rs (extract c routines)) (sn (extract nm sn)) (rg (extract c registers)))
      (cv-par "routines"
              (list (cv-pr-routine "foreign" (extract rs foreign) nm nil)
                    (cv-pr-overflow (extract rs overflow) nm (extract rg stack-limit)
                                    (extract rg link))
                    (cv-pr-routine "poll" (extract rs poll) nm (list "(traps-when-spent 1)"))
                    (cv-pr-routine "cons" (extract rs cons) nm nil)
                    (cv-pr-routine "bloblet" (extract rs bloblet) nm
                                   (list "(makes (kind bloblet) (trailer 1) zeroed)"
                                         "(traps-when-refused 3)"))
                    (let ((t (extract rs trap)))
                      (cv-par "trap"
                              (list (cv-pr-entry sn (extract t entry))
                                    (cv-par "in"
                                            (list (cv-par "kind"
                                                          (list (cv-reg nm (extract t kind))))))
                                    (cv-par "kinds" (cv-pr-numbered (extract t kinds)))))))))))
;; How `c` names its places.
(define cv-naming (->* (convention) cv-nm)
  (lambda (c)
    (product (x86 (string=? (extract c target) "x86_64"))
             (sn (cv-state-names (extract c state))))))
;; A convention's clauses, as a declaration says them, in fixpt's order.
(define cv-print (->* (convention) cv-strs)
  (lambda (c)
    (let* ((rg (extract c registers)) (cl (extract c closures)) (nm (cv-naming c))
           (sn (extract nm sn)) (fu (extract c fuel)) (ba (extract c barrier)))
      (list (cv-par "target" (list (extract c target)))
            (cv-pr-registers nm rg)
            (cv-pr-values (extract c values))
            (cv-par "closures"
                    (list (cv-kv "kind" (extract cl kind))
                          (cv-kv "code-field" (extract cl code-field))
                          (cv-kv "first-free-field" (extract cl first-free-field))
                          (if (extract cl code-always-runs)
                              (cv-par "code-always-runs" nil)
                              (cv-par "native-when-code-at-least"
                                      (list (cv-name-at sn
                                                        (extract cl native-when-code-at-least)))))))
            (cv-par "code"
                    (list (cv-par "runs-at"
                                  (list "reference" "plus" (cv-reg nm (extract rg code-distance))))
                          (cv-kv "field-k-before-code"
                                 (extract (extract c code) field-k-before-code))))
            (cv-pr-frames nm (extract c frames) (extract rg frame) (extract rg link))
            (cv-par "state" (cv-pr-names sn))
            (cv-pr-routines c nm)
            (cv-par "fuel" (list (if (>= (extract fu register) cv-in-state)
                                     (cv-reg nm (extract fu register))
                                     (cv-par "register" (list (cv-reg nm (extract fu register)))))
                                 (cv-kv "subtract" (extract fu subtract)) "(on entry back-edge)"
                                 "(borrow poll)"))
            (cv-par "barrier"
                    (list (cv-par "cards" (list "state" (cv-name-at sn (extract ba cards))))
                          (cv-kv "card-shift" (extract ba card-shift))
                          (cv-kv "mark" (extract ba mark))))))))

;;; ------------------------------------------------------------ reading back

;; A clause's role, from its text: up to its first space or `)`.
(define cv-role-of (->* (string) string)
  (lambda (t) (substring t 1 (cv-atom-end t 1))))
;; The clause of `ts` whose role is `role`; "" if none is.
(define cv-clause (->* (cv-strs string) string)
  (lambda (ts role)
    (cond ((null? ts) "")
          ((string=? (cv-role-of (car ts)) role) (car ts))
          (else (cv-clause (cdr ts) role)))))
;; Why `ts`, declared, is not `back`, printed: "" if it is.
(define cv-differs (->* (cv-strs cv-strs) string)
  (lambda (ts back)
    (if (null? back)
        ""
        (let* ((b (car back)) (role (cv-role-of b)) (t (cv-clause ts role)))
          (cond ((string=? t "") (string-append "no `" role "` clause"))
                ((string=? t b) (cv-differs ts (cdr back)))
                (else (string-append "the `" role "` clause is not one a convention holds: "
                                     t)))))))
;; A clause of `ts` none of `back` has the role of: "" if none.
(define cv-extra (->* (cv-strs cv-strs) string)
  (lambda (ts back)
    (cond ((null? ts) "")
          ((string=? (cv-clause back (cv-role-of (car ts))) "")
           (string-append "a `" (cv-role-of (car ts))
                          "` clause, which a convention has no room for"))
          (else (cv-extra (cdr ts) back)))))
(define cv-parse-all (->* (cv-strs) cv-sxs)
  (lambda (ts)
    (if (null? ts)
        nil
        (the cv-sxs (cons (extract (cv-read-at (car ts) 0) x) (cv-parse-all (cdr ts)))))))
;; A declaration's clauses, read: the convention, or why not.
(define cv-read-clauses (->* (cv-strs) cv-read)
  (lambda (ts)
    (let* ((c (cv-of (cv-parse-all ts))) (back (cv-print c))
           (why (let ((d (cv-differs ts back))) (if (string=? d "") (cv-extra ts back) d))))
      (if (string=? why "") (sum ok c) (sum refused why)))))
;; fixpt's own native convention, read.
(define cv-native (->* () cv-read)
  (lambda () (cv-read-clauses (the cv-strs (native-convention)))))))
