;;; Typed hygienic macros, in FX-26: a signature inferred, as a signature
;;; writes it (`infer.rs`'s `shown_sty`), and as a message says it
;;; (`sig_text`). On top of `macros-infer.fx`, which it loads and gives on
;;; (`infer-module`), for `macros-solve.fx`.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define infer-module ((proj (load-module "fx26:macros-infer.fx") rs re rm rc rp)))
(define files-module (with infer-module files-module))
(define align-module (with files-module align-module))
(define types-module (with align-module types-module))
(define parser-module (with types-module parser-module))
(define reader-types (with parser-module reader-types))
(import reader-types atom lst dotted (type syn))
(import parser-module syn-symbol? syn-name mk-list mk-symbol syn-datums syn->datum
        (type syns-a))
(import types-module show-syn kind-of lowered reserved-sym? s-mark
        s-expr s-bvar s-id s-data s-type s-label s-nil s-literal s-pair s-import s-export s-mu
        s-var s-many s-union s-typed s-lambda s-defn s-dvar s-kind bind-rib bind-cage ring-rib
        ring-at syntax-sig-of (type addr entries ring rings bind sty stys))
(import infer-module open?)

;;; ------------------------------------------------------------ written

;; Syntax type `t` as a signature writes it, at `a`..`b` (`infer.rs`'s
;; `shown_sty`): a `mu` whose variable is used, or whose addresses are
;; from it; a list by ellipsis, `(σ ...)`. `shown`, the `mu`s being
;; written, the innermost first, each its variable and whether it is used.
(define shown (ref (listof (tupleof string bool) acyclic) rs) (new nil))
(define show-sty (->* (sty int int) syn)
  (lambda (t a b)
    (let ((sym (lambda ((s string)) (mk-symbol s a b))))
      (tagcase t
        (s-expr () (sym "expr")) (s-lambda () (sym "lambda")) (s-bvar () (sym "bvar"))
        (s-id () (sym "id")) (s-data () (sym "data")) (s-type () (sym "desc"))
        (s-label () (sym "label")) (s-dvar () (sym "dvar")) (s-kind () (sym "kind"))
        (s-defn () (sym "defn")) (s-item () (sym "item")) (s-rules () (sym "rules"))
        (s-nil () (mk-list nil a b))
        ;; A `syntax-rules`' trailmark, inferred as a word its pattern
        ;; writes; a reserved name but the standard trailmarks, a kernel
        ;; form's word.
        (s-literal (n)
          (mk-list (list (sym (if (word? n) "literal" "trailmark")) (atom n a b 0)) a b))
        (s-mark (n i) (mk-list (list (sym "trailmark") (atom n a b 0)) a b))
        (s-pair (x y) (show-pair t nil a b))
        (s-import (x bd) (mk-list (list (sym "import") (show-sty x a b) (show-bind bd a b)) a b))
        (s-export (x bd) (mk-list (list (sym "export") (show-sty x a b) (show-bind bd a b)) a b))
        (s-many (x) (mk-list (list (sym "many") (show-sty x a b)) a b))
        (s-typed (x h) (show-sty x a b))
        (s-union (ms) (mk-list (cons (sym "oneof") (show-each ms a b)) a b))
        (s-var (j) (begin (set shown (used! j (get shown))) (sym (extract (nth-shown j) 1))))
        (s-mu (x r p) (show-mu t a b))))))
(define show-each (->* (stys int int) syns-a)
  (lambda (ms a b) (if (null? ms) nil (cons (show-sty (car ms) a b) (show-each (cdr ms) a b)))))
(define show-pair (->* (sty syns-a int int) syn)
  (lambda (cur items a b)
    (tagcase cur
      (s-pair (x y) (show-pair y (append items (the syns-a (list (show-sty x a b)))) a b))
      (s-nil () (mk-list items a b))
      (s-mu (x r p)
        (let ((e (listed-elem cur)))
          (if (null? e)
              (joined-list items (show-sty cur a b) a b)
              (mk-list (append items
                               (the syns-a (list (show-sty (car e) a b) (mk-symbol "..." a b))))
                       a b))))
      (else y (joined-list items (show-sty cur a b) a b)))))
;; Items `xs` and tail `t` as one list: a tail that is a list joined to it.
(define joined-list (->* (syns-a syn int int) syn)
  (lambda (xs t a b)
    (tagcase t
      (lst (more d c e y) (mk-list (append xs more) a b))
      (dotted (more tl d c e y)
        (dotted (append xs more) tl (datum-dotted (syn-datums (append xs more)) (syn->datum tl))
                a b 0))
      (else y
        (if (null? xs) t (dotted xs t (datum-dotted (syn-datums xs) (syn->datum t)) a b 0))))))
(define nth-shown (->* (int) (tupleof string bool))
  (lambda (j) (nth-of j (get shown))))
(define nth-of (->* (int (listof (tupleof string bool) acyclic)) (tupleof string bool))
  (lambda (j xs) (if (= j 0) (car xs) (nth-of (- j 1) (cdr xs)))))
(define used! (->* (int (listof (tupleof string bool) acyclic))
                   (listof (tupleof string bool) acyclic))
  (lambda (j xs)
    (if (= j 0)
        (cons (tuple (extract (car xs) 1) #t) (cdr xs))
        (cons (car xs) (used! (- j 1) (cdr xs))))))
(define len-shown (->* ((listof (tupleof string bool) acyclic)) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (len-shown (cdr xs))))))
(define show-mu (->* (sty int int) syn)
  (lambda (t a b)
    (let ((e (listed-elem t)) (body (tagcase t (s-mu (x r p) x) (else y t))))
      (if (not (null? e))
          (mk-list (list (show-sty (car e) a b) (mk-symbol "..." a b)) a b)
          (let ((name (string-append "m" (int->string (+ (len-shown (get shown)) 1)))))
            (begin
              (set shown (cons (tuple name #f) (get shown)))
              (let* ((shown-body (show-sty body a b)) (used (extract (car (get shown)) 2)))
                (begin
                  (set shown (cdr (get shown)))
                  (if (or used (open? body))
                      (mk-list (list (mk-symbol "mu" a b) (mk-symbol name a b) shown-body) a b)
                      shown-body)))))))))
;; The element of `mu` `t`, in a list of one, if it is a list as `(σ ...)`
;; writes one (`seq-type`) and its element does not refer to it: its
;; element as written, outside the list's `mu`.
(define listed-elem (->* (sty) stys)
  (lambda (t)
    (let ((e (tagcase t
               (s-mu (x r p)
                 (tagcase x
                   (s-union (ms)
                     (if (and (not (null? ms)) (not (null? (cdr ms))) (null? (cdr (cdr ms))))
                         (listed-of (car ms) (car (cdr ms)))
                         nil))
                   (else y nil)))
               (else y nil))))
      (if (null? e) nil (lowered (car e))))))
(define tail-of? (->* (sty) bool) (lambda (d) (tagcase d (s-var (j) (= j 0)) (else y #f))))
(define listed-of (->* (sty sty) stys)
  (lambda (nil-m pair-m)
    (tagcase nil-m
      (s-nil ()
        (tagcase pair-m
          (s-pair (e d)
            (if (and (tail-of? d)
                     (tagcase e (s-bvar () #f) (s-dvar () #f) (s-export (x bd) #f) (else y #t)))
                (list e)
                nil))
          (else y nil)))
      (s-export (n none)
        (tagcase pair-m
          (s-export (p both)
            (if (and (= (kind-of n) 6) (no-entries? none))
                (tagcase p
                  (s-pair (e d)
                    (if (tail-of? d)
                        (tagcase e
                          ;; An element's own export not a rib's: the pair's the element's.
                          (s-export (x bd) (if (both-ribs? both) (list e) nil))
                          (else y (rebased-elem e both)))
                        nil))
                  (else y nil))
                nil))
          (else y nil)))
      (else y nil))))
;; Element `e` of a list whose pair exports `both`, the element's entries from the pair's root,
;; then the rest's, `(D rib)` (`seq-body`), in a list of one (`infer.rs`'s `seq_elem`).
(define rebased-elem (->* (sty bind) stys)
  (lambda (e both)
    (tagcase both
      (bind-rib (es)
        (let ((own (own-of es)))
          (cond ((null? own) nil)
                ((and (= (kind-of e) 1) (self-entry? (bind-rib (car own)) 1)) (list e))
                ((and (= (kind-of e) 12) (self-entry? (bind-rib (car own)) 4)) (list e))
                (else (list (s-export e (bind-rib (car own))))))))
      (else y nil))))
(define own-of (->* (entries) (listof entries acyclic))
  (lambda (es)
    (cond ((null? es) nil)
          ((null? (cdr es)) (if (entry-is? (car es) (list #f) 2) (list (the entries nil)) nil))
          ((and (not (null? (extract (car es) 1))) (car (extract (car es) 1)))
           (let ((r (own-of (cdr es))))
             (if (null? r)
                 nil
                 (list (cons (tuple (cdr (extract (car es) 1)) (extract (car es) 2)) (car r))))))
          (else nil))))
(define no-entries? (->* (bind) bool)
  (lambda (bd) (tagcase bd (bind-rib (es) (null? es)) (else y #f))))
(define both-ribs? (->* (bind) bool)
  (lambda (bd)
    (tagcase bd
      (bind-rib (es)
        (and (= (len-entries es) 2)
             (entry-is? (car es) (list #t) 2) (entry-is? (car (cdr es)) (list #f) 2)))
      (else y #f))))
(define self-entry? (->* (bind int) bool)
  (lambda (bd delta)
    (tagcase bd
      (bind-rib (es) (and (= (len-entries es) 1) (entry-is? (car es) nil delta)))
      (else y #f))))
(define len-entries (->* (entries) int)
  (lambda (es) (if (null? es) 0 (+ 1 (len-entries (cdr es))))))
(define entry-is? (->* ((tupleof addr int) addr int) bool)
  (lambda (e a delta) (and (addr-same? (extract e 1) a) (= (extract e 2) delta))))
(define addr-same? (->* (addr addr) bool)
  (lambda (x y)
    (if (null? x)
        (null? y)
        (and (not (null? y)) (eq? (car x) (car y)) (addr-same? (cdr x) (cdr y))))))
(define show-bind (->* (bind int int) syn)
  (lambda (bd a b)
    (tagcase bd
      (bind-rib (es) (show-rib es a b))
      (bind-cage (rs) (mk-list (cons (mk-symbol "cage" a b) (show-rings rs a b)) a b))
      (else y (show-rib nil a b)))))
(define show-rings (->* (rings int int) syns-a)
  (lambda (rs a b)
    (if (null? rs)
        nil
        (cons (tagcase (car rs)
                (ring-rib (es) (show-rib es a b))
                (ring-at (x) (mk-list (list (mk-symbol "at" a b) (show-addr x a b)) a b))
                (ring-shape (x) (mk-list (list (mk-symbol "shape" a b) (show-addr x a b)) a b)))
              (show-rings (cdr rs) a b)))))
(define show-rib (->* (entries int int) syn)
  (lambda (es a b) (mk-list (cons (mk-symbol "rho" a b) (show-entries es a b)) a b)))
(define show-entries (->* (entries int int) syns-a)
  (lambda (es a b)
    (if (null? es)
        nil
        (cons (mk-list (list (show-addr (extract (car es) 1) a b)
                             (let ((d (extract (car es) 2)))
                               (if (>= d 100) (syntax-sig-of d) (mk-symbol (delta-name d) a b))))
                       a b)
              (show-entries (cdr es) a b)))))
(define delta-name (->* (int) string)
  (lambda (d)
    (cond ((= d 0) "none") ((= d 1) "var") ((= d 2) "rib") ((= d 3) "env") ((= d 4) "dvar")
          (else "place"))))
;; `(path #:a #:d …)`, its steps from the root, first first.
(define show-addr (->* (addr int int) syn)
  (lambda (x a b)
    (if (null? x) (mk-list nil a b) (mk-list (cons (mk-symbol "path" a b) (path-keys x a b)) a b))))
(define path-keys (->* (addr int int) syns-a)
  (lambda (x a b)
    (if (null? x)
        nil
        (cons (atom (symbol->keyword (if (car x) 'a 'd)) a b 0) (path-keys (cdr x) a b)))))

;; Signature `s` as a message says it (`infer.rs`'s `sig_text`): each
;; annotation, `union`, `mu`, `many` or literal that is a list's rest after
;; a ` . `.
(define sig-text (->* (syn) string)
  (lambda (s)
    (tagcase s
      (lst (items d a b x) (if (null? items) "()" (string-append "(" (sig-items items #t a b) ")")))
      (dotted (items tl d a b x)
        (string-append "(" (sig-items items #f a b) " . " (sig-text tl) ")"))
      (else y (show-syn s)))))
(define sig-word? (->* (syn) bool)
  (lambda (s)
    (and (syn-symbol? s)
         (let ((n (syn-name s)))
           (or (string=? n "import") (string=? n "export") (string=? n "union") (string=? n "oneof")
               (string=? n "mu") (string=? n "trailmark")
               (string=? n "many") (string=? n "literal"))))))
;; Whether `n` is a kernel form's word, as a signature shows it: reserved,
;; and not one of the standard trailmarks, `else` and `=>`.
(define word? (->* (symbol) bool)
  (lambda (n) (and (reserved-sym? n) (not (symbol=? n 'else)) (not (symbol=? n '=>)))))
;; Items `xs`, the first first (`first`); a word of `sig-word?` past the
;; first, and a proper list's, starts its rest.
(define sig-items (->* (syns-a bool int int) string)
  (lambda (xs proper a b) (sig-items-from xs #t proper a b)))
(define sig-items-from (->* (syns-a bool bool int int) string)
  (lambda (xs first proper a b)
    (cond ((null? xs) "")
          ((and (not first) proper (sig-word? (car xs)))
           (string-append " . " (sig-text (mk-list xs a b))))
          (else (string-append (if first "" " ") (sig-text (car xs))
                               (sig-items-from (cdr xs) #f proper a b))))))
