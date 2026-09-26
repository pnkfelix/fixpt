;;; The checker, in FX-26 (PLAN.md §11, step 10).
;;;
;;; The Rust checker's rules (`check.rs`, `infer.rs`) and its reading of
;;; descriptions (`parse.rs`, `top.rs`), over the parser's trees, rule for
;;; rule and message for message, so the two can be compared: for each
;;; top-level form, what it defines or what type and effect it has; or the
;;; first error, and where it is.
;;;
;;; Types live in an arena, as in Rust: a type is an index, and a recursive
;;; type is a cycle of indexes through forwarding links. Effects are sets of
;;; atoms kept sorted, so `(maxeff e (maxeff e pure))` and `e` are one list;
;;; the order is this file's own, and printing follows it.
;;;
;;; The parser keeps descriptions as the syntax they were written in. A
;;; first pass, `k-resolve`, reads them into the arena, in the order the Rust
;;; parser does (a `lambda`'s parameter types before its body, a `letrec`'s
;;; type before its initialiser), so the first error is the same one.
;;;
;;; Compiled with the reader and the parser, as one program. Its store is
;;; @t and its failures abort to a prompt in @z, both its own.

(private-regions @t @z)

;; The checker's state, and everything checking may do.
(define-effect kstate (maxeff (read @t) (write @t) (alloc @t)))
(define-effect checks (maxeff (read @s) (read @a) kstate (goto @z)))

;;; ------------------------------------------------------------ descriptions

;; A region: a constant `@name`, a fresh one (made by inference, a bloblet,
;; or `private-regions`, which no program can name), or a binder.
(define-datatype k-region (r-const symbol) (r-fresh int string) (r-var int))

(define-datatype k-atom
  (a-read k-region) (a-write k-region) (a-alloc k-region)
  (a-goto k-region) (a-comefrom k-region) (a-await k-region) (a-var int))
(define-type k-eff (listof k-atom @t))

(define-type k-ids (listof int @t))
;; A binder: a description variable and its kind, 0 region, 1 effect, 2 type.
(define-type k-binders (listof (productof (1 int) (2 int)) @t))
(define-type k-parts (listof (productof (1 symbol) (2 int)) @t))
(define-type k-names (listof symbol @t))

(define-datatype k-ty
  (ty-base symbol)
  (ty-void)
  (ty-var int)
  (ty-subr k-eff k-ids int)
  (ty-poly k-binders int)
  (ty-ref int k-region)
  (ty-pair int int k-region)
  ;; answer, payload, bound, region
  (ty-tag int int k-eff k-region)
  ;; argument, answer, effect, region
  (ty-comp int int k-eff k-region)
  (ty-markkey int k-region)
  (ty-product k-parts)
  (ty-sum k-parts)
  (ty-array int k-region)
  (ty-icell int k-region)
  (ty-bloblet k-ids bool k-region)
  ;; A forwarding slot: none or one.
  (ty-link k-ids))

;; A description in argument position, what `proj` supplies.
(define-datatype k-desc (dr k-region) (de k-eff) (dt int))
(define-type k-map (listof (pairof int k-desc @t) @t))

;; What a description name means where it is used.
(define-datatype k-ds
  (ds-var int int)
  (ds-rec int)
  (ds-abbrev (listof (productof (1 symbol) (2 int)) @t) syn)
  (ds-region k-region)
  (ds-eff k-eff)
  (ds-private k-region))

;;; ------------------------------------------------------------ expressions
;;; The parser's trees with their descriptions read. Each ends with where it
;;; starts and ends.

(define-datatype kx
  (x-var symbol int int)
  ;; A literal: its type.
  (x-const int int int)
  (x-lambda (listof (productof (1 symbol) (2 k-ids)) @t) kx int int)
  (x-app kx (listof kx @t) int int)
  (x-plambda k-binders kx int int)
  ;; `letregion`: the region variable, and the body.
  (x-letregion int kx int int)
  (x-proj kx (listof k-desc @t) int int)
  (x-if kx kx kx int int)
  (x-letrec (listof (productof (1 symbol) (2 int) (3 kx)) @t) kx int int)
  (x-let (listof (productof (1 symbol) (2 kx)) @t) kx int int)
  (x-begin (listof kx @t) int int)
  (x-prompt kx kx kx int int)
  (x-the int kx int int)
  (x-bloblet symbol int (listof kx @t) int int)
  (x-product (listof (productof (1 symbol) (2 kx)) @t) int int)
  (x-extract kx symbol int int)
  (x-sum symbol kx int int)
  (x-tagcase kx (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) @t)
             (listof (productof (1 symbol) (2 kx)) @t) int int))
(define-type kxs (listof kx @t))

;; A type and an effect.
(define-type k-te (productof (1 int) (2 k-eff)))
(define k-te (subr pure (int k-eff) k-te) (lambda (t e) (product (1 t) (2 e))))

;; What checking a program found, or the first error; and, inside, what a
;; computation whose errors are being rewritten produced.
(define-datatype k-result
  (k-ok (listof string @t))
  (k-err string int int)
  (k-done k-te))

(define k-tag (prompt-tag k-result k-result (maxeff (read @s) (read @a) kstate) @z)
  (make-continuation-prompt-tag))
(define k-fail (subr checks (string int int) void)
  (lambda (m a b) (abort-current-continuation k-tag (k-err m a b))))

;;; ---------------------------------------------------------------- strings

(define k-cat3 (subr pure (string string string) string)
  (lambda (a b c) (string-append a (string-append b c))))
(define k-cat4 (subr pure (string string string string) string)
  (lambda (a b c d) (string-append a (k-cat3 b c d))))
(define k-cat5 (subr pure (string string string string string) string)
  (lambda (a b c d e) (string-append a (k-cat4 b c d e))))
(define k-quote (subr pure (string) string) (lambda (n) (k-cat3 "`" n "`")))

(define k-join (subr (read @t) ((listof string @t) string) string)
  (lambda (xs sep)
    (cond ((null? xs) "")
          ((null? (cdr xs)) (car xs))
          (else (k-cat3 (car xs) sep (k-join (cdr xs) sep))))))

(define k-starts-at? (subr pure (string string int int) bool)
  (lambda (s sub at i)
    (cond ((= i (string-length sub)) #t)
          ((>= (+ at i) (string-length s)) #f)
          ((char=? (string-ref s (+ at i)) (string-ref sub i)) (k-starts-at? s sub at (+ i 1)))
          (else #f))))
;; Where `sub` first starts in `s` from `at`, or -1.
(define k-find-sub (subr pure (string string int) int)
  (lambda (s sub at)
    (cond ((> (+ at (string-length sub)) (string-length s)) -1)
          ((k-starts-at? s sub at 0) at)
          (else (k-find-sub s sub (+ at 1))))))

(define k-str-cmp (subr pure (string string int) int)
  (lambda (a b i)
    (cond ((= i (string-length a)) (if (= i (string-length b)) 0 -1))
          ((= i (string-length b)) 1)
          (else (let ((x (char->integer (string-ref a i))) (y (char->integer (string-ref b i))))
                  (cond ((< x y) -1) ((> x y) 1) (else (k-str-cmp a b (+ i 1)))))))))
(define k-int-cmp (subr pure (int int) int)
  (lambda (x y) (cond ((< x y) -1) ((> x y) 1) (else 0))))

;;; ------------------------------------------------------------ lists

(define k-length
  (poly ((r region)) (poly ((t type)) (subr (read r) ((listof t r)) int)))
  (plambda ((r region)) (plambda ((t type))
    (lambda ((xs (listof t r))) (if (null? xs) 0 (+ 1 (k-length (cdr xs))))))))
(define k-nth
  (poly ((r region)) (poly ((t type)) (subr (read r) ((listof t r) int) t)))
  (plambda ((r region)) (plambda ((t type))
    (lambda ((xs (listof t r)) (i int)) (if (= i 0) (car xs) (k-nth (cdr xs) (- i 1)))))))
(define k-has-name? (subr (read @t) (k-names symbol) bool)
  (lambda (xs s) (cond ((null? xs) #f) ((symbol=? (car xs) s) #t) (else (k-has-name? (cdr xs) s)))))
(define k-has-id? (subr (read @t) (k-ids int) bool)
  (lambda (xs s) (cond ((null? xs) #f) ((= (car xs) s) #t) (else (k-has-id? (cdr xs) s)))))

;;; ------------------------------------------------------------ the arena

(define k-tys (ref (arrayof k-ty @t) @t) (new (make-array 512 (ty-void))))
(define k-ntys (ref int @t) (new 0))

(define k-copy-tys (subr (maxeff (read @t) (write @t)) ((arrayof k-ty @t) (arrayof k-ty @t) int) unit)
  (lambda (from to i)
    (if (= i (array-length from))
        #u
        (begin (array-set! to i (array-ref from i)) (k-copy-tys from to (+ i 1))))))

(define k-ty-new (subr kstate (k-ty) int)
  (lambda (t)
    (let ((n (get k-ntys)))
      (begin
        (if (= n (array-length (get k-tys)))
            (let ((bigger (the (arrayof k-ty @t) (make-array (* 2 n) (ty-void)))))
              (begin (k-copy-tys (get k-tys) bigger 0) (set k-tys bigger)))
            #u)
        (array-set! (get k-tys) n t)
        (set k-ntys (+ n 1))
        n))))

(define k-raw (subr (read @t) (int) k-ty) (lambda (id) (array-ref (get k-tys) id)))
;; Follow forwarding links to the type itself.
(define k-resolve (subr (read @t) (int) int)
  (lambda (id) (tagcase (k-raw id) (ty-link (to) (if (null? to) id (k-resolve (car to)))) (else x id))))
(define k-get (subr (read @t) (int) k-ty) (lambda (id) (k-raw (k-resolve id))))
(define k-set-link (subr kstate (int int) unit)
  (lambda (slot to) (array-set! (get k-tys) slot (ty-link (cons to nil)))))
(define k-slot (subr kstate () int) (lambda () (k-ty-new (ty-link nil))))

;; Which types a walk has seen: a type is seen in walk `e` when its mark
;; is `e`, so each walk takes a new epoch and nothing is cleared.
(define k-marks (ref (arrayof int @t) @t) (new (make-array 512 0)))
(define k-epoch (ref int @t) (new 0))
(define k-new-epoch (subr kstate () int)
  (lambda () (begin (set k-epoch (+ (get k-epoch) 1)) (get k-epoch))))
(define n-copy-marks (subr (maxeff (read @t) (write @t)) ((arrayof int @t) (arrayof int @t) int) unit)
  (lambda (from to i)
    (if (= i (array-length from)) #u (begin (array-set! to i (array-ref from i)) (n-copy-marks from to (+ i 1))))))
;; Whether walk `e` has seen `t` already; if not, it has now.
(define k-visit? (subr kstate (int int) bool)
  (lambda (t e)
    (begin
      (if (>= t (array-length (get k-marks)))
          (let ((bigger (the (arrayof int @t) (make-array (* 2 (array-length (get k-tys))) 0))))
            (begin (n-copy-marks (get k-marks) bigger 0) (set k-marks bigger)))
          #u)
      (if (= (array-ref (get k-marks) t) e)
          #t
          (begin (array-set! (get k-marks) t e) #f)))))

;; Description variables, newest first, for their names.
(define k-dvars (ref k-names @t) (new nil))
(define k-ndvars (ref int @t) (new 0))
(define k-new-dvar (subr kstate (symbol) int)
  (lambda (name)
    (let ((n (get k-ndvars)))
      (begin (set k-dvars (cons name (get k-dvars))) (set k-ndvars (+ n 1)) n))))
(define k-dvar-name (subr (read @t) (int) symbol)
  (lambda (v) (k-nth (get k-dvars) (- (- (get k-ndvars) 1) v))))

;; The base types, made first, in this order, so their indexes are known.
(define k-int int 0)
(define k-bool int 1)
(define k-string int 2)
(define k-unit int 3)
(define k-char int 4)
(define k-symbol int 6)
(define k-void int 10)
(define k-base (ref (listof (pairof symbol int @t) @t) @t) (new nil))
(define k-basic (subr kstate (string) unit)
  (lambda (name)
    (let* ((s (string->symbol name)) (t (k-ty-new (ty-base s))))
      (set k-base (cons (cons s t) (get k-base))))))

;; Bindings, as lists of them are passed around.
(define-type k-bindings (listof (pairof symbol int @t) @t))
(define k-find (subr (read @t) (k-bindings symbol) int)
  (lambda (bs s)
    (cond ((null? bs) -1) ((symbol=? (car (car bs)) s) (cdr (car bs))) (else (k-find (cdr bs) s)))))

;; Value variables in scope: for each name, the types it is bound to,
;; innermost first; and the names bound, newest first, so that a scope is
;; left by unbinding back to a mark (`k-mark`, `k-unbind-to`). A lookup is
;; a table's, not a walk down every binding in scope.
(define-type k-stack (listof int @t))
(define k-env (ref (table symbol k-stack @t) @t) (new (make-table symbol-hash symbol=?)))
(define k-trail (ref k-names @t) (new nil))
(define k-depth (ref int @t) (new 0))
;; The type `s` is bound to, or -1.
(define k-lookup (subr (read @t) (symbol) int)
  (lambda (s) (let ((st (table-ref (get k-env) s nil))) (if (null? st) -1 (car st)))))
(define k-bind (subr kstate (symbol int) unit)
  (lambda (s t)
    (begin
      (table-set! (get k-env) s (cons t (table-ref (get k-env) s nil)))
      (set k-trail (cons s (get k-trail)))
      (set k-depth (+ (get k-depth) 1)))))
(define k-mark (subr (read @t) () int) (lambda () (get k-depth)))
(define k-unbind-to (subr kstate (int) unit)
  (lambda (m)
    (if (<= (get k-depth) m)
        #u
        (let ((s (car (get k-trail))))
          (begin
            (table-set! (get k-env) s (cdr (table-ref (get k-env) s nil)))
            (set k-trail (cdr (get k-trail)))
            (set k-depth (- (get k-depth) 1))
            (k-unbind-to m))))))

;; Description names in scope, innermost first.
(define-type k-scope (listof (pairof symbol k-ds @t) @t))
(define k-dscope (ref k-scope @t) (new nil))
(define k-find-desc (subr (maxeff (read @t) (alloc @t)) (k-scope symbol) (listof k-ds @t))
  (lambda (ds s)
    (cond ((null? ds) nil) ((symbol=? (car (car ds)) s) (cons (cdr (car ds)) nil)) (else (k-find-desc (cdr ds) s)))))
;; What `s` means as a description: none or one.
(define k-lookup-desc (subr (maxeff (read @t) (alloc @t)) (symbol) (listof k-ds @t))
  (lambda (s) (k-find-desc (get k-dscope) s)))
(define k-push-desc (subr kstate (symbol k-ds) unit)
  (lambda (n d) (set k-dscope (cons (cons n d) (get k-dscope)))))

;; How many fresh regions have been made, for naming the next.
(define k-fresh (ref int @t) (new 0))
(define k-fresh-region (subr kstate (string) k-region)
  (lambda (base)
    (let ((n (+ (get k-fresh) 1)))
      (begin (set k-fresh n) (r-fresh n (k-cat3 base "." (int->string n)))))))

;; How deep in abbreviations' expansions reading is.
(define k-expanding (ref int @t) (new 0))

;; What checking proved that running needs: each `extract`'s field, by
;; position, keyed by where the `extract` is. Only the product's type says.
(define-type k-facts (listof (productof (1 int) (2 int) (3 int)) @t))
(define k-extracts (ref k-facts @t) (new nil))
(define checked-extracts (subr (read @t) () k-facts) (lambda () (get k-extracts)))

;;; ------------------------------------------------------------ effects

(define k-region-rank (subr pure (k-region) int)
  (lambda (r) (tagcase r (r-const (n) 0) (r-fresh (i n) 1) (r-var (v) 2))))
(define k-region-cmp (subr pure (k-region k-region) int)
  (lambda (r s)
    (let ((c (k-int-cmp (k-region-rank r) (k-region-rank s))))
      (if (= c 0)
          (tagcase r
            (r-const (n) (tagcase s (r-const (m) (k-str-cmp (symbol->string n) (symbol->string m) 0)) (else y 0)))
            (r-fresh (i n) (tagcase s (r-fresh (j m) (k-int-cmp i j)) (else y 0)))
            (r-var (v) (tagcase s (r-var (w) (k-int-cmp v w)) (else y 0))))
          c))))
(define k-region=? (subr pure (k-region k-region) bool) (lambda (r s) (= (k-region-cmp r s) 0)))

(define k-atom-rank (subr pure (k-atom) int)
  (lambda (a) (tagcase a (a-read (r) 0) (a-write (r) 1) (a-alloc (r) 2) (a-goto (r) 3) (a-comefrom (r) 4) (a-await (r) 5) (a-var (v) 6))))
;; The atom's region; a variable's is none, shown as a binder -1.
(define k-atom-region (subr pure (k-atom) k-region)
  (lambda (a)
    (tagcase a (a-read (r) r) (a-write (r) r) (a-alloc (r) r) (a-goto (r) r) (a-comefrom (r) r) (a-await (r) r) (a-var (v) (r-var -1)))))
(define k-has-region? (subr pure (k-atom) bool) (lambda (a) (< (k-atom-rank a) 6)))
(define k-atom-cmp (subr pure (k-atom k-atom) int)
  (lambda (a b)
    (let ((c (k-int-cmp (k-atom-rank a) (k-atom-rank b))))
      (cond ((not (= c 0)) c)
            ((k-has-region? a) (k-region-cmp (k-atom-region a) (k-atom-region b)))
            (else (tagcase a (a-var (v) (tagcase b (a-var (w) (k-int-cmp v w)) (else y 0))) (else y 0)))))))
(define k-atom-with (subr pure (k-atom k-region) k-atom)
  (lambda (a r)
    (tagcase a (a-read (x) (a-read r)) (a-write (x) (a-write r)) (a-alloc (x) (a-alloc r))
      (a-goto (x) (a-goto r)) (a-comefrom (x) (a-comefrom r)) (a-await (x) (a-await r)) (a-var (v) a))))

(define k-insert (subr (maxeff (read @t) (alloc @t)) (k-atom k-eff) k-eff)
  (lambda (a e)
    (if (null? e)
        (cons a nil)
        (let ((c (k-atom-cmp a (car e))))
          (cond ((< c 0) (cons a e)) ((= c 0) e) (else (cons (car e) (k-insert a (cdr e)))))))))
(define k-union (subr (maxeff (read @t) (alloc @t)) (k-eff k-eff) k-eff)
  (lambda (x y) (if (null? x) y (k-union (cdr x) (k-insert (car x) y)))))
(define k-contains? (subr (read @t) (k-eff k-atom) bool)
  (lambda (e a) (cond ((null? e) #f) ((= (k-atom-cmp (car e) a) 0) #t) (else (k-contains? (cdr e) a)))))
(define k-within? (subr (read @t) (k-eff k-eff) bool)
  (lambda (x y) (or (null? x) (and (k-contains? y (car x)) (k-within? (cdr x) y)))))
(define k-eff=? (subr (read @t) (k-eff k-eff) bool) (lambda (x y) (and (k-within? x y) (k-within? y x))))
(define k-one (subr (alloc @t) (k-atom) k-eff) (lambda (a) (cons a nil)))
(define k-allocates? (subr (read @t) (k-eff) bool)
  (lambda (e) (cond ((null? e) #f) ((= (k-atom-rank (car e)) 2) #t) (else (k-allocates? (cdr e))))))

;;; ------------------------------------------------------------ printing

(define k-region-show (subr (read @t) (k-region) string)
  (lambda (r) (tagcase r (r-const (n) (symbol->string n)) (r-fresh (i n) n) (r-var (v) (symbol->string (k-dvar-name v))))))
(define k-atom-show (subr (read @t) (k-atom) string)
  (lambda (a)
    (letrec ((one (subr (read @t) (string k-region) string) (lambda (op r) (k-cat5 "(" op " " (k-region-show r) ")"))))
      (tagcase a
        (a-read (r) (one "read" r)) (a-write (r) (one "write" r)) (a-alloc (r) (one "alloc" r))
        (a-goto (r) (one "goto" r)) (a-comefrom (r) (one "comefrom" r)) (a-await (r) (one "await" r))
        (a-var (v) (symbol->string (k-dvar-name v)))))))
(define k-atoms-show (subr (read @t) (k-eff) string)
  (lambda (e) (if (null? e) "" (string-append (string-append " " (k-atom-show (car e))) (k-atoms-show (cdr e))))))
;; `pure`, a single atom, or `(maxeff …)`.
(define k-show-effect (subr (read @t) (k-eff) string)
  (lambda (e)
    (cond ((null? e) "pure")
          ((null? (cdr e)) (k-atom-show (car e)))
          (else (k-cat3 "(maxeff" (k-atoms-show e) ")")))))

(define k-kind-name (subr pure (int) string)
  (lambda (k) (cond ((= k 0) "region") ((= k 1) "effect") (else "type"))))
;; As Rust's `{:?}` writes a kind.
(define k-kind-debug (subr pure (int) string)
  (lambda (k) (cond ((= k 0) "Region") ((= k 1) "Effect") (else "Type"))))

;; The name `define-type` gave `t`, innermost first: each name's innermost
;; binding only.
(define k-abbrev-in (subr (maxeff (read @t) (alloc @t)) (k-scope k-names int) (listof string @t))
  (lambda (ds seen t)
    (if (null? ds)
        nil
        (let ((n (car (car ds))))
          (tagcase (cdr (car ds))
            (ds-rec (d)
              (cond ((k-has-name? seen n) (k-abbrev-in (cdr ds) seen t))
                    ((= (k-resolve d) t) (cons (symbol->string n) nil))
                    (else (k-abbrev-in (cdr ds) (cons n seen) t))))
            (else y (k-abbrev-in (cdr ds) seen t)))))))
(define k-show-binders (subr (maxeff (read @t) (alloc @t)) (k-binders) (listof string @t))
  (lambda (bs)
    (if (null? bs)
        nil
        (cons (k-cat5 "(" (symbol->string (k-dvar-name (extract (car bs) 1))) " " (k-kind-name (extract (car bs) 2)) ")")
              (k-show-binders (cdr bs))))))

(define-rec
  (k-show-on (subr (maxeff (read @t) (alloc @t)) (int k-ids) string)
    (lambda (t path)
      (let* ((t (k-resolve t)) (name (k-abbrev-in (get k-dscope) nil t)))
        (if (null? name) (k-show-body t path) (car name)))))
  (k-show-list (subr (maxeff (read @t) (alloc @t)) (k-ids k-ids) (listof string @t))
    (lambda (ts path) (if (null? ts) nil (cons (k-show-on (car ts) path) (k-show-list (cdr ts) path)))))
  (k-show-parts (subr (maxeff (read @t) (alloc @t)) (k-parts k-ids) string)
    (lambda (ps path)
      (if (null? ps)
          ""
          (string-append (k-cat5 " (" (symbol->string (extract (car ps) 1)) " " (k-show-on (extract (car ps) 2) path) ")")
                         (k-show-parts (cdr ps) path)))))
  (k-show-body (subr (maxeff (read @t) (alloc @t)) (int k-ids) string)
    (lambda (t path)
      (if (k-has-id? path t)
          "…"
          (let ((p (the k-ids (cons t path))))
            (tagcase (k-get t)
              (ty-base (s) (symbol->string s))
              (ty-void () "void")
              (ty-var (v) (symbol->string (k-dvar-name v)))
              (ty-link (x) "?")
              (ty-subr (e ps r)
                (k-cat5 (k-cat3 "(subr " (k-show-effect e) " (") (k-join (k-show-list ps p) " ") ") " (k-show-on r p) ")"))
              (ty-poly (bs body) (k-cat5 "(poly (" (k-join (k-show-binders bs) " ") ") " (k-show-on body p) ")"))
              (ty-ref (a r) (k-cat5 "(ref " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-product (ps) (k-cat3 "(productof" (k-show-parts ps p) ")"))
              (ty-sum (ps) (k-cat3 "(sumof" (k-show-parts ps p) ")"))
              (ty-array (a r) (k-cat5 "(arrayof " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-icell (a r) (k-cat5 "(icell " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-pair (a b r)
                (if (= (k-resolve b) t)
                    (k-cat5 "(listof " (k-show-on a p) " " (k-region-show r) ")")
                    (k-cat5 (k-cat3 "(pairof " (k-show-on a p) " ") (k-show-on b p) " " (k-region-show r) ")")))
              (ty-tag (a h e r)
                (k-cat5 (k-cat4 "(prompt-tag " (k-show-on a p) " " (k-show-on h p)) " " (k-show-effect e) " "
                        (string-append (k-region-show r) ")")))
              (ty-comp (a h e r)
                (k-cat5 (k-cat4 "(composable " (k-show-on a p) " " (k-show-on h p)) " " (k-show-effect e) " "
                        (string-append (k-region-show r) ")")))
              (ty-markkey (a r) (k-cat5 "(mark-key " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-bloblet (fs z r)
                (k-cat5 (if z "(bloblet (frozen" "(bloblet (fields") (if (null? fs) "" " ") (k-join (k-show-list fs p) " ")
                        ") " (string-append (k-region-show r) ")")))))))))

;; A type. One `define-type` named prints as its name; any other recursive
;; type as far as its first repetition, shown as `…`.
(define k-show-ty (subr (maxeff (read @t) (alloc @t)) (int) string)
  (lambda (t) (k-show-on t nil)))

;;; ------------------------------------------------------------ reading syntax

(define k-sfail (subr checks (string syn) void)
  (lambda (m s) (k-fail m (syn-start s) (syn-end s))))
(define k-items (subr checks (syn string) (listof syn @s))
  (lambda (s what)
    (tagcase s (lst (items d a b) items) (else x (k-sfail (string-append what ": expected a list") s)))))
(define k-head (subr (read @s) ((listof syn @s)) string)
  (lambda (items) (if (null? items) "" (syn-name (car items)))))
(define k-name-of (subr checks (syn string) symbol)
  (lambda (s what) (if (syn-symbol? s) (string->symbol (syn-name s)) (k-sfail what s))))
(define k-at-name? (subr pure (string) bool)
  (lambda (n) (and (> (string-length n) 0) (string=? (substring n 0 1) "@"))))
(define k-nil-syn? (subr (read @s) (syn) bool)
  (lambda (s) (tagcase s (lst (items d a b) (null? items)) (else x #f))))
;; The items of a list that may be written `()`.
(define k-items-or-nil (subr checks (syn string) (listof syn @s))
  (lambda (s what) (if (k-nil-syn? s) nil (k-items s what))))

(define k-parse-kind (subr checks (syn) int)
  (lambda (s)
    (let ((n (if (syn-symbol? s) (syn-name s) "")))
      (cond ((string=? n "region") 0) ((string=? n "effect") 1) ((string=? n "type") 2)
            (else (k-sfail "a kind is `region`, `effect` or `type`" s))))))
(define k-binders-each (subr checks ((listof syn @s)) k-binders)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((pair (k-items (car bs) "a binder")))
          (if (= (k-length pair) 2)
              (let* ((name (k-name-of (car pair) "a binder's name"))
                     (kind (k-parse-kind (k-nth pair 1)))
                     (v (k-new-dvar name))
                     (pushed (k-push-desc name (ds-var v kind)))
                     (rest (k-binders-each (cdr bs))))
                (cons (product (1 v) (2 kind)) rest))
              (k-sfail "a binder is `(name kind)`" (car bs)))))))

;; `((name kind) …)`, binding each name for the rest of the reading.
(define k-parse-binders (subr checks (syn) k-binders)
  (lambda (s) (k-binders-each (k-items s "binders"))))

;; The region `@name` stands for: the program's own, if `private-regions`
;; declared it, and otherwise the constant of that name.
(define k-region-constant (subr (maxeff (read @t) (alloc @t)) (symbol) k-region)
  (lambda (sym)
    (let ((d (k-lookup-desc sym)))
      (if (null? d) (r-const sym) (tagcase (car d) (ds-private (r) r) (else x (r-const sym)))))))

(define k-parse-region (subr checks (syn) k-region)
  (lambda (s)
    (if (not (syn-symbol? s))
        (k-sfail "expected a region" s)
        (let* ((n (syn-name s)) (sym (string->symbol n)))
          (if (k-at-name? n)
              (k-region-constant sym)
              (let ((d (k-lookup-desc sym)) (no (string-append (k-quote n) " is not a region")))
                (if (null? d)
                    (k-sfail no s)
                    (tagcase (car d)
                      (ds-var (v k) (if (= k 0) (r-var v) (k-sfail no s)))
                      (ds-region (r) r)
                      (else x (k-sfail no s))))))))))

(define-rec
  (k-effects (subr checks ((listof syn @s)) k-eff)
    (lambda (xs) (if (null? xs) nil (let* ((e (k-parse-effect (car xs))) (rest (k-effects (cdr xs)))) (k-union e rest)))))
  (k-parse-effect (subr checks (syn) k-eff)
    (lambda (s)
      (if (syn-symbol? s)
          (let ((n (syn-name s)))
            (if (string=? n "pure")
                nil
                (let ((d (k-lookup-desc (string->symbol n))) (no (string-append (k-quote n) " is not an effect")))
                  (if (null? d)
                      (k-sfail no s)
                      (tagcase (car d)
                        (ds-var (v k) (if (= k 1) (k-one (a-var v)) (k-sfail no s)))
                        (ds-eff (e) e)
                        (else x (k-sfail no s)))))))
          (let* ((items (k-items s "an effect")) (head (k-head items)))
            (cond ((string=? head "maxeff") (k-effects (cdr items)))
                  ((or (string=? head "read") (string=? head "write") (string=? head "alloc")
                       (string=? head "goto") (string=? head "comefrom") (string=? head "await"))
                   (if (= (k-length items) 2)
                       (let ((r (k-parse-region (k-nth items 1))))
                         (k-one (cond ((string=? head "read") (a-read r)) ((string=? head "write") (a-write r))
                                      ((string=? head "alloc") (a-alloc r)) ((string=? head "goto") (a-goto r))
                                      ((string=? head "await") (a-await r))
                                      (else (a-comefrom r)))))
                       (k-sfail (k-cat3 "`(" head " region)`") s)))
                  (else (k-sfail "expected an effect" s))))))))

;; A label or tag: a name, or a positive integer, which is its digits.
(define k-label (subr checks (syn) symbol)
  (lambda (s)
    (cond ((syn-symbol? s) (string->symbol (syn-name s)))
          ((> (syn-int s) 0) (string->symbol (int->string (syn-int s))))
          (else (k-sfail "a label is a name or a positive integer" s)))))
(define k-has-label? (subr (read @t) (k-parts symbol) bool)
  (lambda (ps l) (cond ((null? ps) #f) ((symbol=? (extract (car ps) 1) l) #t) (else (k-has-label? (cdr ps) l)))))

(define k-shape (subr checks (bool string syn) unit)
  (lambda (ok shape s) (if ok #u (k-sfail shape s))))
(define-type k-slots (listof (pairof int syn @t) @t))
(define k-dletrec-slots (subr checks ((listof syn @s)) k-slots)
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((pair (k-items (car bs) "a dletrec binding")))
          (if (= (k-length pair) 2)
              (let* ((name (k-name-of (car pair) "a name"))
                     (slot (k-slot))
                     (pushed (k-push-desc name (ds-rec slot)))
                     (rest (k-dletrec-slots (cdr bs))))
                (cons (cons slot (k-nth pair 1)) rest))
              (k-sfail "a dletrec binding is `(name type)`" (car bs)))))))
(define k-grounded-from (subr checks (int k-ids int int) unit)
  (lambda (id seen a b)
    (tagcase (k-raw id)
      (ty-link (to)
        (cond ((null? to) #u)
              ((k-has-id? seen id) (k-fail "a recursive type must be built from a constructor, not only from names" a b))
              (else (k-grounded-from (car to) (cons id seen) a b))))
      (else x #u))))

;; A name defined as another name, round a loop, describes nothing.
(define k-grounded (subr checks (int int int) unit)
  (lambda (slot a b) (k-grounded-from slot nil a b)))
(define k-dletrec-grounded (subr checks (k-slots syn) unit)
  (lambda (ss s)
    (if (null? ss) #u (begin (k-grounded (car (car ss)) (syn-start s) (syn-end s)) (k-dletrec-grounded (cdr ss) s)))))
(define k-family-params (subr checks ((listof syn @s)) (listof (productof (1 symbol) (2 int)) @t))
  (lambda (ps)
    (if (null? ps)
        nil
        (let ((pair (k-items (car ps) "`(name kind)`")))
          (if (= (k-length pair) 2)
              (let* ((n (k-name-of (car pair) "a parameter's name")) (k (k-parse-kind (k-nth pair 1)))
                     (rest (k-family-params (cdr ps))))
                (cons (product (1 n) (2 k)) rest))
              (k-sfail "a parameter is `(name kind)`" (car ps)))))))

;; `(define-type (name (param kind) …) type)`: nothing is read until it is
;; used.
(define k-define-family (subr checks (symbol (listof syn @s) syn) unit)
  (lambda (name params body) (k-push-desc name (ds-abbrev (k-family-params params) body))))
;; Push a scope's entries, the first first.
(define k-push-all (subr kstate (k-scope) unit)
  (lambda (bs) (if (null? bs) #u (begin (k-push-desc (car (car bs)) (cdr (car bs))) (k-push-all (cdr bs))))))

(define-rec
  (k-parse-types (subr checks ((listof syn @s)) k-ids)
    (lambda (xs) (if (null? xs) nil (let* ((t (k-parse-type (car xs))) (rest (k-parse-types (cdr xs)))) (cons t rest)))))
  (k-parse-parts (subr checks ((listof syn @s) k-parts) k-parts)
    (lambda (ps done)
      (if (null? ps)
          (reverse done)
          (let ((pair (k-items (car ps) "`(label type)`")))
            (if (= (k-length pair) 2)
                (let ((l (k-label (car pair))))
                  (if (k-has-label? done l)
                      (k-sfail (string-append (k-quote (symbol->string l)) " appears twice") (car ps))
                      (let ((t (k-parse-type (k-nth pair 1))))
                        (k-parse-parts (cdr ps) (cons (product (1 l) (2 t)) done)))))
                (k-sfail "`(label type)`" (car ps)))))))
  (k-parse-type (subr checks (syn) int)
    (lambda (s)
      (if (syn-symbol? s)
          (let* ((n (syn-name s)) (sym (string->symbol n)) (base (k-find (get k-base) sym)))
            (cond ((string=? n "void") k-void)
                  ((>= base 0) base)
                  (else
                   (let ((d (k-lookup-desc sym)) (no (string-append (k-quote n) " is not a type")))
                     (if (null? d)
                         (k-sfail no s)
                         (tagcase (car d)
                           (ds-var (v k) (if (= k 2) (k-ty-new (ty-var v)) (k-sfail no s)))
                           (ds-rec (t) t)
                           (else x (k-sfail no s))))))))
          (let* ((items (k-items s "a type"))
                 (hd (if (null? items) "" (syn-name (car items))))
                 (abbrev (if (string=? hd "") (the (listof k-ds @t) nil) (k-lookup-desc (string->symbol hd))))
                 (n (k-length items)))
            (if (and (not (null? abbrev)) (tagcase (car abbrev) (ds-abbrev (ps body) #t) (else x #f)))
                (tagcase (car abbrev)
                  (ds-abbrev (ps body) (k-expand-abbrev s (string->symbol hd) ps body (cdr items)))
                  (else x (k-sfail "an abbreviation" s)))
                (cond
                  ((string=? hd "subr")
                   (begin
                     (k-shape (= n 4) "`(subr effect (param …) result)`" s)
                     (let* ((e (k-parse-effect (k-nth items 1)))
                            (ps (k-parse-types (k-items-or-nil (k-nth items 2) "parameter types")))
                            (r (k-parse-type (k-nth items 3))))
                       (k-ty-new (ty-subr e ps r)))))
                  ((string=? hd "poly")
                   (begin
                     (k-shape (= n 3) "`(poly ((name kind) …) type)`" s)
                     (let* ((saved (get k-dscope))
                            (bs (k-parse-binders (k-nth items 1)))
                            (body (k-parse-type (k-nth items 2))))
                       (begin (set k-dscope saved) (k-ty-new (ty-poly bs body))))))
                  ((string=? hd "ref")
                   (begin
                     (k-shape (= n 3) "`(ref type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                       (k-ty-new (ty-ref t r)))))
                  ((string=? hd "pairof")
                   (begin
                     (k-shape (= n 4) "`(pairof type type region)`" s)
                     (let* ((a (k-parse-type (k-nth items 1))) (b (k-parse-type (k-nth items 2)))
                            (r (k-parse-region (k-nth items 3))))
                       (k-ty-new (ty-pair a b r)))))
                  ((string=? hd "dletrec") (k-parse-dletrec s items))
                  ((string=? hd "listof")
                   (begin
                     (k-shape (= n 3) "`(listof type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2)))
                            (slot (k-slot)) (pair (k-ty-new (ty-pair t slot r))))
                       (begin (k-set-link slot pair) slot))))
                  ((string=? hd "prompt-tag")
                   (begin
                     (k-shape (= n 5) "`(prompt-tag answer payload effect region)`" s)
                     (let* ((a (k-parse-type (k-nth items 1))) (h (k-parse-type (k-nth items 2)))
                            (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
                       (k-ty-new (ty-tag a h e r)))))
                  ((string=? hd "composable")
                   (begin
                     (k-shape (= n 5) "`(composable argument answer effect region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (a (k-parse-type (k-nth items 2)))
                            (e (k-parse-effect (k-nth items 3))) (r (k-parse-region (k-nth items 4))))
                       (k-ty-new (ty-comp t a e r)))))
                  ((string=? hd "bloblet")
                   (begin
                     (k-shape (= n 3) "`(bloblet (fields type …) region)`, or `(frozen type …)`" s)
                     (let* ((fields (k-nth items 1))
                            (parts (k-items fields "`(fields type …)`"))
                            (which (k-head parts)))
                       (if (or (string=? which "fields") (string=? which "frozen"))
                           (let* ((fs (k-parse-types (cdr parts))) (r (k-parse-region (k-nth items 2))))
                             (k-ty-new (ty-bloblet fs (string=? which "frozen") r)))
                           (k-sfail "`(fields type …)` or `(frozen type …)`" fields)))))
                  ((string=? hd "productof") (k-ty-new (ty-product (k-parse-parts (cdr items) nil))))
                  ((string=? hd "sumof") (k-ty-new (ty-sum (k-parse-parts (cdr items) nil))))
                  ((string=? hd "arrayof")
                   (begin
                     (k-shape (= n 3) "`(arrayof type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                       (k-ty-new (ty-array t r)))))
                  ((string=? hd "icell")
                   (begin
                     (k-shape (= n 3) "`(icell type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                       (k-ty-new (ty-icell t r)))))
                  ((string=? hd "mark-key")
                   (begin
                     (k-shape (= n 3) "`(mark-key type region)`" s)
                     (let* ((t (k-parse-type (k-nth items 1))) (r (k-parse-region (k-nth items 2))))
                       (k-ty-new (ty-markkey t r)))))
                  (else (k-sfail "expected a type" s))))))))
  ;; `(dletrec ((name type) …) type)`: each name gets a forwarding slot
  ;; before any body is read, so the bodies can refer to it and each other.
  (k-parse-dletrec (subr checks (syn (listof syn @s)) int)
    (lambda (s items)
      (begin
        (k-shape (= (k-length items) 3) "`(dletrec ((name type) …) type)`" s)
        (let* ((saved (get k-dscope))
               (slots (k-dletrec-slots (k-items (k-nth items 1) "dletrec bindings")))
               (filled (k-dletrec-fill slots))
               (grounded (k-dletrec-grounded slots s))
               (body (k-parse-type (k-nth items 2))))
          (begin (set k-dscope saved) body)))))
  (k-dletrec-fill (subr checks (k-slots) unit)
    (lambda (ss)
      (if (null? ss)
          #u
          (let ((t (k-parse-type (cdr (car ss)))))
            (begin (k-set-link (car (car ss)) t) (k-dletrec-fill (cdr ss)))))))
  ;; A use of a parametric abbreviation: its body, read with each parameter
  ;; bound to the description given for it.
  (k-expand-abbrev (subr checks (syn symbol (listof (productof (1 symbol) (2 int)) @t) syn (listof syn @s)) int)
    (lambda (s name ps body args)
      (cond
        ((not (= (k-length args) (k-length ps)))
         (k-sfail (k-cat5 (k-quote (symbol->string name)) " takes " (int->string (k-length ps)) " description(s), and has "
                          (int->string (k-length args)))
                  s))
        ((> (get k-expanding) 64)
         (k-sfail (string-append (k-quote (symbol->string name)) " expands without end: an abbreviation with parameters cannot mention itself") s))
        (else
         (let* ((bound (k-abbrev-args ps args))
                (saved (get k-dscope)))
           (begin
             (k-push-all bound)
             (set k-expanding (+ (get k-expanding) 1))
             (let ((t (k-parse-type body)))
               (begin (set k-expanding (- (get k-expanding) 1)) (set k-dscope saved) t))))))))
  (k-abbrev-args (subr checks ((listof (productof (1 symbol) (2 int)) @t) (listof syn @s)) k-scope)
    (lambda (ps args)
      (if (null? ps)
          nil
          (let* ((k (extract (car ps) 2))
                 (d (cond ((= k 2) (ds-rec (k-parse-type (car args))))
                          ((= k 0) (ds-region (k-parse-region (car args))))
                          (else (ds-eff (k-parse-effect (car args))))))
                 (rest (k-abbrev-args (cdr ps) (cdr args))))
            (cons (cons (extract (car ps) 1) d) rest))))))

;; `(define-type name type)`: `name` stands for the type from here on, and
;; may appear in its own definition.
(define k-define-type (subr checks (symbol syn int int) int)
  (lambda (name def a b)
    (let ((slot (k-slot)))
      (begin
        (k-push-desc name (ds-rec slot))
        (let ((t (k-parse-type def)))
          (begin (k-set-link slot t) (k-grounded slot a b) slot))))))

;; A `proj` argument: which kind it is shows in its shape, or, for a bare
;; name, in how the name is bound.
(define k-parse-d (subr checks (syn) k-desc)
  (lambda (s)
    (if (syn-symbol? s)
        (let* ((n (syn-name s)) (sym (string->symbol n)))
          (cond ((k-at-name? n) (dr (k-region-constant sym)))
                ((string=? n "pure") (de nil))
                (else
                 (let ((d (k-lookup-desc sym)))
                   (if (null? d)
                       (dt (k-parse-type s))
                       (tagcase (car d)
                         (ds-var (v k)
                           (cond ((= k 0) (dr (r-var v))) ((= k 1) (de (k-one (a-var v)))) (else (dt (k-parse-type s)))))
                         (ds-eff (e) (de e))
                         (else x (dt (k-parse-type s)))))))))
        (let ((hd (k-head (k-items s "a description"))))
          (if (or (string=? hd "read") (string=? hd "write") (string=? hd "alloc") (string=? hd "goto")
                  (string=? hd "comefrom") (string=? hd "await") (string=? hd "maxeff"))
              (de (k-parse-effect s))
              (dt (k-parse-type s)))))))

;;; ------------------------------------------------------------ resolving
;;; The parser's trees to `kx`, reading descriptions where the Rust parser
;;; does.

(define k-start (subr pure (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b) a) (x-const (t a b) a) (x-lambda (ps e a b) a) (x-app (f xs a b) a)
      (x-plambda (bs e a b) a) (x-proj (e ds a b) a) (x-if (p c d a b) a) (x-letrec (bs e a b) a)
      (x-let (bs e a b) a) (x-begin (xs a b) a) (x-prompt (t e h a b) a) (x-the (t e a b) a)
      (x-bloblet (o i xs a b) a) (x-product (fs a b) a) (x-extract (e l a b) a) (x-sum (l e a b) a)
      (x-tagcase (e arms els a b) a) (x-letregion (r e a b) a))))
(define k-end (subr pure (kx) int)
  (lambda (x)
    (tagcase x
      (x-var (s a b) b) (x-const (t a b) b) (x-lambda (ps e a b) b) (x-app (f xs a b) b)
      (x-plambda (bs e a b) b) (x-proj (e ds a b) b) (x-if (p c d a b) b) (x-letrec (bs e a b) b)
      (x-let (bs e a b) b) (x-begin (xs a b) b) (x-prompt (t e h a b) b) (x-the (t e a b) b)
      (x-bloblet (o i xs a b) b) (x-product (fs a b) b) (x-extract (e l a b) b) (x-sum (l e a b) b)
      (x-tagcase (e arms els a b) b) (x-letregion (r e a b) b))))
(define k-same-span? (subr pure (kx int int) bool)
  (lambda (x a b) (and (= (k-start x) a) (= (k-end x) b))))

(define k-resolve-params (subr checks ((listof (productof (1 symbol) (2 syns-a)) @a)) (listof (productof (1 symbol) (2 k-ids)) @t))
  (lambda (ps)
    (if (null? ps)
        nil
        (let* ((ty (extract (car ps) 2))
               (t (if (null? ty) (the k-ids nil) (the k-ids (cons (k-parse-type (car ty)) nil))))
               (rest (k-resolve-params (cdr ps))))
          (cons (product (1 (extract (car ps) 1)) (2 t)) rest)))))
(define k-resolve-descs (subr checks (syns-a) (listof k-desc @t))
  (lambda (ds) (if (null? ds) nil (let* ((d (k-parse-d (car ds))) (rest (k-resolve-descs (cdr ds)))) (cons d rest)))))
(define k-copy-names (subr (maxeff (read @a) (alloc @t)) (names) k-names)
  (lambda (ns) (if (null? ns) nil (cons (car ns) (k-copy-names (cdr ns))))))

;; Where a parser's tree starts and ends.
(define exp-start (subr pure (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b) a) (e-int (n a b) a) (e-bool (v a b) a) (e-str (v a b) a) (e-char (v a b) a) (e-sym (v a b) a)
      (e-unit (a b) a) (e-lambda (ps x a b) a) (e-app (f xs a b) a) (e-plambda (bs x a b) a) (e-proj (x ds a b) a)
      (e-if (p c d a b) a) (e-letrec (bs x a b) a) (e-let (bs x a b) a) (e-begin (xs a b) a) (e-prompt (t x h a b) a)
      (e-the (t x a b) a) (e-bloblet (o i xs a b) a) (e-product (fs a b) a) (e-extract (x l a b) a) (e-sum (l x a b) a)
      (e-tagcase (x arms els a b) a) (e-letregion (r x a b) a))))
(define exp-end (subr pure (exp) int)
  (lambda (e)
    (tagcase e
      (e-var (s a b) b) (e-int (n a b) b) (e-bool (v a b) b) (e-str (v a b) b) (e-char (v a b) b) (e-sym (v a b) b)
      (e-unit (a b) b) (e-lambda (ps x a b) b) (e-app (f xs a b) b) (e-plambda (bs x a b) b) (e-proj (x ds a b) b)
      (e-if (p c d a b) b) (e-letrec (bs x a b) b) (e-let (bs x a b) b) (e-begin (xs a b) b) (e-prompt (t x h a b) b)
      (e-the (t x a b) b) (e-bloblet (o i xs a b) b) (e-product (fs a b) b) (e-extract (x l a b) b) (e-sum (l x a b) b)
      (e-tagcase (x arms els a b) b) (e-letregion (r x a b) b))))

(define-rec
  (k-resolve-all (subr checks ((listof exp @a)) kxs)
    (lambda (es) (if (null? es) nil (let* ((x (k-resolve-exp (car es))) (rest (k-resolve-all (cdr es)))) (cons x rest)))))
  (k-resolve-exp (subr checks (exp) kx)
    (lambda (e)
      (tagcase e
        (e-var (s a b) (x-var s a b))
        (e-int (n a b) (x-const k-int a b))
        (e-bool (v a b) (x-const k-bool a b))
        (e-str (v a b) (x-const k-string a b))
        (e-char (v a b) (x-const k-char a b))
        (e-sym (v a b) (x-const k-symbol a b))
        (e-unit (a b) (x-const k-unit a b))
        (e-lambda (ps body a b)
          (let* ((params (k-resolve-params ps)) (x (k-resolve-exp body))) (x-lambda params x a b)))
        (e-app (f args a b)
          (let* ((fx (k-resolve-exp f)) (xs (k-resolve-all args))) (x-app fx xs a b)))
        (e-plambda (binders body a b)
          (let* ((saved (get k-dscope))
                 (bs (k-parse-binders binders))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (x-plambda bs x a b))))
        (e-letregion (name body a b)
          (let* ((saved (get k-dscope))
                 (v (k-new-dvar name))
                 (pushed (k-push-desc name (ds-var v 0)))
                 (x (k-resolve-exp body)))
            (begin (set k-dscope saved) (x-letregion v x a b))))
        (e-proj (body ds a b)
          (let* ((x (k-resolve-exp body)) (descs (k-resolve-descs ds))) (x-proj x descs a b)))
        (e-if (p c d a b)
          (let* ((px (k-resolve-exp p)) (cx (k-resolve-exp c)) (dx (k-resolve-exp d))) (x-if px cx dx a b)))
        (e-letrec (bs body a b)
          (let* ((rbs (k-resolve-letrec bs)) (x (k-resolve-exp body))) (x-letrec rbs x a b)))
        (e-let (bs body a b)
          (let* ((rbs (k-resolve-let bs)) (x (k-resolve-exp body))) (x-let rbs x a b)))
        (e-begin (es a b) (x-begin (k-resolve-all es) a b))
        (e-prompt (t body h a b)
          (let* ((tx (k-resolve-exp t)) (bx (k-resolve-exp body)) (hx (k-resolve-exp h))) (x-prompt tx bx hx a b)))
        (e-the (ty body a b)
          (let* ((t (k-parse-type ty)) (x (k-resolve-exp body))) (x-the t x a b)))
        (e-bloblet (op i args a b) (x-bloblet op i (k-resolve-all args) a b))
        (e-product (fs a b) (x-product (k-resolve-fields fs nil a b) a b))
        (e-extract (body l a b) (x-extract (k-resolve-exp body) l a b))
        (e-sum (l body a b) (x-sum l (k-resolve-exp body) a b))
        (e-tagcase (s arms els a b)
          (let* ((sx (k-resolve-exp s)) (rarms (k-resolve-arms arms nil)) (rels (k-resolve-else els)))
            (x-tagcase sx rarms rels a b))))))
  (k-resolve-letrec (subr checks ((listof (productof (1 symbol) (2 syn) (3 exp)) @a)) (listof (productof (1 symbol) (2 int) (3 kx)) @t))
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((t (k-parse-type (extract (car bs) 2)))
                 (x (k-resolve-exp (extract (car bs) 3)))
                 (rest (k-resolve-letrec (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 t) (3 x)) rest)))))
  (k-resolve-let (subr checks ((listof (productof (1 symbol) (2 exp)) @a)) (listof (productof (1 symbol) (2 kx)) @t))
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((x (k-resolve-exp (extract (car bs) 2))) (rest (k-resolve-let (cdr bs))))
            (cons (product (1 (extract (car bs) 1)) (2 x)) rest)))))
  (k-resolve-fields (subr checks ((listof (productof (1 symbol) (2 exp)) @a) k-names int int) (listof (productof (1 symbol) (2 kx)) @t))
    (lambda (fs seen a b)
      (if (null? fs)
          nil
          (let ((l (extract (car fs) 1)))
            (if (k-has-name? seen l)
                (k-fail (string-append (k-quote (symbol->string l)) " appears twice") a b)
                (let* ((x (k-resolve-exp (extract (car fs) 2))) (rest (k-resolve-fields (cdr fs) (cons l seen) a b)))
                  (cons (product (1 l) (2 x)) rest)))))))
  (k-resolve-arms (subr checks ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) k-names)
                          (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) @t))
    (lambda (arms seen)
      (if (null? arms)
          nil
          (let* ((arm (car arms)) (tag (extract arm 1)))
            (if (k-has-name? seen tag)
                (k-fail (string-append (k-quote (symbol->string tag)) " has two arms")
                        (exp-start (extract arm 4)) (exp-end (extract arm 4)))
                (let* ((x (k-resolve-exp (extract arm 4))) (rest (k-resolve-arms (cdr arms) (cons tag seen))))
                  (cons (product (1 tag) (2 (extract arm 2)) (3 (k-copy-names (extract arm 3))) (4 x)) rest)))))))
  (k-resolve-else (subr checks ((listof (productof (1 symbol) (2 exp)) @a)) (listof (productof (1 symbol) (2 kx)) @t))
    (lambda (els)
      (if (null? els) nil (cons (product (1 (extract (car els) 1)) (2 (k-resolve-exp (extract (car els) 2)))) nil)))))

;;; ------------------------------------------------------------ callables

;; What calling a value of type `t` does: its latent effect, parameters and
;; result, as none or one. A composable continuation runs the rest of its
;; prompt's body, with control effects on the tag's region.
(define-type k-callable (productof (1 k-eff) (2 k-ids) (3 int)))
(define k-as-subr (subr (maxeff (read @t) (alloc @t)) (int) (listof k-callable @t))
  (lambda (t)
    (tagcase (k-get t)
      (ty-subr (e ps r) (cons (product (1 e) (2 ps) (3 r)) nil))
      (ty-comp (arg answer e r)
        (cons (product (1 (k-insert (a-goto r) (k-insert (a-comefrom r) e))) (2 (the k-ids (cons arg nil))) (3 answer)) nil))
      (else x nil))))

;;; ------------------------------------------------------------ regions of types

(define-type k-regions (listof k-region @t))
(define k-has-region-in? (subr (read @t) (k-regions k-region) bool)
  (lambda (rs r) (cond ((null? rs) #f) ((k-region=? (car rs) r) #t) (else (k-has-region-in? (cdr rs) r)))))
(define k-add-region (subr (maxeff (read @t) (alloc @t)) (k-regions k-region) k-regions)
  (lambda (rs r) (if (k-has-region-in? rs r) rs (cons r rs))))
(define k-add-eff-regions (subr (maxeff (read @t) (alloc @t)) (k-regions k-eff) k-regions)
  (lambda (rs e)
    (cond ((null? e) rs)
          ((k-has-region? (car e)) (k-add-eff-regions (k-add-region rs (k-atom-region (car e))) (cdr e)))
          (else (k-add-eff-regions rs (cdr e))))))

;; Every region mentioned in type `t`, following recursive types once.
;; Kept once found, by type: a type does not change once built.
(define k-regions-memo (ref (arrayof (listof k-regions @t) @t) @t) (new (make-array 512 nil)))

(define k-reset (subr kstate () unit)
  (lambda ()
    (begin
      (set k-extracts nil)
      (set k-ntys 0) (set k-dvars nil) (set k-ndvars 0) (set k-env (make-table symbol-hash symbol=?)) (set k-trail nil) (set k-depth 0)
      (set k-regions-memo (make-array 512 nil)) (set k-dscope nil)
      (set k-fresh 0) (set k-base nil) (set k-expanding 0)
      (k-basic "int") (k-basic "bool") (k-basic "string") (k-basic "unit") (k-basic "char")
      (k-basic "datum") (k-basic "symbol") (k-basic "tword") (k-basic "wcell") (k-basic "wglobal")
      (k-ty-new (ty-void))
      #u)))
(define n-copy-memo (subr (maxeff (read @t) (write @t)) ((arrayof (listof k-regions @t) @t) (arrayof (listof k-regions @t) @t) int) unit)
  (lambda (from to i)
    (if (= i (array-length from)) #u (begin (array-set! to i (array-ref from i)) (n-copy-memo from to (+ i 1))))))
(define k-remember-regions (subr (maxeff (read @t) (write @t) (alloc @t)) (int k-regions) unit)
  (lambda (t rs)
    (begin
      (if (>= t (array-length (get k-regions-memo)))
          (let ((bigger (the (arrayof (listof k-regions @t) @t) (make-array (* 2 (array-length (get k-tys))) nil))))
            (begin (n-copy-memo (get k-regions-memo) bigger 0) (set k-regions-memo bigger)))
          #u)
      (array-set! (get k-regions-memo) t (cons rs nil)))))

(define-rec
  (k-regions-walk (subr (maxeff (read @t) (write @t) (alloc @t)) (int int (ref k-regions @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #u
            (letrec ((add (subr (maxeff (read @t) (write @t) (alloc @t)) (k-region) unit)
                         (lambda (r) (set out (k-add-region (get out) r))))
                  (walk (subr (maxeff (read @t) (write @t) (alloc @t)) (int) unit) (lambda (x) (k-regions-walk x seen out)))
                  (walks (subr (maxeff (read @t) (write @t) (alloc @t)) (k-ids) unit) (lambda (xs) (k-regions-walks xs seen out))))
              (begin
                (tagcase (k-get t)
                  (ty-subr (e ps r) (begin (set out (k-add-eff-regions (get out) e)) (walks ps) (walk r)))
                  (ty-poly (bs body) (walk body))
                  (ty-ref (a r) (begin (add r) (walk a)))
                  (ty-array (a r) (begin (add r) (walk a)))
                  (ty-icell (a r) (begin (add r) (walk a)))
                  (ty-pair (a b r) (begin (add r) (walk a) (walk b)))
                  (ty-tag (a h e r) (begin (add r) (set out (k-add-eff-regions (get out) e)) (walk a) (walk h)))
                  (ty-comp (b a e r) (begin (add r) (set out (k-add-eff-regions (get out) e)) (walk a) (walk b)))
                  (ty-markkey (a r) (begin (add r) (walk a)))
                  (ty-bloblet (fs z r) (begin (add r) (walks fs)))
                  (ty-product (ps) (k-regions-parts ps seen out))
                  (ty-sum (ps) (k-regions-parts ps seen out))
                  (else x #u))))))))
  (k-regions-walks (subr (maxeff (read @t) (write @t) (alloc @t)) (k-ids int (ref k-regions @t)) unit)
    (lambda (ts seen out) (if (null? ts) #u (begin (k-regions-walk (car ts) seen out) (k-regions-walks (cdr ts) seen out)))))
  (k-regions-parts (subr (maxeff (read @t) (write @t) (alloc @t)) (k-parts int (ref k-regions @t)) unit)
    (lambda (ps seen out)
      (if (null? ps) #u (begin (k-regions-walk (extract (car ps) 2) seen out) (k-regions-parts (cdr ps) seen out))))))
(define k-regions-in (subr (maxeff (read @t) (write @t) (alloc @t)) (int) k-regions)
  (lambda (t)
    (let* ((t (k-resolve t)) (memo (get k-regions-memo)))
      (if (and (< t (array-length memo)) (not (null? (array-ref memo t))))
          (car (array-ref memo t))
          (let ((out (the (ref k-regions @t) (new nil))))
            (begin
              (k-regions-walk t (k-new-epoch) out)
              (k-remember-regions t (get out))
              (get out)))))))
(define k-note (subr (maxeff (read @t) (alloc @t)) (symbol k-names k-names) k-names)
  (lambda (s bound out) (if (or (k-has-name? bound s) (k-has-name? out s)) out (cons s out))))
(define k-names-onto (subr (maxeff (read @t) (alloc @t)) (k-names k-names) k-names)
  (lambda (ns bound) (if (null? ns) bound (k-names-onto (cdr ns) (cons (car ns) bound)))))
(define k-param-names (subr (maxeff (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 k-ids)) @t) k-names) k-names)
  (lambda (ps bound) (if (null? ps) bound (k-param-names (cdr ps) (cons (extract (car ps) 1) bound)))))
(define k-letrec-names (subr (maxeff (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 int) (3 kx)) @t) k-names) k-names)
  (lambda (bs bound) (if (null? bs) bound (k-letrec-names (cdr bs) (cons (extract (car bs) 1) bound)))))
(define k-let-names (subr (maxeff (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 kx)) @t) k-names) k-names)
  (lambda (bs bound) (if (null? bs) bound (k-let-names (cdr bs) (cons (extract (car bs) 1) bound)))))

(define-rec
  (k-free-list (subr (maxeff (read @t) (alloc @t)) (kxs k-names k-names) k-names)
    (lambda (xs bound out) (if (null? xs) out (k-free-list (cdr xs) bound (k-free-into (car xs) bound out)))))
  (k-free-into (subr (maxeff (read @t) (alloc @t)) (kx k-names k-names) k-names)
    (lambda (x bound out)
      (tagcase x
        (x-var (s a b) (k-note s bound out))
        (x-const (t a b) out)
        (x-lambda (ps body a b) (k-free-into body (k-param-names ps bound) out))
        (x-app (f args a b) (k-free-list args bound (k-free-into f bound out)))
        (x-plambda (bs body a b) (k-free-into body bound out))
        (x-letregion (r body a b) (k-free-into body bound out))
        (x-proj (body ds a b) (k-free-into body bound out))
        (x-if (p c d a b) (k-free-into d bound (k-free-into c bound (k-free-into p bound out))))
        (x-letrec (bs body a b)
          (let ((inner (k-letrec-names bs bound)))
            (k-free-into body inner (k-free-letrec bs inner out))))
        (x-let (bs body a b) (k-free-into body (k-let-names bs bound) (k-free-let bs bound out)))
        (x-begin (xs a b) (k-free-list xs bound out))
        (x-prompt (t body h a b) (k-free-into h bound (k-free-into body bound (k-free-into t bound out))))
        (x-the (t body a b) (k-free-into body bound out))
        (x-bloblet (o i xs a b) (k-free-list xs bound out))
        (x-product (fs a b) (k-free-fields fs bound out))
        (x-extract (body l a b) (k-free-into body bound out))
        (x-sum (l body a b) (k-free-into body bound out))
        (x-tagcase (s arms els a b)
          (let ((o (k-free-arms arms bound (k-free-into s bound out))))
            (if (null? els) o (k-free-into (extract (car els) 2) (cons (extract (car els) 1) bound) o)))))))
  (k-free-letrec (subr (maxeff (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 int) (3 kx)) @t) k-names k-names) k-names)
    (lambda (bs bound out) (if (null? bs) out (k-free-letrec (cdr bs) bound (k-free-into (extract (car bs) 3) bound out)))))
  (k-free-let (subr (maxeff (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 kx)) @t) k-names k-names) k-names)
    (lambda (bs bound out) (if (null? bs) out (k-free-let (cdr bs) bound (k-free-into (extract (car bs) 2) bound out)))))
  (k-free-fields (subr (maxeff (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 kx)) @t) k-names k-names) k-names)
    (lambda (fs bound out) (if (null? fs) out (k-free-fields (cdr fs) bound (k-free-into (extract (car fs) 2) bound out)))))
  (k-free-arms (subr (maxeff (read @t) (alloc @t))
                        ((listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) @t) k-names k-names) k-names)
    (lambda (arms bound out)
      (if (null? arms)
          out
          (k-free-arms (cdr arms) bound
                       (k-free-into (extract (car arms) 4) (k-names-onto (extract (car arms) 3) bound) out))))))

;;; ------------------------------------------------------------ free variables

(define k-free-vars (subr (maxeff (read @t) (alloc @t)) (kx) k-names)
  (lambda (x) (k-free-into x nil nil)))
(define k-union-regions (subr (maxeff (read @t) (alloc @t)) (k-regions k-regions) k-regions)
  (lambda (xs ys) (if (null? ys) xs (k-union-regions (k-add-region xs (car ys)) (cdr ys)))))

;;; ------------------------------------------------------------ masking
;;; What cannot be observed outside `x`, whose type is `result`, is removed:
;;; everything on a region that no free variable's type mentions, except
;;; that `alloc`, `goto` and `comefrom` on a region the result mentions stay
;;; (ranks 2 to 4; `await`, like `read`, does not).

(define k-visible (subr (maxeff (read @t) (write @t) (alloc @t)) (k-names k-regions) k-regions)
  (lambda (vs out)
    (if (null? vs)
        out
        (let ((t (k-lookup (car vs))))
          (k-visible (cdr vs) (if (< t 0) out (k-union-regions out (k-regions-in t))))))))
(define k-keep (subr (maxeff (read @t) (alloc @t)) (k-eff k-regions k-regions) k-eff)
  (lambda (e visible in-result)
    (if (null? e)
        nil
        (let* ((a (car e)) (r (k-atom-region a)) (rest (k-keep (cdr e) visible in-result)))
          (cond ((not (k-has-region? a)) (cons a rest))
                ((k-has-region-in? visible r) (cons a rest))
                ((and (k-has-region-in? in-result r) (and (> (k-atom-rank a) 1) (< (k-atom-rank a) 5))) (cons a rest))
                (else rest))))))

(define k-mask (subr (maxeff (read @t) (write @t) (alloc @t)) (kx k-eff int) k-eff)
  (lambda (x e result)
    (if (null? e)
        e
        (let* ((visible (k-visible (k-free-vars x) nil))
               (in-result (k-regions-in result)))
          (k-keep e visible in-result)))))

;;; ------------------------------------------------------------ substitution

(define k-map-find (subr (read @t) (k-map int) k-map)
  (lambda (m v) (cond ((null? m) nil) ((= (car (car m)) v) m) (else (k-map-find (cdr m) v)))))
(define k-subst-region (subr (read @t) (k-region k-map) k-region)
  (lambda (r m)
    (tagcase r
      (r-var (v) (let ((f (k-map-find m v))) (if (null? f) r (tagcase (cdr (car f)) (dr (x) x) (else y r)))))
      (else y r))))
(define k-subst-effect (subr (maxeff (read @t) (alloc @t)) (k-eff k-map) k-eff)
  (lambda (e m)
    (if (null? e)
        nil
        (let* ((a (car e))
               (rest (k-subst-effect (cdr e) m))
               (piece (tagcase a
                        (a-var (v)
                          (let ((f (k-map-find m v)))
                            (if (null? f) (k-one a) (tagcase (cdr (car f)) (de (x) x) (else y (k-one a))))))
                        (else y (k-one (k-atom-with a (k-subst-region (k-atom-region a) m)))))))
          (k-union piece rest)))))
(define k-memo-find (subr (read @t) ((listof (pairof int int @t) @t) int) int)
  (lambda (ms t) (cond ((null? ms) -1) ((= (car (car ms)) t) (cdr (car ms))) (else (k-memo-find (cdr ms) t)))))

(define-rec
  (k-subst-memo (subr kstate (int k-map (ref (listof (pairof int int @t) @t) @t)) int)
    (lambda (t m memo)
      (let* ((t (k-resolve t)) (done (k-memo-find (get memo) t)))
        (if (>= done 0)
            done
            (tagcase (k-get t)
              (ty-base (s) t)
              (ty-void () t)
              (ty-link (x) t)
              (ty-var (v) (let ((f (k-map-find m v))) (if (null? f) t (tagcase (cdr (car f)) (dt (x) x) (else y t)))))
              (else y
                (let ((slot (k-slot)))
                  (begin
                    (set memo (cons (cons t slot) (get memo)))
                    (letrec ((sub (subr kstate (int) int) (lambda (x) (k-subst-memo x m memo)))
                             (subs (subr kstate (k-ids) k-ids) (lambda (xs) (k-subst-list xs m memo)))
                             (reg (subr (read @t) (k-region) k-region) (lambda (r) (k-subst-region r m))))
                    (let* ((new-ty
                            (tagcase (k-get t)
                              (ty-subr (e ps r) (let* ((e2 (k-subst-effect e m)) (ps2 (subs ps)) (r2 (sub r))) (ty-subr e2 ps2 r2)))
                              (ty-poly (bs body) (ty-poly bs (sub body)))
                              (ty-ref (a r) (ty-ref (sub a) (reg r)))
                              (ty-array (a r) (ty-array (sub a) (reg r)))
                              (ty-icell (a r) (ty-icell (sub a) (reg r)))
                              (ty-pair (a b r) (let* ((a2 (sub a)) (b2 (sub b))) (ty-pair a2 b2 (reg r))))
                              (ty-tag (a h e r)
                                (let* ((a2 (sub a)) (h2 (sub h))) (ty-tag a2 h2 (k-subst-effect e m) (reg r))))
                              (ty-comp (b a e r)
                                (let* ((b2 (sub b)) (a2 (sub a))) (ty-comp b2 a2 (k-subst-effect e m) (reg r))))
                              (ty-markkey (a r) (ty-markkey (sub a) (reg r)))
                              (ty-product (ps) (ty-product (k-subst-parts ps m memo)))
                              (ty-sum (ps) (ty-sum (k-subst-parts ps m memo)))
                              (ty-bloblet (fs z r) (ty-bloblet (subs fs) z (reg r)))
                              (else z (k-get t))))
                           (id (k-ty-new new-ty)))
                      (begin (k-set-link slot id) slot)))))))))))
  (k-subst-list (subr kstate (k-ids k-map (ref (listof (pairof int int @t) @t) @t)) k-ids)
    (lambda (ts m memo)
      (if (null? ts) nil (let* ((x (k-subst-memo (car ts) m memo)) (rest (k-subst-list (cdr ts) m memo))) (cons x rest)))))
  (k-subst-parts (subr kstate (k-parts k-map (ref (listof (pairof int int @t) @t) @t)) k-parts)
    (lambda (ps m memo)
      (if (null? ps)
          nil
          (let* ((x (k-subst-memo (extract (car ps) 2) m memo)) (rest (k-subst-parts (cdr ps) m memo)))
            (cons (product (1 (extract (car ps) 1)) (2 x)) rest))))))

;; `t` with each binder in `m` replaced. Recursive types are copied as
;; cycles: each node gets its slot before its children are built.
(define k-subst (subr kstate (int k-map) int)
  (lambda (t m) (k-subst-memo t m (the (ref (listof (pairof int int @t) @t) @t) (new nil)))))

;; `b`'s binders renamed to `a`'s, for comparing under them.
(define k-rename (subr kstate (k-binders k-binders) k-map)
  (lambda (bs as)
    (if (null? bs)
        nil
        (let* ((vb (extract (car bs) 1)) (k (extract (car bs) 2)) (va (extract (car as) 1))
               (d (cond ((= k 0) (dr (r-var va))) ((= k 1) (de (k-one (a-var va)))) (else (dt (k-ty-new (ty-var va))))))
               (rest (k-rename (cdr bs) (cdr as))))
          (cons (cons vb d) rest)))))
(define k-same-kinds? (subr (read @t) (k-binders k-binders) bool)
  (lambda (xs ys)
    (cond ((null? xs) (null? ys))
          ((null? ys) #f)
          (else (and (= (extract (car xs) 2) (extract (car ys) 2)) (k-same-kinds? (cdr xs) (cdr ys)))))))

;;; ------------------------------------------------------------ subtyping
;;; `a ≤ b`. Recursive types are compared coinductively: a pair already
;;; being compared is assumed to hold.

(define-type k-trail (ref (listof (pairof int int @t) @t) @t))
(define k-trail-has? (subr (read @t) ((listof (pairof int int @t) @t) int int) bool)
  (lambda (ps a b) (cond ((null? ps) #f) ((and (= (car (car ps)) a) (= (cdr (car ps)) b)) #t) (else (k-trail-has? (cdr ps) a b)))))
(define k-bool=? (subr pure (bool bool) bool) (lambda (x y) (if x y (not y))))
(define k-part-find (subr (read @t) (k-parts symbol) int)
  (lambda (ps l) (cond ((null? ps) -1) ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2)) (else (k-part-find (cdr ps) l)))))

(define-rec
  (k-subs-contra (subr kstate (k-ids k-ids k-trail) bool)
    (lambda (xs ys trail)
      (cond ((null? xs) (null? ys)) ((null? ys) #f)
            (else (and (k-sub (car ys) (car xs) trail) (k-subs-contra (cdr xs) (cdr ys) trail))))))
  (k-inv (subr kstate (int int k-trail) bool)
    (lambda (x y trail) (and (k-sub x y trail) (k-sub y x trail))))
  (k-sub-callable (subr kstate (k-callable k-callable k-trail) bool)
    (lambda (ca cb trail)
      (and (= (k-length (extract ca 2)) (k-length (extract cb 2)))
           (k-within? (extract ca 1) (extract cb 1))
           (k-subs-contra (extract ca 2) (extract cb 2) trail)
           (k-sub (extract ca 3) (extract cb 3) trail))))
  (k-sub (subr kstate (int int k-trail) bool)
    (lambda (a b trail)
      (let ((a (k-resolve a)) (b (k-resolve b)))
        (cond
          ((= a b) #t)
          ((k-trail-has? (get trail) a b) #t)
          (else
           (begin
             (set trail (cons (cons a b) (get trail)))
             (let ((ta (k-get a)) (tb (k-get b)))
               (if (and (tagcase ta (ty-comp (x y e r) #t) (else z #f)) (tagcase tb (ty-subr (e ps r) #t) (else z #f)))
                   (k-sub-callable (car (k-as-subr a)) (car (k-as-subr b)) trail)
                   (tagcase ta
                     (ty-void () #t)
                     (ty-base (x) (tagcase tb (ty-base (y) (symbol=? x y)) (else z #f)))
                     (ty-var (x) (tagcase tb (ty-var (y) (= x y)) (else z #f)))
                     (ty-subr (e ps r) (tagcase tb (ty-subr (e2 ps2 r2) (k-sub-callable (car (k-as-subr a)) (car (k-as-subr b)) trail)) (else z #f)))
                     (ty-ref (x r) (tagcase tb (ty-ref (y s) (and (k-region=? r s) (k-inv x y trail))) (else z #f)))
                     (ty-array (x r) (tagcase tb (ty-array (y s) (and (k-region=? r s) (k-inv x y trail))) (else z #f)))
                     (ty-icell (x r) (tagcase tb (ty-icell (y s) (and (k-region=? r s) (k-inv x y trail))) (else z #f)))
                     (ty-pair (x1 x2 r)
                       (tagcase tb (ty-pair (y1 y2 s) (and (k-region=? r s) (k-inv x1 y1 trail) (k-inv x2 y2 trail))) (else z #f)))
                     (ty-tag (a1 h1 d1 r1)
                       (tagcase tb
                         (ty-tag (a2 h2 d2 r2) (and (k-region=? r1 r2) (k-eff=? d1 d2) (k-inv a1 a2 trail) (k-inv h1 h2 trail)))
                         (else z #f)))
                     (ty-comp (t1 a1 d1 r1)
                       (tagcase tb
                         (ty-comp (t2 a2 d2 r2)
                           (and (k-region=? r1 r2) (k-within? d1 d2) (k-sub t2 t1 trail) (k-sub a1 a2 trail)))
                         (else z #f)))
                     (ty-markkey (x r) (tagcase tb (ty-markkey (y s) (and (k-region=? r s) (k-inv x y trail))) (else z #f)))
                     (ty-bloblet (fa za r)
                       (tagcase tb
                         (ty-bloblet (fb zb s)
                           (and (k-region=? r s) (k-bool=? za zb) (= (k-length fa) (k-length fb)) (k-sub-fields fa fb za trail)))
                         (else z #f)))
                     (ty-product (pa)
                       (tagcase tb (ty-product (pb) (and (= (k-length pa) (k-length pb)) (k-sub-product pa pb trail))) (else z #f)))
                     (ty-sum (sa) (tagcase tb (ty-sum (sb) (k-sub-sum sa sb trail)) (else z #f)))
                     (ty-poly (ba xa)
                       (tagcase tb
                         (ty-poly (bb xb)
                           (and (= (k-length ba) (k-length bb)) (k-same-kinds? ba bb)
                                (k-sub xa (k-subst xb (k-rename bb ba)) trail)))
                         (else z #f)))
                     (else z #f))))))))))
  (k-sub-fields (subr kstate (k-ids k-ids bool k-trail) bool)
    (lambda (fa fb frozen trail)
      (cond ((null? fa) #t)
            (else (and (k-sub (car fa) (car fb) trail) (or frozen (k-sub (car fb) (car fa) trail))
                       (k-sub-fields (cdr fa) (cdr fb) frozen trail))))))
  (k-sub-product (subr kstate (k-parts k-parts k-trail) bool)
    (lambda (pa pb trail)
      (cond ((null? pa) #t)
            (else (and (symbol=? (extract (car pa) 1) (extract (car pb) 1))
                       (k-sub (extract (car pa) 2) (extract (car pb) 2) trail)
                       (k-sub-product (cdr pa) (cdr pb) trail))))))
  (k-sub-sum (subr kstate (k-parts k-parts k-trail) bool)
    (lambda (sa sb trail)
      (cond ((null? sa) #t)
            (else (let ((y (k-part-find sb (extract (car sa) 1))))
                    (and (>= y 0) (k-sub (extract (car sa) 2) y trail) (k-sub-sum (cdr sa) sb trail))))))))
(define k-subtype (subr kstate (int int) bool)
  (lambda (a b) (k-sub a b (the k-trail (new nil)))))
(define k-part-index (subr (read @t) (k-parts symbol int) int)
  (lambda (ps l i) (cond ((null? ps) -1) ((symbol=? (extract (car ps) 1) l) i) (else (k-part-index (cdr ps) l (+ i 1))))))

;;; ------------------------------------------------------------ errors

;; Run `f`, and if it fails at `a`..`b` with "a W is expected here, and
;; this is a G", fail instead with what `say` makes of W and G.
(define k-expected-split (subr pure (string) string)
  (lambda (m) (if (k-starts-at? m "a " 0 0) (substring m 2 (string-length m)) "")))
(define k-sep string " is expected here, and this is a ")

(define k-rewriting (subr checks ((subr checks () k-te) int int (subr checks (string string string) string)) k-te)
  (lambda (f a b say)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          (let* ((rest (k-expected-split m)) (at (k-find-sub rest k-sep 0)))
            (if (and (= ea a) (= eb b) (not (string=? rest "")) (>= at 0))
                (k-fail (say m (substring rest 0 at) (substring rest (+ at (string-length k-sep)) (string-length rest))) ea eb)
                (k-fail m ea eb))))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))
;; The same, for any error at `a`..`b`.
(define k-prefixing (subr checks ((subr checks () k-te) int int string) k-te)
  (lambda (f a b prefix)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (if (and (= ea a) (= eb b)) (k-fail (string-append prefix m) ea eb) (k-fail m ea eb)))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))

;; `got ≤ want`, or an error at `x` saying so.
(define k-expect (subr checks (kx int int) unit)
  (lambda (x got want)
    (if (k-subtype got want)
        #u
        (k-fail (k-cat4 "a " (k-show-ty want) " is expected here, and this is a " (k-show-ty got)) (k-start x) (k-end x)))))
;; Bind each, the first first.
(define k-bind-all (subr kstate (k-bindings) unit)
  (lambda (bs) (if (null? bs) #u (begin (k-bind (car (car bs)) (cdr (car bs))) (k-bind-all (cdr bs))))))
(define k-bind-letrec (subr kstate ((listof (productof (1 symbol) (2 int) (3 kx)) @t)) unit)
  (lambda (bs) (if (null? bs) #u (begin (k-bind (extract (car bs) 1) (extract (car bs) 2)) (k-bind-letrec (cdr bs))))))
;; Whether `x` is a lambda, under any type abstractions and ascriptions.
(define k-lambda? (subr pure (kx) bool)
  (lambda (x)
    (tagcase x
      (x-lambda (ps body a b) #t)
      (x-plambda (bs e a b) (k-lambda? e))
      (x-the (t e a b) (k-lambda? e))
      (else y #f))))
(define k-letrec-not-lambda (subr pure (symbol) string)
  (lambda (n)
    (string-append (k-quote (symbol->string n))
                   " is bound recursively, so it must be a lambda: nothing may run before every binding exists")))

(define k-proj-map (subr checks (k-binders (listof k-desc @t) int int) k-map)
  (lambda (bs ds a b)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2)) (d (car ds))
               (ok (tagcase d (dr (r) (= k 0)) (de (e) (= k 1)) (dt (t) (= k 2)))))
          (if ok
              (cons (cons v d) (k-proj-map (cdr bs) (cdr ds) a b))
              (k-fail (k-cat4 (k-quote (symbol->string (k-dvar-name v))) " is bound as a " (k-kind-debug k)
                              ", and the description given is not one")
                      a b))))))
(define k-param-types (subr checks ((listof (productof (1 symbol) (2 k-ids)) @t) k-ids int int) k-bindings)
  (lambda (ps hint a b)
    (if (null? ps)
        nil
        (let* ((n (extract (car ps) 1)) (t (extract (car ps) 2))
               (ty (cond ((not (null? t)) (car t))
                         ((not (null? hint)) (car hint))
                         (else (k-fail (k-cat5 "the type of parameter " (k-quote (symbol->string n))
                                               " cannot be known here: write `(" (symbol->string n)
                                               " type)`, or check the `lambda` against a type")
                                       a b))))
               (rest (k-param-types (cdr ps) (if (null? hint) hint (cdr hint)) a b)))
          (cons (cons n ty) rest)))))
(define k-binding-types (subr (maxeff (read @t) (alloc @t)) (k-bindings) k-ids)
  (lambda (bs) (if (null? bs) nil (cons (cdr (car bs)) (k-binding-types (cdr bs))))))
(define k-some-untyped? (subr (read @t) ((listof (productof (1 symbol) (2 k-ids)) @t)) bool)
  (lambda (ps) (cond ((null? ps) #f) ((null? (extract (car ps) 2)) #t) (else (k-some-untyped? (cdr ps))))))

(define k-unannotated? (subr (read @t) (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (k-some-untyped? ps)) (else y #f))))
;; A `lambda` missing parameter types, or a thunk: better told than asked.
(define k-needs-telling? (subr (read @t) (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (or (null? ps) (k-some-untyped? ps))) (else y #f))))

;;; ------------------------------------------------------------ instantiation
;;; A projection left out: the binders of a `poly` solved by matching (local
;;; type inference). A type binder must be solved; an effect binder nothing
;;; constrains is `pure`; a region binder nothing constrains is a fresh
;;; region.

(define-type k-solved (ref k-map @t))
(define k-append-binders (subr (maxeff (read @t) (alloc @t)) (k-binders k-binders) k-binders)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (k-append-binders (cdr xs) ys)))))
(define k-binders-from (subr (maxeff (read @t) (alloc @t)) (int k-binders) (productof (1 k-binders) (2 int)))
  (lambda (t acc)
    (tagcase (k-get t)
      (ty-poly (bs body) (k-binders-from (k-resolve body) (k-append-binders acc bs)))
      (else y (product (1 acc) (2 t))))))

;; The binders of `t` through every nested `poly`, and the type under them.
(define k-binders-of (subr (maxeff (read @t) (alloc @t)) (int) (productof (1 k-binders) (2 int)))
  (lambda (t) (k-binders-from (k-resolve t) nil)))

(define k-unknown? (subr (read @t) (k-binders int) bool)
  (lambda (kinds v) (cond ((null? kinds) #f) ((= (extract (car kinds) 1) v) #t) (else (k-unknown? (cdr kinds) v)))))
(define k-open? (subr (read @t) (k-binders k-solved int) bool)
  (lambda (kinds solved v) (and (k-unknown? kinds v) (null? (k-map-find (get solved) v)))))
(define k-solve (subr kstate (k-solved int k-desc) unit)
  (lambda (solved v d) (set solved (cons (cons v d) (get solved)))))

;; Each region binder nothing has solved gets a fresh region of its own,
;; named after it.
(define k-default-regions (subr kstate (k-binders k-solved) unit)
  (lambda (kinds solved)
    (if (null? kinds)
        #u
        (let ((v (extract (car kinds) 1)))
          (begin
            (if (and (= (extract (car kinds) 2) 0) (null? (k-map-find (get solved) v)))
                (k-solve solved v (dr (k-fresh-region (string-append "@" (symbol->string (k-dvar-name v))))))
                #u)
            (k-default-regions (cdr kinds) solved))))))
(define k-finish-each (subr checks (k-binders k-map int int int) k-map)
  (lambda (kinds m a b ft)
    (if (null? kinds)
        m
        (let ((v (extract (car kinds) 1)) (k (extract (car kinds) 2)))
          (cond ((not (null? (k-map-find m v))) (k-finish-each (cdr kinds) m a b ft))
                ((= k 1) (k-finish-each (cdr kinds) (cons (cons v (de nil)) m) a b ft))
                (else (k-fail (k-cat5 (k-quote (symbol->string (k-dvar-name v))) " cannot be inferred for " (k-show-ty ft)
                                      ": nothing here says what it is. Use `proj`, or `the`" "")
                              a b)))))))

;; The whole solution: every type binder solved, effects defaulting to pure.
(define k-finish (subr checks (k-binders k-solved int int int) k-map)
  (lambda (kinds solved a b ft) (k-finish-each kinds (get solved) a b ft)))

(define k-ty-rank (subr (read @t) (int) int)
  (lambda (t)
    (tagcase (k-get t)
      (ty-base (s) 0) (ty-void () 1) (ty-var (v) 2) (ty-subr (e ps r) 3) (ty-poly (bs x) 4) (ty-ref (x r) 5)
      (ty-pair (x y r) 6) (ty-tag (x y e r) 7) (ty-comp (x y e r) 8) (ty-markkey (x r) 9) (ty-product (ps) 10)
      (ty-sum (ps) 11) (ty-array (x r) 12) (ty-bloblet (fs z r) 13) (ty-link (x) 14) (ty-icell (x r) 15))))
;; Whether no instantiation of `pattern` could fit `actual`.
(define k-wrong-shape? (subr (maxeff (read @t) (alloc @t)) (int int) bool)
  (lambda (pattern actual)
    (let ((p (k-ty-rank pattern)) (a (k-ty-rank actual)))
      (cond ((or (= p 2) (= a 1)) #f)
            ((= p 3) (null? (k-as-subr actual)))
            (else (not (= p a)))))))

;; An argument of the wrong shape altogether is the error to report, before
;; any binder it left unsolved.
(define k-inst-shapes (subr checks (kxs k-ids int k-solved (arrayof int @t)) unit)
  (lambda (args params i solved done-t)
    (if (null? args)
        #u
        (let ((t (array-ref done-t i)))
          (if (and (>= t 0) (k-wrong-shape? (car params) t))
              (let ((p (k-subst (car params) (get solved))))
                (k-fail (k-cat5 "argument " (int->string (+ i 1)) " is a " (k-show-ty t) (k-cat3 ", where a " (k-show-ty p) " is expected"))
                        (k-start (car args)) (k-end (car args))))
              (k-inst-shapes (cdr args) (cdr params) (+ i 1) solved done-t))))))

;; Whether `t` mentions a binder of any kind not yet solved.
(define k-open-region? (subr (read @t) (k-region k-binders k-solved) bool)
  (lambda (r kinds solved) (tagcase r (r-var (v) (k-open? kinds solved v)) (else y #f))))
(define k-open-effect? (subr (read @t) (k-eff k-binders k-solved) bool)
  (lambda (e kinds solved)
    (cond ((null? e) #f)
          ((tagcase (car e) (a-var (v) (k-open? kinds solved v)) (else y (k-open-region? (k-atom-region (car e)) kinds solved))) #t)
          (else (k-open-effect? (cdr e) kinds solved)))))
(define k-push-ids (subr (maxeff (read @t) (alloc @t)) (k-ids k-ids) k-ids)
  (lambda (xs onto) (if (null? xs) onto (cons (car xs) (k-push-ids (cdr xs) onto)))))
(define k-push-parts (subr (maxeff (read @t) (alloc @t)) (k-parts k-ids) k-ids)
  (lambda (ps onto) (if (null? ps) onto (cons (extract (car ps) 2) (k-push-parts (cdr ps) onto)))))
(define k-any-walk (subr kstate (k-ids int k-binders k-solved) bool)
  (lambda (stack seen kinds solved)
    (if (null? stack)
        #f
        (let ((t (k-resolve (car stack))) (rest (cdr stack)))
          (if (k-visit? t seen)
              (k-any-walk rest seen kinds solved)
              (let ((seen seen))
               (letrec ((reg (subr (read @t) (k-region) bool) (lambda (r) (k-open-region? r kinds solved)))
                        (go (subr kstate (k-ids) bool) (lambda (s) (k-any-walk s seen kinds solved))))
                (tagcase (k-get t)
                  (ty-var (v) (or (k-open? kinds solved v) (go rest)))
                  (ty-subr (e ps r) (or (k-open-effect? e kinds solved) (go (k-push-ids ps (cons r rest)))))
                  (ty-poly (bs body) (go (cons body rest)))
                  (ty-ref (x r) (or (reg r) (go (cons x rest))))
                  (ty-markkey (x r) (or (reg r) (go (cons x rest))))
                  (ty-array (x r) (or (reg r) (go (cons x rest))))
                  (ty-icell (x r) (or (reg r) (go (cons x rest))))
                  (ty-pair (x y r) (or (reg r) (go (cons x (cons y rest)))))
                  (ty-bloblet (fs z r) (or (reg r) (go (k-push-ids fs rest))))
                  (ty-product (ps) (go (k-push-parts ps rest)))
                  (ty-sum (ps) (go (k-push-parts ps rest)))
                  (ty-tag (x y e r) (or (reg r) (k-open-effect? e kinds solved) (go (cons x (cons y rest)))))
                  (ty-comp (x y e r) (or (reg r) (k-open-effect? e kinds solved) (go (cons x (cons y rest)))))
                  (else y (go rest))))))))))
(define k-mentions-any-unknown? (subr kstate (int k-binders k-solved) bool)
  (lambda (t kinds solved) (k-any-walk (cons t nil) (k-new-epoch) kinds solved)))

(define-rec
  (k-vars-walk (subr (maxeff (read @t) (write @t) (alloc @t)) (int int k-binders k-solved) bool)
    (lambda (t seen kinds solved)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #f
            (letrec ((w (subr (maxeff (read @t) (write @t) (alloc @t)) (int) bool) (lambda (x) (k-vars-walk x seen kinds solved)))
                  (ws (subr (maxeff (read @t) (write @t) (alloc @t)) (k-ids) bool) (lambda (xs) (k-vars-walks xs seen kinds solved))))
              (begin
                (tagcase (k-get t)
                  (ty-var (v) (k-open? kinds solved v))
                  (ty-subr (e ps r) (or (ws ps) (w r)))
                  (ty-poly (bs body) (w body))
                  (ty-ref (a r) (w a))
                  (ty-markkey (a r) (w a))
                  (ty-array (a r) (w a))
                  (ty-icell (a r) (w a))
                  (ty-bloblet (fs z r) (ws fs))
                  (ty-product (ps) (ws (k-push-parts ps nil)))
                  (ty-sum (ps) (ws (k-push-parts ps nil)))
                  (ty-pair (a b r) (or (w a) (w b)))
                  (ty-tag (a b e r) (or (w a) (w b)))
                  (ty-comp (a b e r) (or (w a) (w b)))
                  (else y #f))))))))
  (k-vars-walks (subr (maxeff (read @t) (write @t) (alloc @t)) (k-ids int k-binders k-solved) bool)
    (lambda (ts seen kinds solved) (cond ((null? ts) #f) ((k-vars-walk (car ts) seen kinds solved) #t) (else (k-vars-walks (cdr ts) seen kinds solved))))))

;; Whether `t` mentions a type binder not yet solved.
(define k-mentions-unknown-type? (subr (maxeff (read @t) (write @t) (alloc @t)) (int k-binders k-solved) bool)
  (lambda (t kinds solved) (k-vars-walk t (k-new-epoch) kinds solved)))
(define k-any-unknown-type? (subr (maxeff (read @t) (write @t) (alloc @t)) (k-ids k-binders k-solved) bool)
  (lambda (ts kinds solved)
    (cond ((null? ts) #f) ((k-mentions-unknown-type? (car ts) kinds solved) #t) (else (k-any-unknown-type? (cdr ts) kinds solved)))))
(define k-unify-region (subr kstate (k-region k-region k-binders k-solved) unit)
  (lambda (p a kinds solved)
    (tagcase p (r-var (v) (if (k-open? kinds solved v) (k-solve solved v (dr a)) #u)) (else y #u))))
(define k-same-kind-regions (subr (maxeff (read @t) (alloc @t)) (k-eff int) k-regions)
  (lambda (e rank)
    (cond ((null? e) nil)
          ((= (k-atom-rank (car e)) rank) (cons (k-atom-region (car e)) (k-same-kind-regions (cdr e) rank)))
          (else (k-same-kind-regions (cdr e) rank)))))
;; An effect binder takes all of `actual`; a region named in an atom is
;; matched against the actual's atoms of that kind when there is only one.
(define k-unify-effect (subr kstate (k-eff k-eff k-binders k-solved) unit)
  (lambda (pattern actual kinds solved)
    (if (null? pattern)
        #u
        (let ((atom (car pattern)))
          (begin
            (tagcase atom
              (a-var (v)
                (if (k-unknown? kinds v)
                    (let* ((f (k-map-find (get solved) v))
                           (prev (if (null? f) (the k-eff nil) (tagcase (cdr (car f)) (de (e) e) (else y (the k-eff nil))))))
                      (k-solve solved v (de (k-union prev actual))))
                    #u))
              (else y
                (tagcase (k-atom-region atom)
                  (r-var (v)
                    (if (k-open? kinds solved v)
                        (let ((same (k-same-kind-regions actual (k-atom-rank atom))))
                          (if (and (not (null? same)) (null? (cdr same))) (k-solve solved v (dr (car same))) #u))
                        #u))
                  (else z #u))))
            (k-unify-effect (cdr pattern) actual kinds solved))))))

;;; Matching: solve binders in `pattern` so that `actual` fits it. Never
;;; fails; what cannot be matched is left for the subtype check after.

(define-rec
  (k-unify (subr kstate (int int k-binders k-solved k-trail) unit)
    (lambda (pattern actual kinds solved trail)
      (let ((p (k-resolve pattern)) (a (k-resolve actual)))
        (if (k-trail-has? (get trail) p a)
            #u
            (begin
              (set trail (cons (cons p a) (get trail)))
              (let ((pt (k-get p)) (at (k-get a)))
                (if (and (tagcase at (ty-void () #t) (else y #f))
                         (not (tagcase pt (ty-var (v) (k-open? kinds solved v)) (else y #f))))
                    #u
                    (letrec ((u (subr kstate (int int) unit) (lambda (x y) (k-unify x y kinds solved trail)))
                          (ur (subr kstate (k-region k-region) unit) (lambda (r s) (k-unify-region r s kinds solved)))
                          (ue (subr kstate (k-eff k-eff) unit) (lambda (e f) (k-unify-effect e f kinds solved))))
                      (tagcase pt
                        (ty-var (v)
                          (if (k-unknown? kinds v)
                              (let ((f (k-map-find (get solved) v)))
                                (if (null? f)
                                    (k-solve solved v (dt a))
                                    (tagcase (cdr (car f))
                                      (dt (prev) (if (and (not (k-subtype a prev)) (k-subtype prev a)) (k-solve solved v (dt a)) #u))
                                      (else y #u))))
                              #u))
                        (ty-subr (pe pp pr)
                          (let ((c (k-as-subr a)))
                            (if (null? c)
                                #u
                                (let ((ap (extract (car c) 2)))
                                  (if (not (= (k-length pp) (k-length ap)))
                                      #u
                                      (begin (k-unify-lists pp ap kinds solved trail)
                                             (u pr (extract (car c) 3))
                                             (ue pe (extract (car c) 1))))))))
                        (ty-ref (x r) (tagcase at (ty-ref (y s) (begin (ur r s) (u x y))) (else z #u)))
                        (ty-markkey (x r) (tagcase at (ty-markkey (y s) (begin (ur r s) (u x y))) (else z #u)))
                        (ty-array (x r) (tagcase at (ty-array (y s) (begin (ur r s) (u x y))) (else z #u)))
                        (ty-icell (x r) (tagcase at (ty-icell (y s) (begin (ur r s) (u x y))) (else z #u)))
                        (ty-pair (x1 x2 r) (tagcase at (ty-pair (y1 y2 s) (begin (ur r s) (u x1 y1) (u x2 y2))) (else z #u)))
                        (ty-product (pp) (tagcase at (ty-product (pa) (k-unify-parts pp pa kinds solved trail)) (else z #u)))
                        (ty-sum (pp) (tagcase at (ty-sum (pa) (k-unify-parts pp pa kinds solved trail)) (else z #u)))
                        (ty-bloblet (fp zp r)
                          (tagcase at
                            (ty-bloblet (fa za s)
                              (if (= (k-length fp) (k-length fa)) (begin (ur r s) (k-unify-lists fp fa kinds solved trail)) #u))
                            (else z #u)))
                        (ty-tag (a1 h1 d1 r1)
                          (tagcase at (ty-tag (a2 h2 d2 r2) (begin (ur r1 r2) (u a1 a2) (u h1 h2) (ue d1 d2))) (else z #u)))
                        (ty-comp (h1 a1 d1 r1)
                          (tagcase at (ty-comp (h2 a2 d2 r2) (begin (ur r1 r2) (u a1 a2) (u h1 h2) (ue d1 d2))) (else z #u)))
                        (else z #u))))))))))
  (k-unify-lists (subr kstate (k-ids k-ids k-binders k-solved k-trail) unit)
    (lambda (xs ys kinds solved trail)
      (if (null? xs) #u (begin (k-unify (car xs) (car ys) kinds solved trail) (k-unify-lists (cdr xs) (cdr ys) kinds solved trail)))))
  (k-unify-parts (subr kstate (k-parts k-parts k-binders k-solved k-trail) unit)
    (lambda (pp pa kinds solved trail)
      (if (null? pp)
          #u
          (let ((y (k-part-find pa (extract (car pp) 1))))
            (begin (if (>= y 0) (k-unify (extract (car pp) 2) y kinds solved trail) #u)
                   (k-unify-parts (cdr pp) pa kinds solved trail)))))))

;; Instantiate a polymorphic value used, unapplied, where `expected` is
;; wanted.
(define k-instantiate-against (subr checks (int int int int) int)
  (lambda (t expected a b)
    (let* ((bo (k-binders-of t)) (kinds (extract bo 1)) (inner (extract bo 2)) (solved (the k-solved (new nil))))
      (begin
        (k-unify inner expected kinds solved (the k-trail (new nil)))
        (k-default-regions kinds solved)
        (k-subst inner (k-finish kinds solved a b t))))))
(define k-plambda-matches? (subr (read @t) (kx k-ty) bool)
  (lambda (x et)
    (tagcase x
      (x-plambda (binders body a b)
        (tagcase et (ty-poly (bs want) (and (= (k-length bs) (k-length binders)) (k-same-kinds? bs binders))) (else y #f)))
      (else y #f))))
(define k-same-labels? (subr (read @t) ((listof (productof (1 symbol) (2 kx)) @t) k-parts) bool)
  (lambda (fs ps)
    (cond ((null? fs) (null? ps))
          ((null? ps) #f)
          (else (and (symbol=? (extract (car fs) 1) (extract (car ps) 1)) (k-same-labels? (cdr fs) (cdr ps)))))))

;;; ------------------------------------------------------------ tagcase

(define-type k-arms (listof (productof (1 symbol) (2 bool) (3 k-names) (4 kx)) @t))
(define k-all-fit? (subr kstate (k-ids int) bool)
  (lambda (types t) (cond ((null? types) #t) ((k-subtype (car types) t) (k-all-fit? (cdr types) t)) (else #f))))
;; The first of `candidates` every one of `types` fits, or -1.
(define k-upper-bound (subr kstate (k-ids k-ids) int)
  (lambda (candidates types)
    (cond ((null? candidates) -1)
          ((k-all-fit? types (car candidates)) (car candidates))
          (else (k-upper-bound (cdr candidates) types)))))
(define k-part-names (subr (maxeff (read @t) (alloc @t)) (k-parts) (listof string @t))
  (lambda (ps) (if (null? ps) nil (cons (symbol->string (extract (car ps) 1)) (k-part-names (cdr ps))))))
(define k-arm-named? (subr (read @t) (k-arms symbol) bool)
  (lambda (arms l) (cond ((null? arms) #f) ((symbol=? (extract (car arms) 1) l) #t) (else (k-arm-named? (cdr arms) l)))))
(define k-variants-not-named (subr (maxeff (read @t) (alloc @t)) (k-parts k-arms) k-parts)
  (lambda (vs arms)
    (cond ((null? vs) nil)
          ((k-arm-named? arms (extract (car vs) 1)) (k-variants-not-named (cdr vs) arms))
          (else (cons (car vs) (k-variants-not-named (cdr vs) arms))))))
(define k-cannot-take-apart (subr checks (symbol int k-names kx) k-bindings)
  (lambda (tag t names body)
    (k-fail (k-cat5 (k-quote (symbol->string tag)) " carries a " (k-show-ty t) ", which cannot be taken apart into "
                    (string-append (int->string (k-length names)) " name(s)"))
            (k-start body) (k-end body))))
(define k-zip-fields (subr (maxeff (read @t) (alloc @t)) (k-names k-parts) k-bindings)
  (lambda (ns fs) (if (null? ns) nil (cons (cons (car ns) (extract (car fs) 2)) (k-zip-fields (cdr ns) (cdr fs))))))
;; The atoms of `e` in neither `bound` nor `own`.
(define k-beyond (subr (maxeff (read @t) (alloc @t)) (k-eff k-eff k-eff) k-eff)
  (lambda (e bound own)
    (cond ((null? e) nil)
          ((or (k-contains? bound (car e)) (k-contains? own (car e))) (k-beyond (cdr e) bound own))
          (else (cons (car e) (k-beyond (cdr e) bound own))))))
(define k-none-reach? (subr (maxeff (read @t) (write @t) (alloc @t)) (k-names k-names k-region) bool)
  (lambda (vs tv r)
    (cond ((null? vs) #t)
          ((k-has-name? tv (car vs)) (k-none-reach? (cdr vs) tv r))
          (else (let ((t (k-lookup (car vs))))
                  (and (or (< t 0) (not (k-has-region-in? (k-regions-in t) r))) (k-none-reach? (cdr vs) tv r)))))))
;; Whether the only way `body` can name anything in region `r` is the
;; variable `tag`, if it is one.
(define k-reaches-only? (subr (maxeff (read @t) (write @t) (alloc @t)) (kx kx k-region) bool)
  (lambda (body tag r)
    (let ((tv (the k-names (tagcase tag (x-var (s a b) (cons s nil)) (else y nil)))))
      (k-none-reach? (k-free-vars body) tv r))))

;;; ------------------------------------------------------------ synthesis

(define k-has-comefrom? (subr (read @t) (k-eff) bool)
  (lambda (e) (and (not (null? e)) (or (tagcase (car e) (a-comefrom (r) #t) (else y #f)) (k-has-comefrom? (cdr e))))))
;; `(letregion r …)`'s body of type `t` and effect `e`, closed: its value
;; may not mention `r`, and no continuation captured in it may outlive it;
;; what it does to `r` is masked, as nothing outside can name `r`.
(define k-close-region (subr checks (kx int int k-eff int int) k-te)
  (lambda (x r t e a b)
    (let ((name (symbol->string (k-dvar-name r))))
      (if (k-has-region-in? (k-regions-in t) (r-var r))
          (k-fail (k-cat4 "the value of `letregion " name "` would outlive its region: its type is " (k-show-ty t)) a b)
          (let ((masked (k-mask x e t)))
            (if (k-has-comefrom? masked)
                (k-fail (k-cat4 "a continuation captured in `letregion " name "` could outlive its region: its effect is "
                                (k-show-effect masked))
                        a b)
                (k-te t masked)))))))

(define-rec
  (k-synth (subr checks (kx) k-te)
    (lambda (x)
      (tagcase x
        (x-var (s a b)
          (let ((t (k-lookup s)))
            (if (< t 0) (k-fail (k-cat3 "unbound variable `" (symbol->string s) "`") a b) (k-te t nil))))
        (x-const (t a b) (k-te t nil))
        (x-lambda (ps body a b) (k-synth-lambda-as x nil -1))
        (x-app (f args a b) (k-synth-app x f args -1))
        (x-the (t e a b) (k-te t (k-check e t)))
        (x-plambda (bs body a b)
          (let ((r (k-synth body)))
            (if (null? (extract r 2))
                (k-te (k-ty-new (ty-poly bs (extract r 1))) nil)
                (k-fail (string-append "a `plambda` body must be pure, and this one has " (k-show-effect (extract r 2))) a b))))
        (x-proj (body ds a b)
          (let* ((r (k-synth body)) (t (extract r 1)))
            (tagcase (k-get t)
              (ty-poly (bs inner)
                (if (not (= (k-length bs) (k-length ds)))
                    (k-fail (k-cat5 "this `poly` binds " (int->string (k-length bs)) " description(s); `proj` gave "
                                    (int->string (k-length ds)) "")
                            a b)
                    (let ((result (k-subst inner (k-proj-map bs ds a b))))
                      (k-te result (k-mask x (extract r 2) result)))))
              (else y (k-fail (string-append "`proj` needs a polymorphic value, not a " (k-show-ty t)) a b)))))
        (x-if (p c d a b)
          (let ((rp (k-synth p)))
            (if (not (k-subtype (extract rp 1) k-bool))
                (k-fail "an `if` test must be a bool" (k-start p) (k-end p))
                (let* ((rc (k-synth c)) (rd (k-synth d)) (tc (extract rc 1)) (td (extract rd 1))
                       (t (cond ((k-subtype tc td) td)
                                ((k-subtype td tc) tc)
                                (else (k-fail (k-cat4 "the branches are a " (k-show-ty tc) " and a " (k-show-ty td)) a b)))))
                  (k-te t (k-mask x (k-union (extract rp 2) (k-union (extract rc 2) (extract rd 2))) t))))))
        (x-letrec (bs body a b)
          (let ((saved (k-mark)))
            (begin
              (k-bind-letrec bs)
              (let* ((ie (k-check-letrec bs)) (rb (k-synth body)))
                (begin
                  (k-unbind-to saved)
                  (k-te (extract rb 1) (k-mask x (k-union ie (extract rb 2)) (extract rb 1))))))))
        (x-let (bs body a b)
          (let* ((inits (k-synth-lets bs)) (saved (k-mark)))
            (begin
              (k-bind-all (extract inits 1))
              (let ((rb (k-synth body)))
                (begin
                  (k-unbind-to saved)
                  (k-te (extract rb 1) (k-mask x (k-union (extract inits 2) (extract rb 2)) (extract rb 1))))))))
        (x-prompt (t body h a b) (k-synth-prompt x t body h))
        (x-letregion (r body a b)
          (let ((rb (k-synth body))) (k-close-region x r (extract rb 1) (extract rb 2) a b)))
        (x-bloblet (op i args a b) (k-synth-bloblet x op i args -1))
        (x-product (fs a b)
          (let* ((r (k-synth-fields fs)) (t (k-ty-new (ty-product (extract r 1)))))
            (k-te t (k-mask x (extract r 2) t))))
        (x-extract (e l a b)
          (let* ((r (k-synth e)) (pt (extract r 1)))
            (tagcase (k-get pt)
              (ty-product (fs)
                (let ((t (k-part-find fs l)))
                  (if (< t 0)
                      (k-fail (k-cat4 "a " (k-show-ty pt) " has no " (k-quote (symbol->string l))) a b)
                      (begin
                        (set k-extracts (cons (product (1 a) (2 b) (3 (k-part-index fs l 0))) (get k-extracts)))
                        (k-te t (k-mask x (extract r 2) t))))))
              (else y (k-fail (string-append "a product is expected here, and this is a " (k-show-ty pt)) (k-start e) (k-end e))))))
        (x-sum (l e a b)
          (let* ((r (k-synth e)) (t (k-ty-new (ty-sum (cons (product (1 l) (2 (extract r 1))) nil)))))
            (k-te t (k-mask x (extract r 2) t))))
        (x-tagcase (s arms els a b) (k-synth-tagcase x s arms els -1))
        (x-begin (xs a b)
          (let ((r (k-synth-seq xs k-unit nil)))
            (k-te (extract r 1) (k-mask x (extract r 2) (extract r 1))))))))
  (k-synth-seq (subr checks (kxs int k-eff) k-te)
    (lambda (xs last e)
      (if (null? xs) (k-te last e) (let ((r (k-synth (car xs)))) (k-synth-seq (cdr xs) (extract r 1) (k-union e (extract r 2)))))))
  (k-synth-fields (subr checks ((listof (productof (1 symbol) (2 kx)) @t)) (productof (1 k-parts) (2 k-eff)))
    (lambda (fs)
      (if (null? fs)
          (product (1 nil) (2 nil))
          (let* ((r (k-synth (extract (car fs) 2))) (rest (k-synth-fields (cdr fs))))
            (product (1 (cons (product (1 (extract (car fs) 1)) (2 (extract r 1))) (extract rest 1)))
                     (2 (k-union (extract r 2) (extract rest 2))))))))
  (k-synth-lets (subr checks ((listof (productof (1 symbol) (2 kx)) @t)) (productof (1 k-bindings) (2 k-eff)))
    (lambda (bs)
      (if (null? bs)
          (product (1 nil) (2 nil))
          (let* ((r (k-synth (extract (car bs) 2))) (rest (k-synth-lets (cdr bs))))
            (product (1 (cons (cons (extract (car bs) 1) (extract r 1)) (extract rest 1)))
                     (2 (k-union (extract r 2) (extract rest 2))))))))
  (k-check-letrec (subr checks ((listof (productof (1 symbol) (2 int) (3 kx)) @t)) k-eff)
    (lambda (bs)
      (if (null? bs)
          nil
          (let* ((n (extract (car bs) 1)) (t (extract (car bs) 2)) (init (extract (car bs) 3))
                 ;; Only lambdas: then nothing runs before every binding
                 ;; exists, and no one sees the knot tied.
                 (e (if (k-lambda? init)
                        (k-check-declared n t init)
                        (k-fail (k-letrec-not-lambda n) (k-start init) (k-end init))))
                 (rest (k-check-letrec (cdr bs))))
            (k-union e rest)))))
  ;; Check `init` against `t`, the type `n` is declared; an error at `init`
  ;; itself says so.
  (k-check-declared (subr checks (symbol int kx) k-eff)
    (lambda (n t init)
      (extract (k-prefixing (lambda () (k-te t (k-check init t))) (k-start init) (k-end init)
                            (k-cat4 (k-quote (symbol->string n)) " is declared a " (k-show-ty t) ": "))
               2)))
  ;;; ------------------------------------------------------------ lambda

  ;; A `lambda`'s type. `hint` supplies the types of parameters the program
  ;; left out; `result`, when not -1, is what the body is checked against.
  (k-synth-lambda-as (subr checks (kx k-ids int) k-te)
    (lambda (x hint result)
      (tagcase x
        (x-lambda (ps body a b)
          (let* ((typed (k-param-types ps hint a b)) (saved (k-mark)))
            (begin
              (k-bind-all typed)
              (let* ((r (if (>= result 0)
                            (let ((e (k-check body result))) (k-te result (k-mask body e result)))
                            (let ((r (k-synth body))) (k-te (extract r 1) (k-mask body (extract r 2) (extract r 1)))))))
                (begin
                  (k-unbind-to saved)
                  (k-te (k-ty-new (ty-subr (extract r 2) (k-binding-types typed) (extract r 1))) nil))))))
        (else y (k-fail "a lambda" (k-start x) (k-end x))))))
  ;;; ------------------------------------------------------------ application
  (k-synth-app (subr checks (kx kx kxs int) k-te)
    (lambda (x f args expected)
      (let* ((a (k-start x)) (b (k-end x))
             (rf (k-synth f))
             (n (k-length args))
             (done-t (the (arrayof int @t) (make-array n -1)))
             (done-e (the (arrayof k-eff @t) (make-array n nil)))
             (ft (tagcase (k-get (extract rf 1))
                   (ty-poly (bs body) (k-instantiate (extract rf 1) args expected a b done-t done-e))
                   (else y (extract rf 1))))
             (callee (k-as-subr ft)))
        (if (null? callee)
            (k-fail (string-append "not a subroutine: " (k-show-ty ft)) a b)
            (let ((params (extract (car callee) 2)))
              (if (not (= (k-length params) n))
                  (k-fail (k-cat4 "expected " (int->string (k-length params)) " argument(s), got " (int->string n)) a b)
                  (let* ((e (k-app-args args params 0 done-t done-e (extract rf 2)))
                         (e (k-union e (extract (car callee) 1)))
                         (result (extract (car callee) 3)))
                    (k-te result (k-mask x e result)))))))))
  (k-app-args (subr checks (kxs k-ids int (arrayof int @t) (arrayof k-eff @t) k-eff) k-eff)
    (lambda (args params i done-t done-e e)
      (if (null? args)
          e
          (let* ((arg (car args)) (p (car params)) (t (array-ref done-t i))
                 (ae (if (>= t 0)
                         (if (k-subtype t p)
                             (array-ref done-e i)
                             (k-fail (k-cat5 "argument " (int->string (+ i 1)) " is a " (k-show-ty t)
                                             (k-cat3 ", where a " (k-show-ty p) " is expected"))
                                     (k-start arg) (k-end arg)))
                         (k-check-argument arg p i))))
            (k-app-args (cdr args) (cdr params) (+ i 1) done-t done-e (k-union e ae))))))
  ;; An argument that failed to check is reported as that argument.
  (k-check-argument (subr checks (kx int int) k-eff)
    (lambda (arg p i)
      (extract (k-rewriting (lambda () (k-te p (k-check arg p))) (k-start arg) (k-end arg)
                            (lambda (m want got) (k-cat5 "argument " (int->string (+ i 1)) " is a " got
                                                         (k-cat3 ", where a " want " is expected"))))
               2)))
  (k-instantiate (subr checks (int kxs int int int (arrayof int @t) (arrayof k-eff @t)) int)
    (lambda (ft args expected a b done-t done-e)
      (let* ((bo (k-binders-of ft)) (kinds (extract bo 1)) (inner (extract bo 2)) (callee (k-as-subr inner)))
        (if (null? callee)
            (k-fail (string-append "not a subroutine, even once projected: " (k-show-ty ft)) a b)
            (let ((params (extract (car callee) 2)) (result (extract (car callee) 3)) (solved (the k-solved (new nil))))
              (if (not (= (k-length params) (k-length args)))
                  (k-fail (k-cat4 "expected " (int->string (k-length params)) " argument(s), got " (int->string (k-length args))) a b)
                  (begin
                    (if (>= expected 0) (k-unify result expected kinds solved (the k-trail (new nil))) #u)
                    (k-inst-asked args params 0 kinds solved done-t done-e)
                    (k-inst-told args params 0 kinds solved done-t done-e)
                    (k-inst-shapes args params 0 solved done-t)
                    (k-default-regions kinds solved)
                    (k-subst inner (k-finish kinds solved a b ft)))))))))
  ;; What the arguments are, except the ones that need to be told.
  (k-inst-asked (subr checks (kxs k-ids int k-binders k-solved (arrayof int @t) (arrayof k-eff @t)) unit)
    (lambda (args params i kinds solved done-t done-e)
      (if (null? args)
          #u
          (begin
            (if (k-needs-telling? (car args))
                #u
                (let ((p (k-subst (car params) (get solved))))
                  (if (not (k-mentions-any-unknown? p kinds solved))
                      (let ((e (k-check (car args) p))) (begin (array-set! done-t i p) (array-set! done-e i e)))
                      (let ((r (k-synth (car args))))
                        (tagcase (k-get (extract r 1))
                          (ty-poly (bs body) #u)
                          (else y
                            (begin (k-unify (car params) (extract r 1) kinds solved (the k-trail (new nil)))
                                   (array-set! done-t i (extract r 1))
                                   (array-set! done-e i (extract r 2)))))))))
            (k-inst-asked (cdr args) (cdr params) (+ i 1) kinds solved done-t done-e)))))
  ;; The arguments that needed telling: each is checked against its parameter
  ;; as solved so far, and what it turns out to be solves more.
  (k-inst-told (subr checks (kxs k-ids int k-binders k-solved (arrayof int @t) (arrayof k-eff @t)) unit)
    (lambda (args params i kinds solved done-t done-e)
      (if (null? args)
          #u
          (begin
            (if (>= (array-ref done-t i) 0)
                #u
                (let* ((arg (car args))
                       (defaulted (k-default-regions kinds solved))
                       (p (k-subst (car params) (get solved))))
                 (letrec ((not-known (subr checks (int) void)
                         (lambda (t)
                           (k-fail (k-cat5 "argument " (int->string (+ i 1)) " must be a " (k-show-ty t)
                                           ", which is not yet known here; give the other arguments first, or `proj` the operator")
                                   (k-start arg) (k-end arg)))))
                  (cond
                    ((k-needs-telling? arg)
                     (let ((c (k-as-subr p)))
                       (if (or (null? c) (k-any-unknown-type? (extract (car c) 2) kinds solved))
                           (not-known p)
                           (let* ((res (extract (car c) 3))
                                  (r (k-synth-lambda-as arg (extract (car c) 2)
                                                        (if (k-mentions-unknown-type? res kinds solved) -1 res))))
                             (begin (k-unify (car params) (extract r 1) kinds solved (the k-trail (new nil)))
                                    (array-set! done-t i (extract r 1))
                                    (array-set! done-e i (extract r 2)))))))
                    ((k-mentions-unknown-type? p kinds solved) (not-known p))
                    (else (let ((e (k-check arg p))) (begin (array-set! done-t i p) (array-set! done-e i e))))))))
            (k-inst-told (cdr args) (cdr params) (+ i 1) kinds solved done-t done-e)))))
  ;;; ------------------------------------------------------------ check mode
  (k-check (subr checks (kx int) k-eff)
    (lambda (x expected)
      (let* ((et (k-get expected))
             (poly? (tagcase et (ty-poly (bs body) #t) (else y #f)))
             (plambda? (tagcase x (x-plambda (bs body a b) #t) (else y #f))))
        (cond
          ((and poly? (not plambda?))
           (tagcase et
             (ty-poly (bs body)
               (let ((e (k-check x body)))
                 (if (null? e) e (k-fail (string-append "a polymorphic value must be pure, and this has " (k-show-effect e)) (k-start x) (k-end x)))))
             (else y nil)))
          ((and poly? plambda? (k-plambda-matches? x et))
           (tagcase x
             (x-plambda (binders body a b)
               (tagcase et
                 (ty-poly (bs want)
                   (let* ((want (k-subst want (k-rename bs binders))) (e (k-check body want)))
                     (if (null? e) e (k-fail (string-append "a `plambda` body must be pure, and this one has " (k-show-effect e)) a b))))
                 (else y nil)))
             (else y nil)))
          (else (k-check-node x expected et))))))
  (k-check-node (subr checks (kx int k-ty) k-eff)
    (lambda (x expected et)
      (letrec ((otherwise (subr checks () k-eff)
                           (lambda () (let ((r (k-synth x))) (begin (k-expect x (extract r 1) expected) (extract r 2))))))
       (the k-eff (let ((a (k-start x)) (b (k-end x)))
        (tagcase x
          (x-lambda (ps body xa xb)
            (let ((c (k-as-subr expected)))
              (cond
                ((not (null? c))
                 (let ((want (extract (car c) 2)))
                   (if (not (= (k-length want) (k-length ps)))
                       (k-fail (k-cat4 "a subroutine of " (int->string (k-length want)) " parameter(s) is expected, and this `lambda` has "
                                       (int->string (k-length ps)))
                               a b)
                       (let ((r (k-synth-lambda-as x want (extract (car c) 3))))
                         (begin (k-expect x (extract r 1) expected) (extract r 2))))))
                ((k-some-untyped? ps) (k-fail (string-append "a `lambda` cannot be a " (k-show-ty expected)) a b))
                (else (otherwise)))))
          (x-app (f args xa xb)
            (let ((r (k-synth-app x f args expected))) (begin (k-expect x (extract r 1) expected) (extract r 2))))
          (x-bloblet (op i args xa xb)
            (let ((r (k-synth-bloblet x op i args expected))) (begin (k-expect x (extract r 1) expected) (extract r 2))))
          (x-tagcase (s arms els xa xb) (extract (k-synth-tagcase x s arms els expected) 2))
          (x-product (fs xa xb)
            (tagcase et
              (ty-product (want)
                (if (k-same-labels? fs want)
                    (k-mask x (k-check-fields fs want) expected)
                    (otherwise)))
              (else y (otherwise))))
          (x-sum (l e xa xb)
            (tagcase et
              (ty-sum (vs)
                (let ((t (k-part-find vs l)))
                  (if (>= t 0) (k-mask x (k-check e t) expected) (otherwise))))
              (else y (otherwise))))
          (x-var (s xa xb)
            (let ((t (k-lookup s)))
              (if (and (>= t 0) (tagcase (k-get t) (ty-poly (bs body) #t) (else y #f)))
                  (let ((inst (k-instantiate-against t expected a b)))
                    (begin (k-expect x inst expected) nil))
                  (otherwise))))
          (x-if (p c d xa xb)
            (let* ((pe (k-check p k-bool)) (ce (k-check c expected)) (de (k-check d expected)))
              (k-mask x (k-union pe (k-union ce de)) expected)))
          (x-begin (xs xa xb)
            (let ((e (k-check-seq xs expected nil)))
              (k-mask x e expected)))
          (x-let (bs body xa xb)
            (let* ((inits (k-synth-lets bs)) (saved (k-mark)))
              (begin
                (k-bind-all (extract inits 1))
                (let ((e (k-check body expected)))
                  (begin (k-unbind-to saved) (k-mask x (k-union (extract inits 2) e) expected))))))
          (else y (otherwise))))))))
  (k-check-seq (subr checks (kxs int k-eff) k-eff)
    (lambda (xs expected e)
      (if (null? (cdr xs))
          (k-union e (k-check (car xs) expected))
          (let ((r (k-synth (car xs)))) (k-check-seq (cdr xs) expected (k-union e (extract r 2)))))))
  (k-check-fields (subr checks ((listof (productof (1 symbol) (2 kx)) @t) k-parts) k-eff)
    (lambda (fs ps)
      (if (null? fs)
          nil
          (let* ((e (k-check (extract (car fs) 2) (extract (car ps) 2))) (rest (k-check-fields (cdr fs) (cdr ps))))
            (k-union e rest)))))
  (k-synth-tagcase (subr checks (kx kx k-arms (listof (productof (1 symbol) (2 kx)) @t) int) k-te)
    (lambda (x s arms els expected)
      (let* ((rs (k-synth s)) (st (extract rs 1)))
        (tagcase (k-get st)
          (ty-sum (variants)
            (let* ((arm-results (k-tagcase-arms arms variants st expected))
                   (rest (k-variants-not-named variants arms))
                   (e (k-union (extract rs 2) (extract arm-results 2)))
                   (both
                    (if (null? els)
                        (if (null? rest)
                            (product (1 (extract arm-results 1)) (2 e))
                            (k-fail (string-append "this `tagcase` has no arm for " (k-join (k-part-names rest) ", ")) (k-start x) (k-end x)))
                        (let* ((y (extract (car els) 1)) (body (extract (car els) 2))
                               (rest-ty (k-ty-new (ty-sum rest)))
                               (r (k-in-scope-check y rest-ty body expected)))
                          (product (1 (k-push-ids (extract arm-results 1) (cons (extract r 1) nil))) (2 (k-union e (extract r 2)))))))
                   (types (extract both 1))
                   (t (if (>= expected 0)
                          expected
                          (let ((found (k-upper-bound types types)))
                            (if (< found 0)
                                (k-fail (string-append "the arms are " (k-join (k-show-list types nil) ", ")) (k-start x) (k-end x))
                                found)))))
              (k-te t (k-mask x (extract both 2) t))))
          (else y (k-fail (string-append "a sum is expected here, and this is a " (k-show-ty st)) (k-start s) (k-end s)))))))
  ;; Each arm: its type and the effects of all.
  (k-tagcase-arms (subr checks (k-arms k-parts int int) (productof (1 k-ids) (2 k-eff)))
    (lambda (arms variants st expected)
      (if (null? arms)
          (product (1 nil) (2 nil))
          (let* ((arm (car arms)) (tag (extract arm 1)) (body (extract arm 4)) (t (k-part-find variants tag)))
            (if (< t 0)
                (k-fail (k-cat4 "a " (k-show-ty st) " has no tag " (k-quote (symbol->string tag))) (k-start body) (k-end body))
                (let* ((bound (if (extract arm 2)
                                  (tagcase (k-get t)
                                    (ty-product (fs)
                                      (if (= (k-length fs) (k-length (extract arm 3)))
                                          (k-zip-fields (extract arm 3) fs)
                                          (k-cannot-take-apart tag t (extract arm 3) body)))
                                    (else y (k-cannot-take-apart tag t (extract arm 3) body)))
                                  (the k-bindings (cons (cons (car (extract arm 3)) t) nil))))
                       (saved (k-mark))
                       (r (begin
                            (k-bind-all bound)
                            (if (>= expected 0) (k-te expected (k-check body expected)) (k-synth body))))
                       (restored (k-unbind-to saved))
                       (rest (k-tagcase-arms (cdr arms) variants st expected)))
                  (product (1 (cons (extract r 1) (extract rest 1))) (2 (k-union (extract r 2) (extract rest 2))))))))))
  (k-in-scope-check (subr checks (symbol int kx int) k-te)
    (lambda (y t body expected)
      (let ((saved (k-mark)))
        (begin
          (k-bind y t)
          (let ((r (if (>= expected 0) (k-te expected (k-check body expected)) (k-synth body))))
            (begin (k-unbind-to saved) r))))))
  ;;; ------------------------------------------------------------ bloblets
  (k-synth-bloblet (subr checks (kx symbol int kxs int) k-te)
    (lambda (x op i args expected)
      (let ((name (symbol->string op)) (a (k-start x)) (b (k-end x)))
        (if (string=? name "make-bloblet")
            (let* ((e (k-check (car args) k-int))
                   (fields (cdr args))
                   (want (the (listof k-ty @t)
                           (if (< expected 0)
                               nil
                               (tagcase (k-get expected)
                                 (ty-bloblet (fs z r) (if (and (not z) (= (k-length fs) (k-length fields))) (cons (k-get expected) nil) nil))
                                 (else y nil)))))
                   (made (if (null? want)
                             (let ((r (k-synth-each fields)))
                               (product (1 (extract r 1)) (2 (extract r 2)) (3 (k-fresh-region "bloblet"))))
                             (tagcase (car want)
                               (ty-bloblet (fs z r) (product (1 fs) (2 (k-check-each fields fs)) (3 r)))
                               (else y (k-fail "a bloblet" a b)))))
                   (region (extract made 3))
                   (e (k-insert (a-alloc region) (k-union e (extract made 2))))
                   (t (k-ty-new (ty-bloblet (extract made 1) #f region))))
              (k-te t (k-mask x e t)))
            (let* ((bx (car args)) (rest (cdr args)) (rb (k-synth bx)) (bt (extract rb 1)))
              (tagcase (k-get bt)
                (ty-bloblet (fields frozen region)
                  (letrec ((field (subr checks () int)
                                  (lambda ()
                                    (if (< i (k-length fields))
                                        (k-nth fields i)
                                        (k-fail (k-cat5 "a " (k-show-ty bt) " has no field " (int->string i)
                                                        (string-append ": its fields are 0 to " (int->string (- (k-length fields) 1))))
                                                a b)))))
                  (let* ((e (extract rb 2))
                         (te
                          (cond
                            ((string=? name "bloblet-ref")
                             (let ((t (field))) (k-te t (if frozen e (k-insert (a-read region) e)))))
                            ((string=? name "bloblet-set!")
                             (let ((t (field)))
                               (if frozen
                                   (k-fail (k-cat3 "a " (k-show-ty bt) " cannot be changed: its fields are frozen") a b)
                                   (k-te k-unit (k-insert (a-write region) (k-union e (k-check (car rest) t)))))))
                            ((string=? name "bloblet-freeze")
                             (k-te (k-ty-new (ty-bloblet fields #t region)) (k-insert (a-write region) e)))
                            ((string=? name "bloblet-byte")
                             (k-te k-int (k-insert (a-read region) (k-union e (k-check (car rest) k-int)))))
                            ((string=? name "bloblet-set-byte!")
                             (let* ((e1 (k-check (car rest) k-int)) (e2 (k-check (car (cdr rest)) k-int)))
                               (k-te k-unit (k-insert (a-write region) (k-union e (k-union e1 e2))))))
                            (else (k-te k-int e)))))
                    (k-te (extract te 1) (k-mask x (extract te 2) (extract te 1))))))
                (else y (k-fail (string-append "a bloblet is expected here, and this is a " (k-show-ty bt)) (k-start bx) (k-end bx)))))))))
  (k-synth-each (subr checks (kxs) (productof (1 k-ids) (2 k-eff)))
    (lambda (xs)
      (if (null? xs)
          (product (1 nil) (2 nil))
          (let* ((r (k-synth (car xs))) (rest (k-synth-each (cdr xs))))
            (product (1 (cons (extract r 1) (extract rest 1))) (2 (k-union (extract r 2) (extract rest 2))))))))
  (k-check-each (subr checks (kxs k-ids) k-eff)
    (lambda (xs ts)
      (if (null? xs) nil (let* ((e (k-check (car xs) (car ts))) (rest (k-check-each (cdr xs) (cdr ts)))) (k-union e rest)))))
  ;;; ------------------------------------------------------------ prompts
  ;;; The tag's type fixes what crosses the prompt, and the body's effect must
  ;;; be within the tag's bound apart from control on its region. Then the
  ;;; prompt delimits: that control is removed, if the body can reach no other
  ;;; tag in the region.
  (k-synth-prompt (subr checks (kx kx kx kx) k-te)
    (lambda (x tag body handler)
      (let* ((rt (k-synth tag)) (tt (extract rt 1)))
        (tagcase (k-get tt)
          (ty-tag (answer payload bound region)
            (let* ((be (extract (k-rewriting (lambda () (k-te answer (k-check body answer))) (k-start body) (k-end body)
                                             (lambda (m want got) (k-cat4 "the tag's prompts deliver a " want ", and this body is a " got)))
                                2))
                   (own (k-insert (a-goto region) (k-one (a-comefrom region))))
                   (beyond (k-beyond be bound own)))
              (if (not (null? beyond))
                  (k-fail (k-cat4 "the tag allows its delimited computations " (k-show-effect bound) ", and this body also has " (k-show-effect beyond))
                          (k-start body) (k-end body))
                  (let* ((rh (k-synth-handler handler payload answer))
                         (ht (extract rh 1))
                         (c (k-as-subr ht)))
                    (if (null? c)
                        (k-fail (string-append "a handler is a subroutine, not a " (k-show-ty ht)) (k-start handler) (k-end handler))
                        (let ((ps (extract (car c) 2)))
                          (if (or (not (= (k-length ps) 1)) (not (k-subtype payload (car ps))) (not (k-subtype (extract (car c) 3) answer)))
                              (k-fail (k-cat5 (k-cat3 "the handler must take a " (k-show-ty payload) " to a ") (k-show-ty answer) "; it is a " (k-show-ty ht) "")
                                      (k-start handler) (k-end handler))
                              (let* ((delimited (if (k-reaches-only? body tag region) (k-beyond be nil own) be))
                                     (e (k-union (extract rt 2) (k-union (extract rh 2) (k-union (extract (car c) 1) delimited)))))
                                (k-te answer (k-mask x e answer))))))))))
          (else y (k-fail (string-append "a prompt needs a prompt tag, not a " (k-show-ty tt)) (k-start tag) (k-end tag)))))))
  ;; A handler written as a `lambda` of one parameter is told what it takes
  ;; and gives.
  (k-synth-handler (subr checks (kx int int) k-te)
    (lambda (h payload answer)
      (tagcase h
        (x-lambda (ps hbody a b)
          (if (= (k-length ps) 1)
              (k-rewriting (lambda () (k-synth-lambda-as h (cons payload nil) answer)) (k-start hbody) (k-end hbody)
                           (lambda (m want got)
                             (k-cat5 (k-cat3 "the handler must take a " (k-show-ty payload) " to a ") (k-show-ty answer) ", and this gives a " got "")))
              (k-synth h)))
        (else y (k-synth h))))))

;;; ------------------------------------------------------------ programs

;; The initial environment: `(name type)` for each binding.
(define k-standard (subr checks ((listof syn @s)) unit)
  (lambda (entries)
    (if (null? entries)
        #u
        (let* ((pair (k-items (car entries) "a standard binding"))
               (t (k-parse-type (k-nth pair 1))))
          (begin (k-bind (k-name-of (car pair) "a name") t) (k-standard (cdr entries)))))))

(define-type k-out (listof string @t))
(define k-push-binders (subr kstate (k-binders) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (let ((v (extract (car bs) 1)))
          (begin (k-push-desc (k-dvar-name v) (ds-var v (extract (car bs) 2))) (k-push-binders (cdr bs)))))))

;; Put the binders of every `poly` at the top of `t` in scope for reading.
(define k-bind-signature (subr kstate (int) unit)
  (lambda (t)
    (tagcase (k-get t)
      (ty-poly (bs body) (begin (k-push-binders bs) (k-bind-signature body)))
      (else y #u))))

(define k-private (subr checks (syns-a) unit)
  (lambda (rs)
    (if (null? rs)
        #u
        (let ((name (k-name-of (car rs) "expected a name")))
          (if (not (k-at-name? (symbol->string name)))
              (k-sfail "a region constant is written `@name`" (car rs))
              (begin (k-push-desc name (ds-private (k-fresh-region (symbol->string name)))) (k-private (cdr rs))))))))

;; `define-type`, `define-effect` and `private-regions`.
(define k-declare (subr checks (top) unit)
  (lambda (form)
    (tagcase form
      (t-define-type (name def a b)
        (if (syn-symbol? name)
            (begin (k-define-type (k-name-of name "expected a name") def a b) #u)
            (let ((items (k-items name "a type definition")))
              (if (null? items)
                  (k-sfail "expected a name" name)
                  (k-define-family (k-name-of (car items) "expected a name") (cdr items) def)))))
      (t-define-effect (name def a b)
        (let* ((n (k-name-of name "expected a name")) (e (k-parse-effect def))) (k-push-desc n (ds-eff e))))
      (t-private-regions (rs a b) (k-private rs))
      (else y #u))))

;; The first pass: abbreviations, so that types can refer to each other in
;; any order. Values cannot: a definition sees only those before it.
(define k-ahead (subr checks ((listof top @a)) unit)
  (lambda (forms)
    (if (null? forms)
        #u
        (begin (k-declare (car forms)) (k-ahead (cdr forms))))))

(define k-line (subr (maxeff (read @t) (alloc @t)) (int k-eff) string)
  (lambda (t e) (k-cat3 (k-show-ty t) " ! " (k-show-effect e))))
(define k-push-lines (subr (maxeff (read @t) (alloc @t)) ((listof string @t) k-out) k-out)
  (lambda (lines out) (if (null? lines) out (k-push-lines (cdr lines) (cons (car lines) out)))))
(define k-rec-types (subr checks ((listof (productof (1 symbol) (2 syn) (3 exp)) @a)) k-ids)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((t (k-parse-type (extract (car bs) 2))) (bound (k-bind (extract (car bs) 1) t)))
          (cons t (k-rec-types (cdr bs)))))))
(define k-rec-check (subr checks ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) k-ids) (listof string @t))
  (lambda (bs ts)
    (if (null? bs)
        nil
        (let* ((name (extract (car bs) 1))
               (t (car ts))
               (saved (get k-dscope))
               (signed (k-bind-signature t))
               (x (k-resolve-exp (extract (car bs) 3)))
               (restored (set k-dscope saved))
               (e (if (k-lambda? x)
                      (k-check-declared name t x)
                      (k-fail (k-letrec-not-lambda name) (k-start x) (k-end x))))
               (line (k-cat4 "define " (symbol->string name) " : " (k-line t e)))
               (rest (k-rec-check (cdr bs) (cdr ts))))
          (cons line rest)))))

;; `(define-rec (name type lambda) …)`: every name in scope first, then each
;; lambda checked against its type. A line for each.
(define k-define-rec (subr checks ((listof (productof (1 symbol) (2 syn) (3 exp)) @a)) (listof string @t))
  (lambda (bs) (k-rec-check bs (k-rec-types bs))))

;; The second pass: definitions and expressions, in order.
(define k-forms (subr checks ((listof top @a) k-out) k-out)
  (lambda (forms out)
    (if (null? forms)
        (reverse out)
        (let ((line
               (the (listof string @t) (tagcase (car forms)
                 (t-define (name ty init a b)
                   (if (null? ty)
                       (let* ((x (k-resolve-exp init)) (r (k-synth x)))
                         (begin (k-bind name (extract r 1))
                                (cons (k-cat4 "define " (symbol->string name) " : " (k-line (extract r 1) (extract r 2))) nil)))
                       ;; A lambda is in scope in itself, as a `letrec`
                       ;; binding is; anything else is not.
                       (let* ((t (k-parse-type (car ty)))
                              (saved (get k-dscope))
                              (signed (k-bind-signature t))
                              (x (k-resolve-exp init))
                              (restored (set k-dscope saved))
                              (bound (if (k-lambda? x) (k-bind name t) #u))
                              (e (k-check-declared name t x))
                              (after (if (k-lambda? x) #u (k-bind name t))))
                         (cons (k-cat4 "define " (symbol->string name) " : " (k-line t e)) nil))))
                 (t-define-rec (bs a b) (k-define-rec bs))
                 (t-exp (e)
                   (let* ((x (k-resolve-exp e)) (r (k-synth x)))
                     (cons (k-line (extract r 1) (extract r 2)) nil)))
                 (else y nil)))))
          (k-forms (cdr forms) (k-push-lines line out))))))

;; The entry point: check a program's trees, in the initial environment
;; written `standard`. What each definition and expression is, in order,
;; or the first error.
(define check-program (subr checks ((listof syn @s) (listof top @a)) k-result)
  (lambda (standard forms)
    (prompt k-tag
      (begin (k-reset) (k-standard standard) (k-ahead forms) (k-ok (k-forms forms nil)))
      (lambda (r) r))))
