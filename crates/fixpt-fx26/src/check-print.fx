;;; The checker, in FX-26: types and effects shown as the Rust checker shows
;;; them.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ printing

(define k-region-show (subr (maxeff (read @globals) (read @t)) (k-region) string)
  (lambda (r) (tagcase r (r-const (n) (symbol->string n)) (r-fresh (i n) n) (r-var (v) (symbol->string (k-dvar-name v))) (r-frozen (p f)
                  (let ((word (if f "acyclic" "const")))
                    (if (< p 0) word (k-cat5 "(" word " " (symbol->string (k-dvar-name p)) ")")))) (r-heap () "heap")
                  (r-global (g) (k-cat3 "(globals " (symbol->string g) ")")) (r-globals () "@globals"))))
(define k-atom-show (subr (maxeff (read @globals) (read @t)) (k-atom) string)
  (lambda (a)
    (letrec ((one (subr (maxeff (read @globals) (read @t)) (string k-region) string) (lambda (op r) (k-cat5 "(" op " " (k-region-show r) ")"))))
      (tagcase a
        (a-read (r) (one "read" r)) (a-write (r) (one "write" r)) (a-alloc (r) (one "alloc" r))
        (a-goto (r) (one "goto" r)) (a-comefrom (r) (one "comefrom" r)) (a-await (r) (one "await" r))
        (a-spin () "spin")
        (a-var (v) (symbol->string (k-dvar-name v)))))))
(define k-atoms-show (subr (maxeff (read @globals) (read @t)) (k-eff) string)
  (lambda (e) (if (null? e) "" (string-append (string-append " " (k-atom-show (car e))) (k-atoms-show (cdr e))))))
(define k-strings-append (subr (read @globals) ((listof string acyclic) (listof string acyclic)) (listof string acyclic))
  (lambda (xs ys) (if (null? xs) ys (the (listof string acyclic) (cons (car xs) (k-strings-append (cdr xs) ys))))))
(define k-strings-spaced (subr (read @globals) ((listof string acyclic)) string)
  (lambda (xs) (if (null? xs) "" (string-append (string-append " " (car xs)) (k-strings-spaced (cdr xs))))))
;; The names of the globals `e` reads (`op` 0) or writes (1), in order, each
;; after a space.
(define k-globals-shown (subr (maxeff (read @globals) (read @t)) (k-eff int) string)
  (lambda (e op)
    (if (null? e)
        ""
        (let ((g (tagcase (car e)
                   (a-read (r) (if (= op 0) (tagcase r (r-global (g) (string-append " " (symbol->string g))) (else y "")) ""))
                   (a-write (r) (if (= op 1) (tagcase r (r-global (g) (string-append " " (symbol->string g))) (else y "")) ""))
                   (else y ""))))
          (string-append g (k-globals-shown (cdr e) op))))))
(define k-one-global? (subr pure (k-atom) bool)
  (lambda (a)
    (tagcase a
      (a-read (r) (tagcase r (r-global (g) #t) (else y #f)))
      (a-write (r) (tagcase r (r-global (g) #t) (else y #f)))
      (else y #f))))
;; Whether `a` is on globals' bindings, which are never masked.
(define k-globals-atom? (subr (read @globals) (k-atom) bool)
  (lambda (a) (and (k-has-region? a) (tagcase (k-atom-region a) (r-global (g) #t) (r-globals () #t) (else y #f)))))
;; The atoms shown, reads, or writes, of several globals being one atom:
;; `(read (globals f g))`.
(define k-atom-strings (subr (maxeff (read @globals) (read @t)) (k-eff) (listof string acyclic))
  (lambda (e)
    (letrec ((others (subr (maxeff (read @globals) (read @t)) (k-eff) (listof string acyclic))
                       (lambda (e)
                         (cond ((null? e) nil)
                               ((k-one-global? (car e)) (others (cdr e)))
                               (else (the (listof string acyclic) (cons (k-atom-show (car e)) (others (cdr e))))))))
             (grouped (subr (maxeff (read @globals) (read @t)) (string string) (listof string acyclic))
                        (lambda (op names) (if (string=? names "") nil (the (listof string acyclic) (cons (k-cat5 "(" op " (globals" names "))") nil))))))
      (k-strings-append (others e) (k-strings-append (grouped "read" (k-globals-shown e 0)) (grouped "write" (k-globals-shown e 1)))))))
;; `pure`, a single atom, or `…`.
(define k-show-effect (subr (maxeff (read @globals) (read @t)) (k-eff) string)
  (lambda (e)
    (let ((xs (k-atom-strings e)))
      (cond ((null? xs) "pure")
            ((null? (cdr xs)) (car xs))
            (else (k-cat3 "(maxeff" (k-strings-spaced xs) ")"))))))

(define k-kind-name (subr pure (int) string)
  (lambda (k) (cond ((= k 0) "region") ((= k 1) "effect") ((= k 3) "place") ((= k 4) "data") ((= k 5) "size") ((= k 6) "conv") (else "type"))))
;; A convention as a program writes it.
(define k-conv-show (subr (maxeff (read @globals) (read @t)) (k-conv) string)
  (lambda (c)
    (tagcase c (cv-cellular () "cellular") (cv-native () "native") (cv-fx () "fx") (cv-var (v) (symbol->string (k-dvar-name v))))))
;; The program's convention: what a subroutine type that names none has,
;; and what a convention nothing solves defaults to. Cellular, unless a
;; driver says otherwise (`--calling-convention`).
(define k-conv-default (ref k-conv @t) (new (cv-cellular)))
;; For a driver: whether the program's convention is native.
(define check-conv-native! (subr (maxeff (read @globals) (write @t)) (bool) unit)
  (lambda (on) (set k-conv-default (if on (cv-native) (cv-cellular)))))
;; A convention as a number: one of FX-26's own, or its binder.
(define k-conv-code (subr pure (k-conv) int)
  (lambda (c) (tagcase c (cv-cellular () -1) (cv-native () -2) (cv-fx () -3) (cv-var (v) v))))
(define k-conv=? (subr (read @globals) (k-conv k-conv) bool)
  (lambda (a b) (= (k-conv-code a) (k-conv-code b))))
;; As Rust's `{:?}` writes a kind.
(define k-kind-debug (subr pure (int) string)
  (lambda (k) (cond ((= k 0) "Region") ((= k 1) "Effect") ((= k 3) "Place") ((= k 4) "Data") ((= k 5) "Size") ((= k 6) "Conv") (else "Type"))))
;; Whether a region is a place: a variable bound as one.
(define k-place? (subr (maxeff (read @globals) (read @t)) (k-region) bool)
  (lambda (r) (tagcase r (r-var (v) (k-place-var? v)) (r-heap () #t) (else x #f))))

;; The name `define-type` gave `t`, innermost first: each name's innermost
;; binding only.
(define k-abbrev-in (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-scope k-names int) (listof string acyclic))
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
(define k-show-binders (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-binders) (listof string acyclic))
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (b (k-bound-of v))
               (named (k-cat3 (symbol->string (k-dvar-name v)) " " (k-kind-name (extract (car bs) 2)))))
          (cons (if (null? b) (k-cat3 "(" named ")") (k-cat5 "(" named " " (k-region-show (car b)) ")"))
                (k-show-binders (cdr bs)))))))

;; How deep `t` is in `path`, newest first: its place from the root, from 1.
(define k-depth-of (subr (maxeff (read @globals) (read @t)) (k-ids int) int)
  (lambda (path t) (if (= (car path) t) (k-length path) (k-depth-of (cdr path) t))))
;; Whether `name` occurs in `s` as a symbol of its own.
(define k-mentions-token? (subr (maxeff (read @globals) spin) (string string) bool)
  (lambda (s name)
    (or (>= (k-find-sub s (k-cat3 " " name " ") 0) 0)
        (or (>= (k-find-sub s (k-cat3 " " name ")") 0) 0)
            (or (>= (k-find-sub s (k-cat3 "(" name " ") 0) 0)
                (>= (k-find-sub s (k-cat3 "(" name ")") 0) 0))))))
;; Sizes: a literal, `finite`, one more or less, and whether one list's
;; size is another's.
(define k-size-lit (subr (read @globals) (int) k-size) (lambda (k) (sz-lin k nil)))
;; The literal a size is, or -1.
(define k-size-as-lit (subr pure (k-size) int)
  (lambda (z) (tagcase z (sz-lin (k ts) (if (null? ts) k -1)) (else y -1))))
(define k-size-plus (subr (read @globals) (k-size int) k-size)
  (lambda (z d) (tagcase z (sz-lin (k ts) (sz-lin (+ k d) ts)) (else y z))))
(define k-terms=? (subr (read @globals) ((listof (pairof int int acyclic) acyclic) (listof (pairof int int acyclic) acyclic)) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys)) (= (car (car xs)) (car (car ys))) (= (cdr (car xs)) (cdr (car ys))) (k-terms=? (cdr xs) (cdr ys))))))
(define k-size=? (subr (read @globals) (k-size k-size) bool)
  (lambda (a b)
    (tagcase a
      (sz-finite () (tagcase b (sz-finite () #t) (else y #f)))
      (sz-lin (k ts) (tagcase b (sz-lin (k2 ts2) (and (= k k2) (k-terms=? ts ts2))) (else y #f))))))

(define k-map-find (subr (maxeff (read @globals) (read @t)) (k-map int) k-map)
  (lambda (m v) (cond ((null? m) nil) ((= (car (car m)) v) m) (else (k-map-find (cdr m) v)))))
;; Linear sizes (`src/sizes.rs`): a variable; `a + c·b`; `v` replaced.
(define-type k-terms (listof (pairof int int acyclic) acyclic))
(define k-size-var (subr (read @globals) (int) k-size) (lambda (v) (sz-lin 0 (the k-terms (cons (cons v 1) nil)))))
;; `xs + c·ys`, terms in variable order, none zero.
(define k-terms-add (subr (read @globals) (k-terms k-terms int) k-terms)
  (lambda (xs ys c)
    (cond ((null? ys) xs)
          ((null? xs) (let ((n (* c (cdr (car ys)))) (rest (k-terms-add xs (cdr ys) c)))
                        (if (= n 0) rest (the k-terms (cons (cons (car (car ys)) n) rest)))))
          ((< (car (car xs)) (car (car ys))) (the k-terms (cons (car xs) (k-terms-add (cdr xs) ys c))))
          ((> (car (car xs)) (car (car ys)))
           (let ((n (* c (cdr (car ys)))) (rest (k-terms-add xs (cdr ys) c)))
             (if (= n 0) rest (the k-terms (cons (cons (car (car ys)) n) rest)))))
          (else (let ((n (+ (cdr (car xs)) (* c (cdr (car ys))))) (rest (k-terms-add (cdr xs) (cdr ys) c)))
                  (if (= n 0) rest (the k-terms (cons (cons (car (car xs)) n) rest))))))))
(define k-size-add-scaled (subr (read @globals) (k-size k-size int) k-size)
  (lambda (a b c)
    (tagcase a
      (sz-lin (k ts) (tagcase b (sz-lin (k2 ts2) (sz-lin (+ k (* c k2)) (k-terms-add ts ts2 c))) (else y (sz-finite))))
      (else y (sz-finite)))))
(define k-coef-of (subr (read @globals) (k-terms int) int)
  (lambda (ts v) (cond ((null? ts) 0) ((= (car (car ts)) v) (cdr (car ts))) (else (k-coef-of (cdr ts) v)))))
(define k-size-replace (subr (read @globals) (k-size int k-size) k-size)
  (lambda (s v by)
    (tagcase s
      (sz-lin (k ts)
        (let ((c (k-coef-of ts v)))
          (if (= c 0) s (k-size-add-scaled (k-size-add-scaled s (k-size-var v) (- 0 c)) by c))))
      (else y (sz-finite)))))
;; What the branches being checked have learned about sizes: `lin = 0`
;; (`#t`) or `lin ≥ 0`, newest first.
(define-type k-size-fact (productof (1 k-size) (2 bool)))
(define k-size-facts (ref (listof k-size-fact acyclic) @t) (new nil))
;; `s` with each variable an equality determines rewritten away, oldest
;; fact first.
(define k-reduced (subr (maxeff (read @globals) (read @t)) (k-size) k-size)
  (lambda (s)
    (letrec ((go (subr (read @globals) (k-size (listof k-size-fact acyclic)) k-size)
                   (lambda (s fs)
                     (if (null? fs)
                         s
                         (go (let ((f (car fs)))
                               (if (not (extract f 2))
                                   s
                                   (tagcase (extract f 1)
                                     (sz-lin (k ts)
                                       (letrec ((unit (subr (read @globals) (k-terms) k-terms)
                                                      (lambda (xs) (cond ((null? xs) xs)
                                                                         ((or (= (cdr (car xs)) 1) (= (cdr (car xs)) -1)) xs)
                                                                         (else (unit (cdr xs)))))))
                                         (let ((u (unit ts)))
                                           (if (null? u)
                                               s
                                               (let* ((v (car (car u))) (c (cdr (car u)))
                                                      (rest (k-size-add-scaled (extract f 1) (k-size-var v) (- 0 c)))
                                                      (by (k-size-add-scaled (k-size-lit 0) rest (- 0 c))))
                                                 (k-size-replace s v by))))))
                                     (else y s))))
                             (cdr fs))))))
      (go s (the (listof k-size-fact acyclic) (reverse (get k-size-facts)))))))
;; Whether a size is plainly non-negative: every size is a natural.
(define k-plainly-nonneg? (subr (read @globals) (k-size) bool)
  (lambda (s)
    (tagcase s
      (sz-lin (k ts) (and (>= k 0) (letrec ((all (subr (read @globals) (k-terms) bool) (lambda (xs) (or (null? xs) (and (>= (cdr (car xs)) 0) (all (cdr xs))))))) (all ts))))
      (else y #f))))
;; Whether the facts show `a ≥ 0`: plainly, or with a fact `f ≥ 0` to spare.
(define k-size-nonneg? (subr (maxeff (read @globals) (read @t)) (k-size) bool)
  (lambda (a0)
    (let ((a (k-reduced a0)))
      (or (k-plainly-nonneg? a)
          (letrec ((any (subr (maxeff (read @globals) (read @t)) ((listof k-size-fact acyclic)) bool)
                        (lambda (fs)
                          (and (not (null? fs))
                               (or (and (not (extract (car fs) 2))
                                        (k-plainly-nonneg? (k-size-add-scaled a (k-reduced (extract (car fs) 1)) -1)))
                                   (any (cdr fs)))))))
            (any (the (listof k-size-fact acyclic) (reverse (get k-size-facts)))))))))
;; Whether the facts show `a = b`.
(define k-size-eq? (subr (maxeff (read @globals) (read @t)) (k-size k-size) bool)
  (lambda (a b)
    (tagcase a
      (sz-finite () (tagcase b (sz-finite () #t) (else y #f)))
      (else y (tagcase b (sz-finite () #f) (else w (k-size=? (k-reduced (k-size-add-scaled a b -1)) (k-size-lit 0))))))))
;; The size of the tail of a list of size `n`: one less, where the facts
;; show `n ≥ 1`; `finite` otherwise.
(define k-tail-size (subr (maxeff (read @globals) (read @t)) (k-size) k-size)
  (lambda (n) (tagcase n (sz-finite () n) (else y (if (k-size-nonneg? (k-size-plus n -1)) (k-size-plus n -1) (sz-finite))))))
;; Whether a list of size `m` is one of size `n`: the facts show them
;; equal, or `n` is `finite`.
(define k-size-le? (subr (maxeff (read @globals) (read @t)) (k-size k-size) bool)
  (lambda (m n) (or (tagcase n (sz-finite () #t) (else y #f)) (k-size-eq? m n))))
;; `s` with `m`'s sizes for its variables.
(define k-subst-size (subr (maxeff (read @globals) (read @t)) (k-size k-map) k-size)
  (lambda (s m)
    (tagcase s
      (sz-lin (k ts)
        (letrec ((go (subr (maxeff (read @globals) (read @t)) (k-size k-terms) k-size)
                       (lambda (out xs)
                         (if (null? xs)
                             out
                             (let ((f (k-map-find m (car (car xs)))))
                               (go (if (null? f) out (tagcase (cdr (car f)) (dz (by) (k-size-replace out (car (car xs)) by)) (else y out)))
                                   (cdr xs)))))))
          (go s ts)))
      (else y s))))
(define k-show-terms (subr (maxeff (read @globals) (read @t) (alloc @t) spin) ((listof (pairof int int acyclic) acyclic)) (listof string acyclic))
  (lambda (ts)
    (if (null? ts)
        nil
        (let* ((n (symbol->string (k-dvar-name (car (car ts)))))
               (c (cdr (car ts)))
               (x (if (= c 1) n (k-cat5 "(* " (int->string c) " " n ")"))))
          (cons x (k-show-terms (cdr ts)))))))
(define k-show-size (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-size) string)
  (lambda (z)
    (tagcase z
      (sz-finite () "finite")
      (sz-lin (k ts)
        (let ((parts (k-show-terms ts)))
          (cond ((null? parts) (int->string k))
                ((and (null? (cdr parts)) (= k 0)) (car parts))
                ((and (null? (cdr parts)) (< k 0)) (k-cat5 "(- " (car parts) " " (int->string (- 0 k)) ")"))
                ((= k 0) (k-cat3 "(+ " (k-join parts " ") ")"))
                (else (k-cat5 "(+ " (k-join parts " ") " " (int->string k) ")"))))))))
;; `out`, the type a node shows as, as `(mu name out)` if it mentions itself.
(define k-mu-wrap (subr (maxeff (read @globals) spin) (string string) string)
  (lambda (name out) (if (k-mentions-token? out name) (k-cat5 "(mu " name " " out ")") out)))

(define-rec
  (k-show-on (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-ids) string)
    (lambda (t path)
      (let* ((t (k-resolve t)) (name (k-abbrev-in (get k-dscope) nil t)))
        (if (null? name) (k-show-body t path) (car name)))))
  (k-show-list (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-ids k-ids) (listof string acyclic))
    (lambda (ts path) (if (null? ts) nil (cons (k-show-on (car ts) path) (k-show-list (cdr ts) path)))))
  (k-show-parts (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-parts k-ids) string)
    (lambda (ps path)
      (if (null? ps)
          ""
          (string-append (k-cat5 " (" (symbol->string (extract (car ps) 1)) " " (k-show-on (extract (car ps) 2) path) ")")
                         (k-show-parts (cdr ps) path)))))
  ;; A node met again on the way down is a cycle: named by its depth, and
  ;; written `(mu %d …)` where the cycle starts.
  (k-show-descs (subr (maxeff (read @globals) (read @t) (alloc @t) spin) ((listof k-desc acyclic) k-ids) (listof string acyclic))
    (lambda (ds p)
      (if (null? ds)
          nil
          (let ((x (tagcase (car ds) (dt (t) (k-show-on t p)) (dr (r) (k-region-show r)) (de (e) (k-show-effect e)) (dz (z) (k-show-size z)) (dc (c) (k-conv-show c)))))
            (cons x (k-show-descs (cdr ds) p))))))
  (k-show-body (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-ids) string)
    (lambda (t path)
      (if (k-has-id? path t)
          (string-append "%" (int->string (k-depth-of path t)))
          (let ((p (the k-ids (cons t path))))
            (k-mu-wrap (string-append "%" (int->string (k-length p)))
            (tagcase (k-get t)
              (ty-base (s) (symbol->string s))
              (ty-void () "void")
              (ty-var (v) (symbol->string (k-dvar-name v)))
              (ty-link (x) "?")
              (ty-subr (e ps r cv)
                ;; The convention only where it is not the program's.
                (k-cat5 (k-cat4 "(subr " (if (k-conv=? cv (get k-conv-default)) "" (k-cat3 "(conv " (k-conv-show cv) ") ")) (k-show-effect e) " (") (k-join (k-show-list ps p) " ") ") " (k-show-on r p) ")"))
              (ty-poly (bs body) (k-cat5 "(poly (" (k-join (k-show-binders bs) " ") ") " (k-show-on body p) ")"))
              (ty-ref (a r) (k-cat5 "(ref " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-product (ps) (k-cat3 "(productof" (k-show-parts ps p) ")"))
              (ty-sum (ps) (k-cat3 "(sumof" (k-show-parts ps p) ")"))
              (ty-array (a r) (k-cat5 "(arrayof " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-icell (a r) (k-cat5 "(icell " (k-show-on a p) " " (k-region-show r) ")"))
              (ty-place (r) (k-cat3 "(place " (k-region-show r) ")"))
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
                        ") " (string-append (k-region-show r) ")")))
              (ty-nlist (e z r)
                (tagcase r
                  (r-frozen (q f)
                    (if (>= q 0)
                        (k-cat5 "(nlist " (k-show-on e p) " " (k-show-size z) (k-cat3 " " (symbol->string (k-dvar-name q)) ")"))
                        (k-cat5 "(nlist " (k-show-on e p) " " (k-show-size z) ")")))
                  (else y (k-cat5 "(nlist " (k-show-on e p) " " (k-show-size z) ")"))))
              (ty-nat (z) (tagcase z (sz-finite () "nat") (else y (k-cat3 "(nat " (k-show-size z) ")"))))
              (ty-named (g ds)
                (let ((name (symbol->string (extract (k-gen-of g) 1))))
                  (if (null? ds) name (k-cat5 "(" name " " (k-join (k-show-descs ds p) " ") ")")))))))))))

;; A type. One `define-type` named prints as its name; any other recursive
;; type as `(mu %d …)`, `%d` naming the cycle.
(define k-show-ty (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) string)
  (lambda (t) (k-show-on t nil)))
