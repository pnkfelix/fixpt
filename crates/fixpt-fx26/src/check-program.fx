;;; The checker, in FX-26: programs, form by form, and proofs.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ programs

;; The initial environment: `(name type)` for each binding.
(define k-standard (subr (maxeff checks spin) ((listof syn acyclic)) unit)
  (lambda (entries)
    (if (null? entries)
        #u
        (let ((pair (k-items (car entries) "a standard binding")))
          ;; `vsubr`'s declaration first: generative type 0, as in the Rust
          ;; checker (`check::VSUBR`), with no `up-` or `down-`.
          (if (and (syn-symbol? (car pair)) (string=? (syn-name (car pair)) "define-generative"))
              (begin (k-define-generative (k-nth pair 1) (k-nth pair 2)) (k-standard (cdr entries)))
              (let ((t (k-parse-type (k-nth pair 1))) (n (k-name-of (car pair) "a name")))
                (begin (k-bind n t) (set k-std (cons (cons n t) (get k-std))) (k-standard (cdr entries)))))))))

(define-type k-out (listof string acyclic))
(define k-push-binders (subr kstate (k-binders) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (let ((v (extract (car bs) 1)))
          (begin (k-push-desc (k-dvar-name v) (ds-var v (extract (car bs) 2))) (k-push-binders (cdr bs)))))))

;; Put the binders of every `poly` at the top of `t` in scope for reading.
(define k-bind-signature (subr (maxeff kstate spin) (int) unit)
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
;;; ------------------------------------------------------------ proofs
;;; A definition whose declared type is `(proves …)` is a lemma once its
;;; body is a guarded structural identity (`src/lemma.rs`): it takes apart
;;; only what it was given, rebuilds the same tags and labels, applies
;;; hypotheses and proofs only to what was given at the same place, and uses
;;; itself only under a constructor.

;; A place in what a proof was given: a variable and the labels extracted.
(define-type k-pos (pairof symbol (listof symbol acyclic) @t))
(define k-syms=? (subr (read @globals) ((listof symbol acyclic) (listof symbol acyclic)) bool)
  (lambda (xs ys) (if (null? xs) (null? ys) (and (not (null? ys)) (symbol=? (car xs) (car ys)) (k-syms=? (cdr xs) (cdr ys))))))
(define k-append-sym (subr (maxeff (read @globals) (alloc @t)) ((listof symbol acyclic) symbol) (listof symbol acyclic))
  (lambda (xs l) (if (null? xs) (the (listof symbol acyclic) (cons l nil)) (the (listof symbol acyclic) (cons (car xs) (k-append-sym (cdr xs) l))))))
;; Whether `f` names a generative type's conversion.
(define k-names-conversion? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) bool)
  (lambda (f)
    (tagcase (k-under f)
      (x-var (s a b) (let ((t (k-lookup s))) (and (>= t 0) (k-named-has? (get k-conversions) s t))))
      (else y #f))))
;; `e` under ascriptions and conversions, which are the identity.
(define k-strip-conv (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) kx)
  (lambda (e)
    (tagcase e
      (x-the (t x a b) (k-strip-conv x))
      (x-app (f args a b) (if (and (k-sc-one? args) (k-names-conversion? f)) (k-strip-conv (car args)) e))
      (else y e))))
;; The place `e` names, if it names one (none or one).
(define k-place-of (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx) (listof k-pos acyclic))
  (lambda (e)
    (tagcase (k-strip-conv e)
      (x-var (s a b) (the (listof k-pos acyclic) (cons (cons s nil) nil)))
      (x-extract (x l a b)
        (let ((p (k-place-of x))) (if (null? p) nil (the (listof k-pos acyclic) (cons (cons (car (car p)) (k-append-sym (cdr (car p)) l)) nil)))))
      (else y nil))))
(define k-at? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (kx k-pos) bool)
  (lambda (e at)
    (let ((p (k-place-of e))) (and (not (null? p)) (symbol=? (car (car p)) (car at)) (k-syms=? (cdr (car p)) (cdr at))))))
;; `t` with generative types unfolded, as far as they go.
(define k-unfold-all (subr (maxeff kstate spin) (int int) int)
  (lambda (t n)
    (if (= n 0)
        t
        (let ((t (k-resolve t))) (tagcase (k-get t) (ty-named (g ds) (k-unfold-all (k-unfold g ds) (- n 1))) (else y t))))))
(define k-proof-fail (subr checks (kx string string) void)
  (lambda (e want why) (k-fail (k-cat4 "this does not prove " want ": " why) (k-start e) (k-end e))))
(define k-lemma-name? (subr (maxeff (read @globals) (read @t) spin) ((listof k-lemma acyclic) symbol int) bool)
  (lambda (ls s t) (and (not (null? ls)) (or (k-named-has? (extract (car ls) 5) s t) (k-lemma-name? (cdr ls) s t)))))
(define k-names-meet? (subr (maxeff (read @globals) (read @t)) (k-names k-names) bool)
  (lambda (xs ys) (and (not (null? xs)) (or (k-has-name? ys (car xs)) (k-names-meet? (cdr xs) ys)))))
(define k-last (subr (maxeff (read @globals) (read @t)) (kxs) kx) (lambda (xs) (if (null? (cdr xs)) (car xs) (k-last (cdr xs)))))
(define k-but-last (subr (maxeff (read @globals) (read @t) (alloc @t)) (kxs) kxs)
  (lambda (xs) (if (null? (cdr xs)) nil (the kxs (cons (car xs) (k-but-last (cdr xs)))))))
(define-rec
  ;; Whether `e0` rebuilds, as the identity, what was given at `at`, of type
  ;; `ty`; `guarded` once something has been rebuilt above it.
  (k-rebuild (subr (maxeff checks spin) (kx k-pos int bool symbol k-names string) unit)
    (lambda (e0 at ty guarded me hyps want)
      (let ((e (k-strip-conv e0)))
        (if (k-at? e at)
            #u
            (tagcase e
              (x-app (f args a b)
                (let ((op (tagcase (k-under f) (x-var (s fa fb) (the k-names (cons s nil))) (else y (the k-names nil)))))
                  (if (null? op)
                      (k-proof-fail e want "a proof may call only its hypotheses, itself, or another proof")
                      (let ((f (car op)))
                        (if (k-has-name? hyps f)
                            (if (and (k-sc-one? args) (k-at? (car args) at))
                                #u
                                (k-proof-fail e want "a hypothesis applies only to what was given here"))
                            (let* ((me? (symbol=? f me))
                                   (t (k-lookup f))
                                   (lemma? (and (>= t 0) (k-lemma-name? (get k-lemmas) f t))))
                              (cond ((and (not me?) (not lemma?))
                                     (k-proof-fail e want "a proof may call only its hypotheses, itself, or another proof"))
                                    ((and me? (not guarded))
                                     (k-proof-fail e want "it uses itself before rebuilding anything, which proves nothing"))
                                    ((null? args) (k-proof-fail e want "a proof applies to something"))
                                    (else
                                     (let ((last (k-last args)))
                                       (if (k-at? last at)
                                           (k-proof-coercions (k-but-last args) guarded me hyps want)
                                           (k-proof-fail last want "a proof applies only to what was given here")))))))))))
              (x-tagcase (sc arms els a b)
                (if (not (k-at? sc at))
                    (k-proof-fail sc want "a proof takes apart only what was given here")
                    (tagcase (k-get (k-unfold-all ty 64))
                      (ty-sum (vs)
                        (begin
                          (k-rebuild-arms arms vs at me hyps want)
                          (if (null? els)
                              #u
                              (let ((y (extract (car els) 1)) (body (extract (car els) 2)))
                                (if (or (symbol=? y me) (k-has-name? hyps y))
                                    (k-proof-fail body want "a proof may not rebind the names it relies on")
                                    (k-rebuild body (cons y nil) ty guarded me hyps want))))))
                      (else z (k-proof-fail sc want "what is given here is not a sum")))))
              (x-product (gs a b)
                (tagcase (k-get (k-unfold-all ty 64))
                  (ty-product (fs)
                    (if (k-same-labels? gs fs)
                        (k-rebuild-paths gs fs at me hyps want)
                        (k-proof-fail e want "a product is rebuilt with its fields, in order")))
                  (else z (k-proof-fail e want "what is given here is not a product"))))
              (else y (k-proof-fail e want "a proof may only take apart and rebuild what it was given")))))))
  (k-rebuild-arms (subr (maxeff checks spin) (k-arms k-parts k-pos symbol k-names string) unit)
    (lambda (arms vs at me hyps want)
      (if (null? arms)
          #u
          (let* ((arm (car arms)) (tag (extract arm 1)) (fields? (extract arm 2)) (names (extract arm 3)) (body0 (extract arm 4)))
            (begin
              (if (or (k-has-name? names (car at)) (k-has-name? names me) (k-names-meet? names hyps))
                  (k-proof-fail body0 want "a proof may not rebind the names it relies on")
                  #u)
              (let ((vt (k-part-find vs tag)))
                (if (< vt 0)
                    (k-proof-fail body0 want "an arm for a tag that is not there")
                    (let ((body (k-strip-conv body0)))
                      (tagcase body
                        (x-sum (t2 inner sa sb)
                          (if (not (symbol=? t2 tag))
                              (k-proof-fail body0 want "each arm rebuilds its own tag")
                              (if fields?
                                  (tagcase (k-get (k-unfold-all vt 64))
                                    (ty-product (fs)
                                      (let ((inner (k-strip-conv inner)))
                                        (tagcase inner
                                          (x-product (gs pa pb)
                                            (if (and (= (k-length gs) (k-length fs)) (= (k-length names) (k-length fs)) (k-same-labels? gs fs))
                                                (k-rebuild-fields gs fs names me hyps want)
                                                (k-proof-fail inner want "each arm rebuilds its fields, in order")))
                                          (else z (k-proof-fail inner want "each arm rebuilds its fields")))))
                                    (else z (k-proof-fail body0 want "fields of something that is not a product")))
                                  (k-rebuild inner (cons (car names) nil) vt #t me hyps want))))
                        (else z (k-proof-fail body0 want "each arm rebuilds its own tag"))))))
              (k-rebuild-arms (cdr arms) vs at me hyps want))))))
  (k-rebuild-fields (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-parts k-names symbol k-names string) unit)
    (lambda (gs fs xs me hyps want)
      (if (null? gs)
          #u
          (begin (k-rebuild (extract (car gs) 2) (cons (car xs) nil) (extract (car fs) 2) #t me hyps want)
                 (k-rebuild-fields (cdr gs) (cdr fs) (cdr xs) me hyps want)))))
  (k-rebuild-paths (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 kx)) acyclic) k-parts k-pos symbol k-names string) unit)
    (lambda (gs fs at me hyps want)
      (if (null? gs)
          #u
          (begin (k-rebuild (extract (car gs) 2) (cons (car at) (k-append-sym (cdr at) (extract (car gs) 1))) (extract (car fs) 2) #t me hyps want)
                 (k-rebuild-paths (cdr gs) (cdr fs) at me hyps want)))))
  ;; A coercion a proof passes to a proof: a hypothesis, a proof, itself
  ;; (under a constructor), or a lambda whose parameter is annotated and
  ;; whose body rebuilds it.
  (k-proof-coercion (subr (maxeff checks spin) (kx bool symbol k-names string) unit)
    (lambda (c0 guarded me hyps want)
      (let ((c (k-strip-conv c0)))
        (tagcase c
          (x-var (s a b)
            (cond ((k-has-name? hyps s) #u)
                  ((symbol=? s me) (if guarded #u (k-proof-fail c want "it passes itself on before rebuilding anything")))
                  ((let ((t (k-lookup s))) (and (>= t 0) (k-lemma-name? (get k-lemmas) s t))) #u)
                  (else (k-proof-fail c want "a proof is given only hypotheses, proofs, or coercions that rebuild"))))
          (x-lambda (ps body a b)
            (if (and (not (null? ps)) (null? (cdr ps)) (not (null? (extract (car ps) 2))))
                (let ((x (extract (car ps) 1)))
                  (if (or (symbol=? x me) (k-has-name? hyps x))
                      (k-proof-fail c want "a proof may not rebind the names it relies on")
                      (k-rebuild body (cons x nil) (car (extract (car ps) 2)) guarded me hyps want)))
                (k-proof-fail c want "a coercion given to a proof takes one parameter, with its type written")))
          (else y (k-proof-fail c want "a proof is given only hypotheses, proofs, or coercions that rebuild"))))))
  (k-proof-coercions (subr (maxeff checks spin) (kxs bool symbol k-names string) unit)
    (lambda (cs guarded me hyps want)
      (if (null? cs) #u (begin (k-proof-coercion (car cs) guarded me hyps want) (k-proof-coercions (cdr cs) guarded me hyps want))))))
(define k-under-abstractions (subr (maxeff (read @globals) spin) (kx) kx)
  (lambda (x) (tagcase x (x-plambda (bs body a b) (k-under-abstractions body)) (x-the (t body a b) (k-under-abstractions body)) (else y x))))
(define k-param-names-first (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (productof (1 symbol) (2 k-ids)) acyclic) int) k-names)
  (lambda (ps n) (if (= n 0) nil (the k-names (cons (extract (car ps) 1) (k-param-names-first (cdr ps) (- n 1)))))))

;; Whether `e`, the body of `name`, proves lemma `l`; an error where not.
(define k-check-proof (subr (maxeff checks spin) (k-lemma symbol kx) unit)
  (lambda (l name e)
    (let* ((want (k-cat5 "`" (k-show-ty (extract l 2)) " ≤ " (k-show-ty (extract l 3)) "`"))
           (x (k-under-abstractions e)))
      (tagcase x
        (x-lambda (ps body a b)
          (let ((n (k-length (extract l 4))))
            (if (not (= (k-length ps) (+ n 1)))
                (k-fail (k-cat3 "a proof of " want " takes a coercion for each hypothesis, then what it proves of") a b)
                (k-rebuild body (cons (extract (k-nth ps n) 1) nil) (extract l 2) #f name (k-param-names-first ps n) want))))
        (else y (k-fail (k-cat3 "a proof of " want " is a lambda") (k-start e) (k-end e)))))))
;; The generative type `name` may see inside, as one of its conversions, or
;; -1; no longer, once asked.
(define k-take-inside (subr kstate (symbol) int)
  (lambda (name)
    (letrec ((find (subr (maxeff (read @globals) (read @t)) ((listof (pairof symbol int @t) acyclic)) int)
                   (lambda (xs) (cond ((null? xs) -1) ((symbol=? (car (car xs)) name) (cdr (car xs))) (else (find (cdr xs))))))
             (drop (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof (pairof symbol int @t) acyclic)) (listof (pairof symbol int @t) acyclic))
                   (lambda (xs)
                     (cond ((null? xs) xs)
                           ((symbol=? (car (car xs)) name) (cdr xs))
                           (else (the (listof (pairof symbol int @t) acyclic) (cons (car xs) (drop (cdr xs)))))))))
      (let ((g (find (get k-inside))))
        (begin (if (>= g 0) (set k-inside (drop (get k-inside))) #u) g)))))
(define k-declare (subr (maxeff checks spin) (top) unit)
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
      (t-define-generative (head rep a b)
        (let* ((name (k-define-generative head rep)) (g (- (get k-ngens) 1)) (n (symbol->string name)))
          ;; Only its own conversions, which follow, see inside it.
          (set k-inside (cons (cons (string->symbol (string-append "down-" n)) g)
                              (cons (cons (string->symbol (string-append "up-" n)) g) (get k-inside))))))
      (else y #u))))

;; The first pass: abbreviations, so that types can refer to each other in
;; any order. Values cannot: a definition sees only those before it.
(define k-ahead (subr (maxeff checks spin) ((listof top acyclic)) unit)
  (lambda (forms)
    (if (null? forms)
        #u
        (begin (k-declare (car forms)) (k-ahead (cdr forms))))))

(define k-line (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int k-eff) string)
  (lambda (t e) (k-cat3 (k-show-ty t) " ! " (k-show-effect e))))
(define k-push-lines (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof string acyclic) k-out) k-out)
  (lambda (lines out) (if (null? lines) out (k-push-lines (cdr lines) (cons (car lines) out)))))
(define k-rec-types (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) k-ids)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((t (k-parse-type (extract (car bs) 2))) (bound (k-bind-global (extract (car bs) 1) t))
               (noted (k-note-known (extract (car bs) 1) 0)))
          (cons t (k-rec-types (cdr bs)))))))
;; Each lambda, read under its signature: a lambda, or an error.
(define k-rec-lambdas (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) k-ids) k-group)
  (lambda (bs ts)
    (if (null? bs)
        nil
        (let* ((name (extract (car bs) 1))
               (t (car ts))
               (saved (get k-dscope))
               (signed (k-bind-signature t))
               (x (k-resolve-exp (extract (car bs) 3)))
               (restored (set k-dscope saved))
               (checked (if (k-lambda? x) #u (k-fail (k-letrec-not-lambda name) (k-start x) (k-end x)))))
          (cons (product (1 name) (2 t) (3 x)) (k-rec-lambdas (cdr bs) (cdr ts)))))))
(define k-rec-check (subr (maxeff checks spin) (k-group) (listof string acyclic))
  (lambda (g)
    (if (null? g)
        nil
        (let* ((name (extract (car g) 1))
               (t (extract (car g) 2))
               (e (k-check-declared name t (extract (car g) 3)))
               (line (k-cat4 "define " (symbol->string name) " : " (k-line t e)))
               (rest (k-rec-check (cdr g))))
          (cons line rest)))))

;; A `define-rec` group's free variables.
(define k-group-free (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-group k-names) k-names)
  (lambda (g out) (if (null? g) out (k-group-free (cdr g) (k-free-into (extract (car g) 3) nil out)))))
;; `(define-rec (name type lambda) …)`: every name in scope first, then each
;; lambda checked against its type. A line for each.
(define k-define-rec (subr (maxeff checks spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) (listof string acyclic))
  (lambda (bs)
    (let* ((rsaved (get k-recursive))
           (g (k-rec-lambdas bs (k-rec-types bs)))
           (u (set k-last-uses (k-group-free g nil)))
           ;; A group whose every run ends needs no `spin`.
           (why (k-termination g))
           (noted (if (string=? why "") #u (begin (k-note-recursive g) (k-note-why g why))))
           (lines (k-rec-check g)))
      (begin (set k-recursive rsaved) lines))))

;;; Redefinition (`top.rs`, `Checker::top_defining`), for files and the REPL
;;; alike: a global's uses always refer to what it is now. A definition of a
;;; name already a global, at a type every use can take (each a subtype of
;;; the old), assigns the global. At any other type it makes a new global,
;;; and every earlier definition that uses the name (and every one that uses
;;; those) is checked again, in order: each that checks is defined again,
;;; by the same rule; each that does not is broken. To keep a value as it
;;; was, a program binds it: `(define d (let ((g g)) …))`.

(define k-rev-runs (subr (read @globals) ((listof k-run acyclic) (listof k-run acyclic)) (listof k-run acyclic))
  (lambda (xs acc) (if (null? xs) acc (k-rev-runs (cdr xs) (the (listof k-run acyclic) (cons (car xs) acc))))))
;; For a driver: what the program checked runs, in order (`compile-checked`,
;; `run-checked`).
(define checked-tops (subr (maxeff (read @globals) (read @t)) () (listof k-run acyclic))
  (lambda () (k-rev-runs (get k-runs) nil)))
(define k-rev-defs (subr (read @globals) ((listof k-def acyclic) (listof k-def acyclic)) (listof k-def acyclic))
  (lambda (xs acc) (if (null? xs) acc (k-rev-defs (cdr xs) (the (listof k-def acyclic) (cons (car xs) acc))))))
(define k-rec-names (subr (read @globals) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) k-names)
  (lambda (bs) (if (null? bs) nil (the k-names (cons (extract (car bs) 1) (k-rec-names (cdr bs)))))))
;; The names a form defines.
(define k-top-names (subr (read @globals) (top) k-names)
  (lambda (form)
    (tagcase form
      (t-define (name ty init a b) (the k-names (cons name nil)))
      (t-define-rec (bs a b) (k-rec-names bs))
      (else y (the k-names nil)))))
;; Whether `n` is a global a definition made.
(define k-defined? (subr (maxeff (read @globals) (read @t)) (symbol) bool)
  (lambda (n)
    (letrec ((go (subr (maxeff (read @globals) (read @t)) ((listof k-def acyclic)) bool)
               (lambda (ds) (and (not (null? ds)) (or (k-has-name? (extract (car ds) 1) n) (go (cdr ds)))))))
      (go (get k-defs)))))
;; The names of `ns` that are globals already, with their types.
(define-type k-olds (listof (pairof symbol int acyclic) acyclic))
(define k-old-types (subr (maxeff (read @globals) (read @t) spin) (k-names) k-olds)
  (lambda (ns)
    (cond ((null? ns) nil)
          ((k-defined? (car ns)) (the k-olds (cons (cons (car ns) (k-lookup-raw (car ns))) (k-old-types (cdr ns)))))
          (else (k-old-types (cdr ns))))))
;; Whether each of them now has a type its old one's uses can take.
(define k-fits-old? (subr (maxeff kstate spin) (k-olds) bool)
  (lambda (os) (or (null? os) (and (k-subtype (k-lookup-raw (car (car os))) (cdr (car os))) (k-fits-old? (cdr os))))))
(define k-names-without (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
  (lambda (xs ns)
    (cond ((null? xs) xs)
          ((k-has-name? ns (car xs)) (k-names-without (cdr xs) ns))
          (else (the k-names (cons (car xs) (k-names-without (cdr xs) ns)))))))
(define k-defs-without (subr (maxeff (read @globals) (read @t)) ((listof k-def acyclic) k-names) (listof k-def acyclic))
  (lambda (ds ns)
    (cond ((null? ds) ds)
          ((k-names-meet? (extract (car ds) 1) ns) (k-defs-without (cdr ds) ns))
          (else (the (listof k-def acyclic) (cons (car ds) (k-defs-without (cdr ds) ns)))))))
;; `form`, which defines `ns`, recorded as their definition now.
(define k-record (subr kstate (top k-names) unit)
  (lambda (form ns)
    (if (null? ns)
        #u
        (set k-defs (the (listof k-def acyclic)
                      (cons (product (1 ns) (2 form) (3 (k-names-without (get k-last-uses) ns))) (k-defs-without (get k-defs) ns)))))))
;; The definitions that use `ns`, and those that use them, and so on,
;; oldest first.
(define k-users-of (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names) (listof k-def acyclic))
  (lambda (ns)
    (letrec ((go (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof k-def acyclic) k-names) (listof k-def acyclic))
               (lambda (ds used)
                 (cond ((null? ds) nil)
                       ((k-names-meet? (extract (car ds) 1) ns) (go (cdr ds) used))
                       ((k-names-meet? (extract (car ds) 3) used)
                        (the (listof k-def acyclic) (cons (car ds) (go (cdr ds) (k-names-onto (extract (car ds) 1) used)))))
                       (else (go (cdr ds) used))))))
      (go (k-rev-defs (get k-defs) nil) ns))))
;; Names as a message shows them: `a`, `b`.
(define k-shown (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-names) string)
  (lambda (ns)
    (letrec ((go (subr (maxeff (read @globals) (alloc @t)) (k-names) (listof string acyclic))
               (lambda (xs) (if (null? xs) nil (the (listof string acyclic) (cons (k-cat3 "`" (symbol->string (car xs)) "`") (go (cdr xs))))))))
      (k-join (go ns) ", "))))
(define k-break-all (subr (maxeff kstate spin) (k-names string) unit)
  (lambda (ns why)
    (if (null? ns)
        #u
        (begin (set k-broken (the (listof k-break acyclic) (cons (product (1 (car ns)) (2 (k-name-depth (car ns))) (3 why)) (get k-broken))))
               (k-break-all (cdr ns) why)))))
(define k-lines-append (subr (read @globals) ((listof string acyclic) (listof string acyclic)) (listof string acyclic))
  (lambda (xs ys) (if (null? xs) ys (the (listof string acyclic) (cons (car xs) (k-lines-append (cdr xs) ys))))))
;; `t`, a `subr` under any `poly`s, with `extra` in its latent effect; -1 if
;; `t` is not one.
(define k-with-latent (subr (maxeff kstate spin) (int k-eff) int)
  (lambda (t extra)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (let ((b (k-with-latent body extra))) (if (< b 0) -1 (k-ty-new (ty-poly bs b)))))
      (ty-subr (e ps r cv) (k-ty-new (ty-subr (k-union e extra) ps r cv)))
      (else y -1))))
;; The atoms of `e` on globals.
(define k-globals-of (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-eff) k-eff)
  (lambda (e) (cond ((null? e) nil) ((k-globals-atom? (car e)) (the k-eff (cons (car e) (k-globals-of (cdr e))))) (else (k-globals-of (cdr e))))))
;; `n`'s innermost binding, now of type `t`.
(define k-rebind-top (subr (maxeff kstate spin) (symbol int) unit)
  (lambda (n t) (table-set! (get k-env) n (cons t (cdr (table-ref (get k-env) n nil))))))
;; `f`'s value, or, if it fails, the error `say` makes of its message.
(define k-saying (subr (maxeff (read @globals) checks spin) ((subr (maxeff checks spin) () k-te) (subr (maxeff checks spin) (string) string)) k-te)
  (lambda (f say)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (k-fail (say m) ea eb))
        (k-ok (xs) (k-fail "k-ok inside" 0 0))))))
;; `(define name type init)`, or, if `star` is not empty,
;; `(define* name type init)`: its line.
(define k-define-typed (subr (maxeff checks spin) (symbol syn (listof syn acyclic) exp) (listof string acyclic))
  (lambda (name written star-syns init)
    ;; A lambda is in scope in itself, as a `letrec`
    ;; binding is; anything else is not.
    (let* ((reset (set k-pending-lemma nil))
           (t (k-parse-type written))
           ;; `define*`: checked as though its type read
           ;; `@globals`, which finds what it reads.
           (star (not (null? star-syns)))
           (tw (if star (k-with-latent t (k-one (a-read (r-globals)))) t))
           (subr-ok (if (< tw 0) (k-sfail "`define*` finds what a procedure reads: its type is a `subr`" written) #u))
           ;; A `proves` type: a lemma, once the body proves it.
           (lemma (get k-pending-lemma))
           (taken (set k-pending-lemma nil))
           (saved (get k-dscope))
           (signed (k-bind-signature t))
           (x (k-resolve-exp init))
           (lambda-ok (if (and star (not (k-lambda? x))) (k-fail "`define*` defines a procedure: a `lambda`" (k-start x) (k-end x)) #u))
           (u (set k-last-uses (k-free-into x nil nil)))
           (restored (set k-dscope saved))
           (bound (if (k-lambda? x) (k-bind-global name t) #u))
           (rsaved (get k-recursive))
           ;; A lambda whose every run ends needs no `spin`.
           (noted (if (k-lambda? x)
                      (begin (k-note-known name 0)
                             (let* ((g (the k-group (cons (product (1 name) (2 tw) (3 x)) nil)))
                                    (why (k-termination g)))
                               (if (string=? why "")
                                   #u
                                   (begin (set k-recursive (cons (cons name tw) rsaved)) (k-note-why g why)))))
                      #u))
           ;; A generative type's own `up-` and `down-` see
           ;; inside it.
           (inside (k-take-inside name))
           (opened (if (>= inside 0) (set k-transparent (cons inside (get k-transparent))) #u))
           (e0 (k-check-declared name tw x))
           ;; With `define*`, the globals the lambda read,
           ;; found, are its type's; and it is checked again
           ;; at that type, bound to it: one that fails is
           ;; the checker's mistake, not the program's.
           (tf (if star (k-with-latent t (k-globals-of (get k-last-latent))) tw))
           (refound (if star
                        (begin
                          (k-rebind-top name tf)
                          (set k-recursive rsaved)
                          (let* ((g (the k-group (cons (product (1 name) (2 tf) (3 x)) nil)))
                                 (why (k-termination g)))
                            (if (string=? why "")
                                #u
                                (begin (set k-recursive (cons (cons name tf) rsaved)) (k-note-why g why)))))
                        #u))
           (e (if star
                  (extract (k-saying (lambda () (k-te tf (k-check-declared name tf x)))
                                     (lambda (m) (k-cat5 (k-cat3 "`define*` found `" (symbol->string name) "` to be a ")
                                                         (k-show-ty tf) ", and checked at it, it does not check (a mistake of the checker's): " m "")))
                           2)
                  e0))
           (closed (if (>= inside 0)
                       (begin (set k-transparent (cdr (get k-transparent)))
                              (set k-conversions (cons (cons name t) (get k-conversions))))
                       #u))
           (popped (set k-recursive rsaved))
           (proved (if (null? lemma)
                       #u
                       (let ((l (car lemma)))
                         (begin (k-check-proof l name x)
                                (set k-lemmas (cons (product (1 (extract l 1)) (2 (extract l 2)) (3 (extract l 3)) (4 (extract l 4))
                                                             (5 (the k-named (cons (cons name t) nil))))
                                                    (get k-lemmas)))))))
           (after (if (k-lambda? x) #u (k-bind-global name tf))))
      (cons (k-cat4 "define " (symbol->string name) " : " (k-line tf e)) nil))))
;; One top-level form's lines: what each definition and expression is.
(define k-top-lines (subr (maxeff checks spin) (top) (listof string acyclic))
  (lambda (form)
    (the (listof string acyclic) (tagcase form
                 (t-define (name ty init a b)
                   (if (null? ty)
                       (let* ((x (k-resolve-exp init)) (u (set k-last-uses (k-free-into x nil nil))) (r (k-synth x)))
                         (begin (k-bind-global name (extract r 1))
                                (if (k-lambda? x) (k-note-known name 0) #u)
                                (cons (k-cat4 "define " (symbol->string name) " : " (k-line (extract r 1) (extract r 2))) nil)))
                       (k-define-typed name (car ty) (cdr ty) init)))
                 (t-define-rec (bs a b) (k-define-rec bs))
                 (t-exp (e)
                   (let* ((x (k-resolve-exp e)) (r (k-synth x)))
                     (cons (k-line (extract r 1) (extract r 2)) nil)))
                 (else y nil)))))
(define k-lines-append-names (subr (read @globals) (k-names k-names) k-names)
  (lambda (xs ys) (if (null? xs) ys (the k-names (cons (car xs) (k-lines-append-names (cdr xs) ys))))))
;; The names `defs` define, in order.
(define k-defs-names (subr (maxeff (read @globals) (read @t) (alloc @t)) ((listof k-def acyclic)) k-names)
  (lambda (ds) (if (null? ds) nil (k-lines-append-names (extract (car ds) 1) (k-defs-names (cdr ds))))))
;; Those of `xs` that are in `ys`, in `xs`'s order.
(define k-names-within (subr (maxeff (read @globals) (read @t)) (k-names k-names) k-names)
  (lambda (xs ys)
    (cond ((null? xs) xs)
          ((k-has-name? ys (car xs)) (the k-names (cons (car xs) (k-names-within (cdr xs) ys))))
          (else (k-names-within (cdr xs) ys)))))
;; Whether `t` is a procedure whose calls may not end: `spin` in its latent
;; effect, under any `poly`.
(define k-type-spins? (subr (maxeff (read @globals) (read @t) spin) (int) bool)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-type-spins? body))
      (ty-subr (e ps r cv)
        (letrec ((go (subr (read @globals) (k-eff) bool) (lambda (e) (and (not (null? e)) (or (tagcase (car e) (a-spin () #t) (else y #f)) (go (cdr e)))))))
          (go e)))
      (else y #f))))
(define k-names-spin? (subr (maxeff (read @globals) (read @t) spin) (k-names) bool)
  (lambda (ns) (and (not (null? ns)) (or (k-type-spins? (k-lookup-raw (car ns))) (k-names-spin? (cdr ns))))))
(define k-top-start (subr pure (top) int)
  (lambda (form) (tagcase form (t-define (name ty init a b) a) (t-define-rec (bs a b) a) (else y 0))))
(define k-top-end (subr pure (top) int)
  (lambda (form) (tagcase form (t-define (name ty init a b) b) (t-define-rec (bs a b) b) (else y 0))))
(define k-atoms-globals (subr (maxeff (read @globals) (alloc @t)) (k-eff) k-regions)
  (lambda (e)
    (cond ((null? e) nil)
          ((k-globals-atom? (car e)) (the k-regions (cons (k-atom-region (car e)) (k-atoms-globals (cdr e)))))
          (else (k-atoms-globals (cdr e))))))
;; The globals calling a value of type `t` reads: its latent effect's, under
;; any `poly`; none, if it is not a procedure.
(define k-latent-globals (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (int) k-regions)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-latent-globals body))
      (ty-subr (e ps r cv) (k-atoms-globals e))
      (else y nil))))
;; The first of `ns` whose global `rs` has, if any.
(define k-first-read (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-regions k-names) k-names)
  (lambda (rs ns)
    (cond ((null? ns) nil)
          ((k-has-region-in? rs (r-global (car ns))) (the k-names (cons (car ns) nil)))
          (else (k-first-read rs (cdr ns))))))
;; Defining a global writes it: a procedure stored in global `f` whose calls
;; read `f` may reach itself through the global, which termination checking,
;; trusting every procedure of a type without `spin` to end, has not seen.
;; So it must say `spin`, as a procedure kept in a ref must, however it
;; reads `f`; one that stays `pure` binds itself with a local `letrec`. A
;; group's members read each other so. Reading `@globals` may read `f` only
;; once `f` is a global (`top.rs`, `no_reaching_itself`).
(define k-no-reaching-itself (subr (maxeff checks spin) (top k-names bool) unit)
  (lambda (form ns redefining)
    (letrec ((each (subr (maxeff checks spin) (k-names) unit)
               (lambda (ms)
                 (if (null? ms)
                     #u
                     (let* ((n (car ms)) (t (k-lookup-raw n)))
                       (if (k-type-spins? t)
                           (each (cdr ms))
                           (let* ((reads (k-latent-globals t))
                                  (m (k-first-read reads ns))
                                  (name (symbol->string n)))
                             (cond ((not (null? m))
                                    (k-fail (k-cat5 (k-cat5 "calling `" name "` reads `" (symbol->string (car m)) "`, so `")
                                                    name "` may reach itself through a global: its type must say `spin` (or, to call itself directly, it binds itself with a local `letrec`)" "" "")
                                            (k-top-start form) (k-top-end form)))
                                   ((and redefining (k-has-region-in? reads (r-globals)))
                                    (k-fail (k-cat5 (k-cat5 "calling `" name "` may read any global, `" name "` too, so `")
                                                    name "` may reach itself through a global: its type must say `spin`" "" "")
                                            (k-top-start form) (k-top-end form)))
                                   (else (each (cdr ms)))))))))))
      (each ns))))
;; Each of `users` checked again after the redefinition of `ns`: defined
;; again if it checks, broken if not.
(define k-rerun (subr (maxeff (read @globals) checks spin) ((listof k-def acyclic) k-names (listof string acyclic)) (listof string acyclic))
  (lambda (users ns lines)
    (if (null? users)
        lines
        (let* ((u (car users))
               (olds (k-old-types (extract u 1)))
               (m (k-mark))
               (reset (set k-last-uses nil))
               (r (prompt k-tag
                    (let ((ls (k-top-lines (extract u 2))))
                      (begin (k-no-reaching-itself (extract u 2) (extract u 1) #t) (k-ok ls)))
                    (lambda (r) r))))
          (tagcase r
            (k-ok (ls)
              (let* ((assigns (k-fits-old? olds))
                     (recorded (k-record (extract u 2) (extract u 1)))
                     (ran (set k-runs (the (listof k-run acyclic) (cons (product (1 (extract u 2)) (2 assigns)) (get k-runs))))))
                (k-rerun (cdr users) ns (k-lines-append lines ls))))
            (k-err (msg a b)
              (begin (k-unbind-to m)
                     (k-break-all (extract u 1) (k-cat5 "since " (k-shown ns) " was redefined (" msg ")"))
                     (k-rerun (cdr users) ns lines)))
            (else y (k-rerun (cdr users) ns lines)))))))
;; A top-level form, checked under redefinition: its lines, and those of
;; the definitions it has run again.
(define k-defining (subr (maxeff checks spin) (top) (listof string acyclic))
  (lambda (form)
    (let* ((ns (k-top-names form))
           (olds (k-old-types ns))
           (users (if (null? olds) (the (listof k-def acyclic) nil) (k-users-of ns)))
           (reset (set k-last-uses nil))
           (lines (k-top-lines form))
           (knot (k-no-reaching-itself form ns (not (null? olds))))
           (assigns (and (not (null? olds)) (k-fits-old? olds)))
           (recorded (k-record form ns))
           (ran (set k-runs (the (listof k-run acyclic) (cons (product (1 form) (2 assigns)) (get k-runs))))))
      (if (or (null? olds) assigns) lines (k-rerun users ns lines)))))


;; The second pass: definitions and expressions, in order, each under
;; redefinition (`k-defining`).
(define k-forms (subr (maxeff checks spin) ((listof top acyclic) k-out) k-out)
  (lambda (forms out)
    (if (null? forms)
        (reverse out)
        (k-forms (cdr forms) (k-push-lines (k-defining (car forms)) out)))))

;; The entry point: check a program's trees, in the initial environment
;; written `standard`. What each definition and expression is, in order,
;; or the first error.
(define check-program (subr (maxeff (read @globals) checks spin) ((listof syn acyclic) (listof top acyclic)) k-result)
  (lambda (standard forms)
    (prompt k-tag
      (begin (k-reset) (k-standard standard) (k-ahead forms) (k-ok (k-forms forms nil)))
      (lambda (r) r))))

;; The entry point for more of a program, form by form, as the REPL gives
;; them: checked in the environment the forms before left, which
;; `check-program` began. The facts for the compiler are only the new
;; forms', whose positions are in their own text.
(define check-more (subr (maxeff (read @globals) checks spin) ((listof top acyclic)) k-result)
  (lambda (forms)
    (prompt k-tag
      (begin (set k-extracts nil) (set k-effect-notes nil) (set k-runs nil) (k-ahead forms) (k-ok (k-forms forms nil)))
      (lambda (r) r))))
