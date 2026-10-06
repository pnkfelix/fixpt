;;; The checker, in FX-26: subtyping, errors, and calls that may not end.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ subtyping
;;; `a ≤ b`. Recursive types are compared coinductively: a pair already
;;; being compared is assumed to hold.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define check-subtype-module (module
(define-type k-trail (ref k-pairs @t))
;; A subtype question's binder environment, for one side: each `poly`
;; binder in scope, by the name its pair of binders was given, so bodies are
;; compared as they are, not substituted, and a cycle through a `poly` comes
;; back to a pair, and an environment, already on the trail.
(define-type k-benv k-pairs)
;; Both sides' environments.
(define-type k-benvs (pairof k-benv k-benv @t))
;; What one subtype question remembers: the pairs assumed (FX-87's trail),
;; each with the environments it was asked under; and the names given to
;; pairs of `poly` binders, by the pair of nodes and the position.
(define-type k-assumed (listof (productof (1 int) (2 int) (3 k-benv) (4 k-benv)) acyclic))
(define-type k-strail (ref k-assumed @t))
(define-type k-label-entry (productof (1 int) (2 int) (3 int) (4 int)))
(define-type k-label-list (listof k-label-entry acyclic))
(define-type k-labels (ref k-label-list @t))
;; Each lemma that fits a pair of types: its hypotheses, instantiated.
(define-type k-instances (listof k-hyps acyclic))

;; Modules' types compared, by `check-module-rules.fx`, which sets this.
(define-type k-sub-rule
  (subr (maxeff kstate spin) (int int k-ty k-ty k-benv k-benv k-strail k-labels) bool))
;; A computation checked, and what makes a message of W and G.
(define-type k-checking (subr (maxeff checks spin) () k-te))
(define-type k-saying (subr (maxeff checks spin) (string string string) string))

;; The latent effect of `t`, a `subr` under any `poly`s, in a list; or none.
(define-type k-effs (listof k-eff acyclic))
(define k-bool=? (subr pure (bool bool) bool) (lambda (x y) (if x y (not y))))
(define k-part-find (subr kreads (k-parts symbol) int)
  (lambda (ps l)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2))
          (else (k-part-find (cdr ps) l)))))

(define k-benv-var (subr kreads (k-benv int) int)
  (lambda (env v)
    (cond ((null? env) v)
          ((= (car (car env)) v) (cdr (car env)))
          (else (k-benv-var (cdr env) v)))))
;; Whether binders `x` and `y` stand for the same, each by its side's
;; environment.
(define k-benv-var=? (subr kreads (int int k-benv k-benv) bool)
  (lambda (x y ea eb) (= (k-benv-var ea x) (k-benv-var eb y))))
;; Whether a procedure called in convention `a` may be used as one called
;; in `b`: the same, or any of FX-26's own as `fx`; binders by the binders
;; they stand for.
(define k-conv-sub? (subr kreads (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (k-benv-var=? x y ea eb)) (else z #f)))
      (else y (or (k-conv=? a b) (tagcase b (cv-fx () #t) (else z #f)))))))
;; Whether two conventions are the same, binders by what they stand for.
(define k-conv-same? (subr kreads (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (k-benv-var=? x y ea eb)) (else z #f)))
      (else y (k-conv=? a b)))))
;; `env` with `v` named `l`, in place of any name it had: re-entering a scope
;; shadows it, so the environments stay finitely many.
(define k-benv-set (subr kmakes (k-benv int int) k-benv)
  (lambda (env v l)
    (letrec ((drop (subr kmakes (k-benv) k-benv)
               (lambda (e)
                 (cond ((null? e) nil)
                       ((= (car (car e)) v) (cdr e))
                       (else (cons (car e) (drop (cdr e))))))))
      (the k-benv (cons (the (pairof int int @t) (cons v l)) (drop env))))))
(define k-benv-within? (subr kreads (k-benv k-benv) bool)
  (lambda (x y)
    (or (null? x)
        (and (= (k-benv-var y (car (car x))) (cdr (car x))) (k-benv-within? (cdr x) y)))))
(define k-benv=? (subr kreads (k-benv k-benv) bool)
  (lambda (x y) (and (= (k-length x) (k-length y)) (k-benv-within? x y))))
;; `a ≤ b` for frozen data: the same, or finite data seen as possibly
;; cyclic, in one place.
(define k-frozen-le? (subr (maxeff (read @globals) spin) (k-region k-region) bool)
  (lambda (a b)
    (or (k-region=? a b)
        (tagcase a
          (r-frozen (p f) (and f (tagcase b (r-frozen (q g) (and (= p q) (not g))) (else y #f))))
          (else y #f)))))
(define k-benv-region (subr kreads (k-benv k-region) k-region)
  (lambda (env r)
    (if (null? env)
        r
        (tagcase r
          (r-var (v) (r-var (k-benv-var env v)))
          (r-frozen (p f) (if (< p 0) r (r-frozen (k-benv-var env p) f)))
          (else y r)))))
;; Whether regions `r` and `s` are the same, each by its side's environment.
(define k-benv-region=? (subr (maxeff kreads spin) (k-region k-region k-benv k-benv) bool)
  (lambda (r s ea eb) (k-region=? (k-benv-region ea r) (k-benv-region eb s))))
;; `r ≤ s` for frozen data, each by its side's environment.
(define k-benv-frozen-le? (subr (maxeff kreads spin) (k-region k-region k-benv k-benv) bool)
  (lambda (r s ea eb) (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))))
;; Whether `g` is the `x` of a dependent procedure's `k`th parameter.
(define k-param-is? (subr (maxeff kreads spin) (int int symbol) bool)
  (lambda (g k x) (tagcase (k-get g) (ty-param (j y) (and (= k j) (symbol=? x y))) (else z #f))))
;; Whether `g` is `(select m x)` as written.
(define k-select-is? (subr (maxeff kreads spin) (int symbol symbol) bool)
  (lambda (g m x)
    (tagcase (k-get g) (ty-select (n y) (and (symbol=? m n) (symbol=? x y))) (else z #f))))
;; Convention `c` by an environment.
(define k-benv-conv (subr kreads (k-benv k-conv) k-conv)
  (lambda (env c) (tagcase c (cv-var (v) (cv-var (k-benv-var env v))) (else y c))))
(define-rec
  (k-benv-effect (subr (maxeff kmakes spin) (k-benv k-eff) k-eff)
    (lambda (env e)
      (if (or (null? env) (null? e))
          e
          (let ((x (car e)) (rest (k-benv-effect env (cdr e))))
            (cons (tagcase x
                    (a-read (r) (a-read (k-benv-region env r)))
                    (a-write (r) (a-write (k-benv-region env r)))
                    (a-alloc (r) (a-alloc (k-benv-region env r)))
                    (a-goto (r) (a-goto (k-benv-region env r)))
                    (a-comefrom (r) (a-comefrom (k-benv-region env r)))
                    (a-await (r) (a-await (k-benv-region env r)))
                    (a-spin () x)
                    (a-var (v) (a-var (k-benv-var env v)))
                    ;; Its variable, and what it was given, as named here.
                    (a-app (v ds) (a-app (k-benv-var env v) (k-benv-eargs env ds))))
                  rest)))))
  (k-benv-eargs (subr (maxeff kmakes spin) (k-benv k-descs) k-descs)
    (lambda (env ds)
      (if (null? ds)
          nil
          (let* ((d (tagcase (car ds)
                      (dr (r) (dr (k-benv-region env r)))
                      (de (e) (de (k-benv-effect env e)))
                      (dc (c) (dc (k-benv-conv env c)))
                      (else y (car ds))))
                 (rest (k-benv-eargs env (cdr ds))))
            (the k-descs (cons d rest)))))))
(define k-strail-has? (subr kreads (k-assumed int int k-benv k-benv) bool)
  (lambda (ps a b ea eb)
    (and (not (null? ps))
         (or (let ((p (car ps)))
               (and (= (extract p 1) a) (= (extract p 2) b)
                    (k-benv=? (extract p 3) ea) (k-benv=? (extract p 4) eb)))
             (k-strail-has? (cdr ps) a b ea eb)))))
;; Put a subtype question's memory back as it was: trail `st`, labels `sl`.
(define k-restore (subr kstate (k-strail k-labels k-assumed k-label-list) unit)
  (lambda (trail labels st sl) (begin (set trail st) (set labels sl))))
;; Whether label entry `x` is for the binders at position `i` of nodes `a`
;; and `b`.
(define k-label-of? (subr pure (k-label-entry int int int) bool)
  (lambda (x a b i) (and (= (extract x 1) a) (= (extract x 2) b) (= (extract x 3) i))))
(define k-label (subr kstate (k-labels int int int) int)
  (lambda (labels a b i)
    (letrec ((find (subr kreads (k-label-list) int)
               (lambda (ls)
                 (cond ((null? ls) 0)
                       ((k-label-of? (car ls) a b i) (extract (car ls) 4))
                       (else (find (cdr ls)))))))
      (let ((found (find (get labels))))
        (if (< found 0)
            found
            (let ((l (- -1000 (k-length (get labels)))))
              (begin (set labels (cons (product (1 a) (2 b) (3 i) (4 l)) (get labels))) l)))))))

;; Name each pair of binders of two `poly` nodes `a` and `b` by the pair and
;; its position: the environments inside, for each side, from `es`.
(define k-name-binders (subr kstate (k-binders k-binders int int int k-benvs k-labels) k-benvs)
  (lambda (ba bb a b i es labels)
    (if (null? ba)
        es
        (let* ((l (k-label labels a b i))
               (ea (k-benv-set (car es) (extract (car ba) 1) l))
               (eb (k-benv-set (cdr es) (extract (car bb) 1) l)))
          (k-name-binders (cdr ba) (cdr bb) a b (+ i 1) (the k-benvs (cons ea eb)) labels)))))
;; Bounded region binders must have the same bounds.
(define k-same-bounds? (subr (maxeff kmakes spin) (k-binders k-binders k-benv k-benv) bool)
  (lambda (ba bb ea eb)
    (or (null? ba)
        (let ((x (k-bound-of (extract (car ba) 1))) (y (k-bound-of (extract (car bb) 1))))
          (and (cond ((and (null? x) (null? y)) #t)
                     ((or (null? x) (null? y)) #f)
                     (else (k-benv-region=? (car x) (car y) ea eb)))
               (k-same-bounds? (cdr ba) (cdr bb) ea eb))))))
;; Whether two nodes are the same generative type's.
(define k-same-named? (subr pure (k-ty k-ty) bool)
  (lambda (ta tb)
    (tagcase ta
      (ty-named (g xs) (tagcase tb (ty-named (h ys) (= g h)) (else z #f)))
      (else z #f))))
;; Whether node `t` is a generative type open here: inside its own
;; conversions, its name is its representation; everywhere else only itself.
(define k-open-named? (subr kreads (k-ty) bool)
  (lambda (t) (tagcase t (ty-named (g xs) (k-has-id? (get k-transparent) g)) (else z #f))))
;; The tail of a `nlist` of `x` of size `m` in `r`: one shorter.
(define k-nlist-tail (subr (maxeff kstate spin) (int k-size k-region) int)
  (lambda (x m r) (k-ty-new (ty-nlist x (k-tail-size m) r))))
;; The binder of `bs` that effect `d` is, alone, or -1.
(define k-effect-binder (subr kreads (k-binders k-eff) int)
  (lambda (bs d)
    (if (and (not (null? d)) (null? (cdr d)))
        (tagcase (car d) (a-var (x) (if (k-binder-has? bs x) x -1)) (else z -1))
        -1)))
(define k-sub-module (ref k-sub-rule @t) (new (lambda (a b ta tb ea eb trail labels) #f)))

;; Whether effects `d` and `e` are the same, each by its side's environment.
(define k-benv-eff=? (subr (maxeff kmakes spin) (k-eff k-eff k-benv k-benv) bool)
  (lambda (d e ea eb) (k-eff=? (k-benv-effect ea d) (k-benv-effect eb e))))
(define-rec
  (k-subs-contra (subr (maxeff kstate spin) (k-ids k-ids k-benv k-benv k-strail k-labels) bool)
    (lambda (xs ys ea eb trail labels)
      (cond ((null? xs) (null? ys))
            ((null? ys) #f)
            (else (and (k-sub (car ys) (car xs) eb ea trail labels)
                       (k-subs-contra (cdr xs) (cdr ys) ea eb trail labels))))))
  (k-inv (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (x y ea eb trail labels)
      (and (k-sub x y ea eb trail labels) (k-sub y x eb ea trail labels))))
  ;; `x ≤ y` as what a place holds: covariant if it is `frozen`, cannot be
  ;; written; otherwise invariant.
  (k-sub-held (subr (maxeff kstate spin) (bool int int k-benv k-benv k-strail k-labels) bool)
    (lambda (frozen x y ea eb trail labels)
      (and (k-sub x y ea eb trail labels) (or frozen (k-sub y x eb ea trail labels)))))
  ;; `a ≤ b` as what calling each does.
  (k-sub-callable (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (a b ea eb trail labels)
      (let ((ca (car (k-as-subr a))) (cb (car (k-as-subr b))))
        (and (= (k-length (extract ca 2)) (k-length (extract cb 2)))
             (k-within? (k-benv-effect ea (extract ca 1)) (k-benv-effect eb (extract cb 1)))
             (k-subs-contra (extract ca 2) (extract cb 2) ea eb trail labels)
             (k-sub (extract ca 3) (extract cb 3) ea eb trail labels)))))
  ;; `a ≤ b`. Recursive types are compared coinductively: a pair already
  ;; being compared is assumed to hold, which is what makes comparing two
  ;; cycles terminate: FX-87's trail, Amadio and Cardelli's assumption set.
  ;; Every rule is a conjunction, so an assumption left behind by a failed
  ;; comparison is never relied on: the failure is the answer.
  ;; `a ≤ b`: by the rules; failing that, by a lemma. A comparison that
  ;; failed may have left assumptions on the trail, so it is put back as it
  ;; was; a lemma's hypotheses are compared assuming what is being shown.
  (k-sub (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (a b ea eb trail labels)
      (if (null? (get k-lemmas))
          (k-sub-rules a b ea eb trail labels)
          (let ((ra (k-resolve a)) (rb (k-resolve b)))
            (if (not (k-lemma-may-apply? (get k-lemmas) ra rb))
                (k-sub-rules a b ea eb trail labels)
                (let ((st (get trail)) (sl (get labels)))
                  (or (k-sub-rules a b ea eb trail labels)
                      (begin
                        (k-restore trail labels st sl)
                        (set trail (cons (product (1 ra) (2 rb) (3 ea) (4 eb)) (get trail)))
                        (let ((ls (the (listof k-lemma acyclic) (reverse (get k-lemmas)))))
                          (k-sub-by-lemmas (k-lemma-instances ls ra rb) ea eb trail labels))))))))))
  (k-sub-by-lemmas (subr (maxeff kstate spin) (k-instances k-benv k-benv k-strail k-labels) bool)
    (lambda (insts ea eb trail labels)
      (and (not (null? insts))
           (let ((st (get trail)) (sl (get labels)))
             (or (k-sub-hyps (car insts) ea eb trail labels)
                 (begin (k-restore trail labels st sl)
                        (k-sub-by-lemmas (cdr insts) ea eb trail labels)))))))
  (k-sub-hyps (subr (maxeff kstate spin) (k-hyps k-benv k-benv k-strail k-labels) bool)
    (lambda (hs ea eb trail labels)
      (or (null? hs)
          (and (k-sub (car (car hs)) (cdr (car hs)) ea eb trail labels)
               (k-sub-hyps (cdr hs) ea eb trail labels)))))
  ;; `a ≤ b`, a question of its own.
  (k-subtype (subr (maxeff kstate spin) (int int) bool)
    (lambda (a b)
      (k-sub a b (the k-benv nil) (the k-benv nil)
             (the k-strail (new nil)) (the k-labels (new nil)))))
  (k-same-ty? (subr (maxeff kstate spin) (int int) bool)
    (lambda (x y) (and (k-subtype x y) (k-subtype y x))))
  ;; Each lemma of `ls` that fits `a` and `b`: its hypotheses, instantiated.
  (k-lemma-instances (subr (maxeff kstate spin) ((listof k-lemma acyclic) int int) k-instances)
    (lambda (ls a b)
      (if (null? ls)
          nil
          (let* ((l (car ls))
                 (m (the (ref k-map @t) (new nil)))
                 (mine (if (k-lemma-fits? l a b m)
                           (the k-instances (cons (k-subst-hyps (extract l 4) (get m)) nil))
                           (the k-instances nil)))
                 (rest (k-lemma-instances (cdr ls) a b)))
            (if (null? mine) rest (the k-instances (cons (car mine) rest)))))))
  ;; Whether lemma `l`'s sides fit `a` and `b`, its binders standing for
  ;; what is recorded in `m`, and each for something.
  (k-lemma-fits? (subr (maxeff kstate spin) (k-lemma int int (ref k-map @t)) bool)
    (lambda (l a b m)
      (let ((seen (the k-trail (new nil))))
        (and (k-match-ty l (extract l 2) a m seen) (k-match-ty l (extract l 3) b m seen)
             (k-all-bound? (extract l 1) (get m))))))
  ;; Whether `t` is `pat` with the lemma's binders standing for something,
  ;; recorded in `m`.
  (k-match-ty (subr (maxeff kstate spin) (k-lemma int int (ref k-map @t) k-trail) bool)
    (lambda (l pat t m seen)
      (let ((pat (k-resolve pat)) (t (k-resolve t)))
        (or (k-pair-seen? (get seen) pat t)
            (begin
              (set seen (cons (cons pat t) (get seen)))
              (tagcase (k-get pat)
                (ty-var (v)
                  (if (k-binder-has? (extract l 1) v)
                      (k-match-binder v (dt t) m)
                      (k-same-ty? pat t)))
                (else z (k-match-node l pat t m seen))))))))
  ;; Whether node `t` is node `pat`, other than a variable: of its shape,
  ;; with parts that match; or, failing that, the same type.
  (k-match-node (subr (maxeff kstate spin) (k-lemma int int (ref k-map @t) k-trail) bool)
    (lambda (l pat t m seen)
      (letrec ((mt (subr (maxeff kstate spin) (int int) bool)
                   (lambda (x y) (k-match-ty l x y m seen)))
               (mr (subr (maxeff kstate spin) (k-region k-region) bool)
                   (lambda (r q) (k-match-region (extract l 1) r q m)))
               (same (subr (maxeff kstate spin) () bool) (lambda () (k-same-ty? pat t))))
        (let ((tt (k-get t)))
          (tagcase (k-get pat)
            (ty-named (g xs)
              (tagcase tt
                (ty-named (h ys) (and (= g h) (k-match-descs l xs ys m seen)))
                (else z (same))))
            (ty-pair (a1 b1 r1)
              (tagcase tt
                (ty-pair (a2 b2 r2) (and (mr r1 r2) (mt a1 a2) (mt b1 b2)))
                (else z (same))))
            (ty-ref (x r) (tagcase tt (ty-ref (y q) (and (mr r q) (mt x y))) (else z (same))))
            (ty-array (x r) (tagcase tt (ty-array (y q) (and (mr r q) (mt x y))) (else z (same))))
            (ty-icell (x r) (tagcase tt (ty-icell (y q) (and (mr r q) (mt x y))) (else z (same))))
            (ty-product (ps)
              (tagcase tt (ty-product (qs) (k-match-parts l ps qs m seen)) (else z (same))))
            (ty-sum (ps) (tagcase tt (ty-sum (qs) (k-match-parts l ps qs m seen)) (else z (same))))
            (ty-subr (e1 p1 r1 c1)
              (tagcase tt
                (ty-subr (e2 p2 r2 c2)
                  (and (k-conv=? c1 c2) (k-eff=? e1 e2) (= (k-length p1) (k-length p2))
                       (k-match-list l p1 p2 m seen) (mt r1 r2)))
                (else z (same))))
            (else z (same)))))))
  (k-match-list (subr (maxeff kstate spin) (k-lemma k-ids k-ids (ref k-map @t) k-trail) bool)
    (lambda (l xs ys m seen)
      (or (null? xs)
          (and (k-match-ty l (car xs) (car ys) m seen) (k-match-list l (cdr xs) (cdr ys) m seen)))))
  (k-match-parts (subr (maxeff kstate spin) (k-lemma k-parts k-parts (ref k-map @t) k-trail) bool)
    (lambda (l ps qs m seen)
      (and (= (k-length ps) (k-length qs))
           (letrec ((each (subr (maxeff kstate spin) (k-parts k-parts) bool)
                          (lambda (ps qs)
                            (or (null? ps)
                                (and (symbol=? (extract (car ps) 1) (extract (car qs) 1))
                                     (k-match-ty l (extract (car ps) 2) (extract (car qs) 2) m seen)
                                     (each (cdr ps) (cdr qs)))))))
             (each ps qs)))))
  (k-match-descs (subr (maxeff kstate spin) (k-lemma k-descs k-descs (ref k-map @t) k-trail) bool)
    (lambda (l xs ys m seen)
      (or (null? xs)
          (and (let ((y (car ys)) (bs (extract l 1)))
                 (tagcase (car xs)
                   (dt (a) (tagcase y (dt (b) (k-match-ty l a b m seen)) (else z #f)))
                   (dr (r) (tagcase y (dr (q) (k-match-region bs r q m)) (else z #f)))
                   (de (d) (tagcase y (de (e) (k-match-effect bs d e m)) (else z #f)))
                   (dz (a) (tagcase y (dz (b) (k-size=? a b)) (else z #f)))
                   (dc (a) (tagcase y (dc (b) (k-conv=? a b)) (else z #f)))
                   (df (a) #f)))
               (k-match-descs l (cdr xs) (cdr ys) m seen)))))
  ;; Whether binder `v` may stand for `d`, as recorded in `m`: recorded now
  ;; if it stands for nothing yet, or already for the same.
  (k-match-binder (subr (maxeff kstate spin) (int k-desc (ref k-map @t)) bool)
    (lambda (v d m)
      (let ((f (k-map-find (get m) v)))
        (if (null? f)
            (begin (set m (cons (cons v d) (get m))) #t)
            (k-same-desc? (cdr (car f)) d)))))
  ;; Whether descriptions `x` and `d` are the same type, region or effect.
  (k-same-desc? (subr (maxeff kstate spin) (k-desc k-desc) bool)
    (lambda (x d)
      (tagcase x
        (dt (u) (tagcase d (dt (t) (k-same-ty? u t)) (else z #f)))
        (dr (r) (tagcase d (dr (q) (k-region=? r q)) (else z #f)))
        (de (e) (tagcase d (de (e2) (k-eff=? e e2)) (else z #f)))
        (else z #f))))
  (k-match-region (subr (maxeff kstate spin) (k-binders k-region k-region (ref k-map @t)) bool)
    (lambda (bs r q m)
      (tagcase r
        (r-var (v) (if (k-binder-has? bs v) (k-match-binder v (dr q) m) (k-region=? r q)))
        (else z (k-region=? r q)))))
  (k-match-effect (subr (maxeff kstate spin) (k-binders k-eff k-eff (ref k-map @t)) bool)
    (lambda (bs d e m)
      (let ((v (k-effect-binder bs d)))
        (if (< v 0) (k-eff=? d e) (k-match-binder v (de e) m)))))
  ;; `a ≤ b` by the rules alone.
  (k-sub-rules (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (a b ea eb trail labels)
      (let ((a (k-resolve a)) (b (k-resolve b)))
        (cond
          ((and (= a b) (and (null? ea) (null? eb))) #t)
          ((k-strail-has? (get trail) a b ea eb) #t)
          (else
           (begin
             (set trail (cons (product (1 a) (2 b) (3 ea) (4 eb)) (get trail)))
             (k-sub-opened a b ea eb trail labels)))))))
  ;; `a ≤ b`, assumed: a generative type open here is its representation,
  ;; unless both are the same one or `a` is `void`.
  (k-sub-opened (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (a b ea eb trail labels)
      (let* ((ta (k-get a)) (tb (k-get b))
             (closed (or (k-same-named? ta tb) (tagcase ta (ty-void () #t) (else z #f)))))
        (cond
          ((and (not closed) (k-open-named? ta))
           (tagcase ta (ty-named (g xs) (k-sub (k-unfold g xs) b ea eb trail labels)) (else z #f)))
          ((and (not closed) (k-open-named? tb))
           (tagcase tb (ty-named (g ys) (k-sub a (k-unfold g ys) ea eb trail labels)) (else z #f)))
          (else (k-sub-shapes a b ta tb ea eb trail labels))))))
  ;; `a ≤ b`, their nodes `ta` and `tb`, by their shapes.
  (k-sub-shapes (subr (maxeff kstate spin) (int int k-ty k-ty k-benv k-benv k-strail k-labels) bool)
    (lambda (a b ta tb ea eb trail labels)
      (if (and (tagcase ta (ty-comp (x y e r) #t) (else z #f))
               (tagcase tb (ty-subr (e ps r cv) #t) (else z #f)))
          (k-sub-callable a b ea eb trail labels)
          (tagcase ta
            (ty-void () #t)
            (ty-base (x) (tagcase tb (ty-base (y) (symbol=? x y)) (else z #f)))
            ;; A natural is an integer; one of a known size, a natural.
            (ty-nat (m)
              (tagcase tb
                (ty-base (y) (symbol=? y 'int))
                (ty-nat (n) (k-size-le? m n))
                (else z #f)))
            (ty-var (x) (tagcase tb (ty-var (y) (k-benv-var=? x y ea eb)) (else z #f)))
            (ty-subr (e ps r cv)
              (tagcase tb
                (ty-subr (e2 ps2 r2 cv2)
                  (and (k-conv-sub? cv cv2 ea eb) (k-sub-callable a b ea eb trail labels)))
                (else z #f)))
            (ty-ref (x r)
              (tagcase tb
                (ty-ref (y s) (and (k-benv-region=? r s ea eb) (k-inv x y ea eb trail labels)))
                (else z #f)))
            (ty-array (x r)
              (tagcase tb
                (ty-array (y s) (and (k-benv-region=? r s ea eb) (k-inv x y ea eb trail labels)))
                (else z #f)))
            (ty-icell (x r)
              (tagcase tb
                (ty-icell (y s) (and (k-benv-region=? r s ea eb) (k-inv x y ea eb trail labels)))
                (else z #f)))
            (ty-place (r) (tagcase tb (ty-place (s) (k-benv-region=? r s ea eb)) (else z #f)))
            (ty-pair (x1 x2 r)
              (tagcase tb
                (ty-pair (y1 y2 s)
                  (and (k-benv-frozen-le? r s ea eb)
                       ;; Frozen pairs cannot be written, so, as a frozen
                       ;; bloblet's fields, their contents are covariant;
                       ;; and finite data may be seen as possibly cyclic.
                       (let ((frozen (tagcase r (r-frozen (p f) #t) (else z #f))))
                         (and (k-sub-held frozen x1 y1 ea eb trail labels)
                              (k-sub-held frozen x2 y2 ea eb trail labels)))))
                ;; A finite list is a `nlist` of some length.
                (ty-nlist (y sz s)
                  (and (tagcase sz (sz-finite () #t) (else z #f))
                       (tagcase r (r-frozen (p f) f) (else z #f))
                       (k-benv-frozen-le? r s ea eb)
                       (k-sub x1 y ea eb trail labels)
                       (k-sub x2 b ea eb trail labels)))
                (else z #f)))
            (ty-tag (a1 h1 d1 r1)
              (tagcase tb
                (ty-tag (a2 h2 d2 r2)
                  (and (k-benv-region=? r1 r2 ea eb)
                       (k-eff=? (k-benv-effect ea d1) (k-benv-effect eb d2))
                       (k-inv a1 a2 ea eb trail labels) (k-inv h1 h2 ea eb trail labels)))
                (else z #f)))
            (ty-comp (t1 a1 d1 r1)
              (tagcase tb
                (ty-comp (t2 a2 d2 r2)
                  (and (k-benv-region=? r1 r2 ea eb)
                       (k-within? (k-benv-effect ea d1) (k-benv-effect eb d2))
                       (k-sub t2 t1 eb ea trail labels) (k-sub a1 a2 ea eb trail labels)))
                (else z #f)))
            (ty-markkey (x r)
              (tagcase tb
                (ty-markkey (y s) (and (k-benv-region=? r s ea eb) (k-inv x y ea eb trail labels)))
                (else z #f)))
            (ty-bloblet (fa za r)
              (tagcase tb
                (ty-bloblet (fb zb s)
                  (and (if za (k-benv-frozen-le? r s ea eb) (k-benv-region=? r s ea eb))
                       (k-bool=? za zb) (= (k-length fa) (k-length fb))
                       (k-sub-fields fa fb za ea eb trail labels)))
                (else z #f)))
            (ty-product (pa)
              (tagcase tb
                (ty-product (pb)
                  (and (= (k-length pa) (k-length pb)) (k-sub-product pa pb ea eb trail labels)))
                (else z #f)))
            (ty-sum (sa)
              (tagcase tb (ty-sum (sb) (k-sub-sum sa sb ea eb trail labels)) (else z #f)))
            (ty-poly (ba xa)
              (tagcase tb
                (ty-poly (bb xb)
                  (and (= (k-length ba) (k-length bb)) (k-same-kinds? ba bb)
                       (let* ((named (k-name-binders ba bb a b 0 (the k-benvs (cons ea eb)) labels))
                              (ia (car named)) (ib (cdr named)))
                         (and (k-same-bounds? ba bb ia ib)
                              (k-sub xa xb ia ib trail labels)))))
                (else z #f)))
            ;; A `nlist` is frozen, so covariant in its elements, and
            ;; forgets its size to `finite`; any `nlist` is a finite
            ;; list, and a finite list a `nlist` of some length.
            (ty-nlist (x m r)
              (tagcase tb
                (ty-nlist (y n s)
                  (and (k-benv-frozen-le? r s ea eb) (k-size-le? m n)
                       (k-sub x y ea eb trail labels)))
                (ty-pair (y tail s)
                  (let ((k (k-size-as-lit m)))
                    (and (k-benv-frozen-le? r s ea eb)
                         (k-sub x y ea eb trail labels)
                         (tagcase m
                           ;; A `nlist` of some length has for its tail the same type.
                           (sz-finite () (k-sub a tail ea eb trail labels))
                           (else w
                             (or (= k 0) (k-sub (k-nlist-tail x m r) tail ea eb trail labels)))))))
                (else z #f)))
            ;; A generative type is related only to itself, argument
            ;; by argument, as its variance says.
            (ty-named (g xs)
              (tagcase tb
                (ty-named (h ys)
                  (and (= g h) (k-sub-descs xs ys (extract (k-gen-of g) 3) ea eb trail labels)))
                (else z #f)))
            ;; A description function applied: the same function, given
            ;; the same descriptions (FX-91's congruence).
            (ty-app (f xs)
              (tagcase tb
                (ty-app (g ys)
                  (and (= (k-length xs) (k-length ys)) (k-fun-same? f g ea eb trail labels)
                       (k-ds-same? xs ys ea eb trail labels)))
                (else z #f)))
            ;; Two description functions (a module's transparent ones).
            (ty-lam (bs x)
              (tagcase tb (ty-lam (cs y) (k-fun-same? a b ea eb trail labels)) (else z #f)))
            (ty-module (abs ds vs) ((get k-sub-module) a b ta tb ea eb trail labels))
            (ty-param (k x) ((get k-sub-module) a b ta tb ea eb trail labels))
            (else z #f)))))
  ;; Generative type arguments `xs ≤ ys`, each as its variance in `vs` says.
  (k-sub-descs (subr (maxeff kstate spin)
                     (k-descs k-descs k-ids k-benv k-benv k-strail k-labels) bool)
    (lambda (xs ys vs ea eb trail labels)
      (or (null? xs)
          (and (let ((v (car vs)))
                 (tagcase (car xs)
                   (dt (x)
                     (tagcase (car ys)
                       (dt (y) (cond ((= v 0) (k-sub x y ea eb trail labels))
                                     ((= v 1) (k-sub y x eb ea trail labels))
                                     (else (k-inv x y ea eb trail labels))))
                       (else z #f)))
                   (dr (r) (tagcase (car ys) (dr (q) (k-benv-region=? r q ea eb)) (else z #f)))
                   (de (d)
                     (tagcase (car ys)
                       (de (e)
                         (let ((d2 (k-benv-effect ea d)) (e2 (k-benv-effect eb e)))
                           (cond ((= v 0) (k-within? d2 e2))
                                 ((= v 1) (k-within? e2 d2))
                                 (else (k-eff=? d2 e2)))))
                       (else z #f)))
                   (dz (m) (tagcase (car ys) (dz (n) (k-size-eq? m n)) (else z #f)))
                   (dc (c) (tagcase (car ys) (dc (d) (k-conv-same? c d ea eb)) (else z #f)))
                   (df (f) (k-d-same? (car xs) (car ys) ea eb trail labels))))
               (k-sub-descs (cdr xs) (cdr ys) (cdr vs) ea eb trail labels)))))
  (k-sub-fields (subr (maxeff kstate spin) (k-ids k-ids bool k-benv k-benv k-strail k-labels) bool)
    (lambda (fa fb frozen ea eb trail labels)
      (cond ((null? fa) #t)
            (else (and (k-sub-held frozen (car fa) (car fb) ea eb trail labels)
                       (k-sub-fields (cdr fa) (cdr fb) frozen ea eb trail labels))))))
  (k-sub-product (subr (maxeff kstate spin) (k-parts k-parts k-benv k-benv k-strail k-labels) bool)
    (lambda (pa pb ea eb trail labels)
      (cond ((null? pa) #t)
            (else (and (symbol=? (extract (car pa) 1) (extract (car pb) 1))
                       (k-sub (extract (car pa) 2) (extract (car pb) 2) ea eb trail labels)
                       (k-sub-product (cdr pa) (cdr pb) ea eb trail labels))))))
  (k-sub-sum (subr (maxeff kstate spin) (k-parts k-parts k-benv k-benv k-strail k-labels) bool)
    (lambda (sa sb ea eb trail labels)
      (cond ((null? sa) #t)
            (else (let ((y (k-part-find sb (extract (car sa) 1))))
                    (and (>= y 0) (k-sub (extract (car sa) 2) y ea eb trail labels)
                         (k-sub-sum (cdr sa) sb ea eb trail labels)))))))
  ;; Whether descriptions `x` and `y` are the same, each by its side's
  ;; environment: types each a subtype of the other.
  (k-d-same? (subr (maxeff kstate spin) (k-desc k-desc k-benv k-benv k-strail k-labels) bool)
    (lambda (x y ea eb trail labels)
      (tagcase x
        (dt (a) (tagcase y (dt (b) (k-inv a b ea eb trail labels)) (else z #f)))
        (dr (r) (tagcase y (dr (s) (k-benv-region=? r s ea eb)) (else z #f)))
        (de (d) (tagcase y (de (e) (k-benv-eff=? d e ea eb)) (else z #f)))
        (dz (m) (tagcase y (dz (n) (k-size-eq? m n)) (else z #f)))
        (dc (c) (tagcase y (dc (d) (k-conv-same? c d ea eb)) (else z #f)))
        (df (f) (tagcase y (df (g) (k-fun-same? f g ea eb trail labels)) (else z #f))))))
  (k-ds-same? (subr (maxeff kstate spin) (k-descs k-descs k-benv k-benv k-strail k-labels) bool)
    (lambda (xs ys ea eb trail labels)
      (or (null? xs)
          (and (k-d-same? (car xs) (car ys) ea eb trail labels)
               (k-ds-same? (cdr xs) (cdr ys) ea eb trail labels)))))
  ;; Whether description functions `f` and `g` are the same, each by its
  ;; side's environment: the same variable, or `dlambda`s of the same kinds
  ;; whose bodies are the same, their parameters named alike. They are
  ;; reduced and eta-contracted as they are made, so nothing else is.
  (k-fun-same? (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (f g ea eb trail labels)
      (let ((f (k-resolve f)) (g (k-resolve g)))
        (if (and (= f g) (null? ea) (null? eb))
            #t
            (tagcase (k-get f)
              (ty-var (x) (tagcase (k-get g) (ty-var (y) (k-benv-var=? x y ea eb)) (else z #f)))
              ;; A dependent procedure's parameter's, or a `select` as written.
              (ty-param (k x) (k-param-is? g k x))
              (ty-select (m x) (k-select-is? g m x))
              (ty-lam (pa ba)
                (tagcase (k-get g)
                  (ty-lam (pb bb)
                    (and (= (k-length pa) (k-length pb)) (k-same-kinds? pa pb)
                         (let ((named (k-name-binders pa pb f g 0 (cons ea eb) labels)))
                           (k-d-same? ba bb (car named) (cdr named) trail labels))))
                  (else z #f)))
              (else z #f)))))))
(define k-part-index (subr kreads (k-parts symbol int) int)
  (lambda (ps l i)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) l) i)
          (else (k-part-index (cdr ps) l (+ i 1))))))

;;; ------------------------------------------------------------ errors

(define k-newline string (char->string (integer->char 10)))
;; Run `f`, and if it fails at `a`..`b` with "a W is expected here, and
;; this is a G", fail instead with what `say` makes of W and G.
(define k-expected-split (subr (maxeff (read @globals) spin) (string) string)
  (lambda (m) (if (= (string-search m "a " 0) 0) (substring m 2 (string-length m)) "")))
(define k-sep string " is expected here, and this is a ")
;; "a W is expected here, and this is a G", of `w` and `g`.
(define k-expected-here (subr (read @globals) (string string) string)
  (lambda (w g) (k-cat4 "a " w k-sep g)))
(define k-rewriting (subr (maxeff checks spin) (k-checking int int k-saying) k-te)
  (lambda (f a b say)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          ;; Its second line, an effect's delta, apart, and put back last.
          (let* ((nl (string-search m k-newline 0))
                 (first (if (< nl 0) m (substring m 0 nl)))
                 (delta (if (< nl 0) "" (substring m nl (string-length m))))
                 (rest (k-expected-split first)) (at (k-find-sub rest k-sep 0)))
            (if (and (= ea a) (= eb b) (not (string=? rest "")) (>= at 0))
                (let ((w (substring rest 0 at))
                      (g (substring rest (+ at (string-length k-sep)) (string-length rest))))
                  (k-fail (string-append (say m w g) delta) ea eb))
                (k-fail m ea eb))))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))
;; The same, for any error at `a`..`b`.
(define k-prefixing (subr checks ((subr checks () k-te) int int (subr checks () string)) k-te)
  (lambda (f a b prefix)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb)
          (if (and (= ea a) (= eb b)) (k-fail (string-append (prefix) m) ea eb) (k-fail m ea eb)))
        (k-ok (xs) (k-fail "k-ok inside" a b))))))

;; The convention `want` asks of `got`, where a procedure differs from what
;; is expected only in its convention, so that a conversion makes it one
;; (`docs/research/native-conventions.md`).
(define k-conversion (subr (maxeff checks spin) (int int) (listof k-conv acyclic))
  (lambda (got want)
    (tagcase (k-get (k-resolve got))
      (ty-subr (e ps r from)
        (tagcase (k-get (k-resolve want))
          (ty-subr (e2 ps2 r2 to)
            (if (and (not (k-conv=? from to)) (k-subtype (k-ty-new (ty-subr e ps r to)) want))
                (cons to nil)
                nil))
          (else y nil)))
      (else y nil))))
;; Conversion `code` at `x`'s span, among the facts `checked-extracts` gives.
(define k-note-conversion (subr (maxeff checks spin) (kx int) unit)
  (lambda (x code)
    (let ((fact (product (1 (k-start x)) (2 (k-end x)) (3 (- -1000 code)))))
      (set k-extracts (cons fact (get k-extracts))))))
;; A conversion of `x`'s procedure, of type `t`, to `to`. To `fx` or to a
;; convention binder it does nothing at run time; to `cellular` or `native`
;; it is `%fx26-convert`, which gives the value if it is already one of
;; those, and otherwise an adapter: a procedure of the convention asked
;; for that calls it. The compiler learns of it as a fact at `x`'s span:
;; -1000 less the arity times 4, plus 1 for `cellular` or 2 for `native`.
(define k-convert-at (subr (maxeff checks spin) (kx int k-conv) unit)
  (lambda (x t to)
    (let ((n (tagcase (k-get (k-resolve t)) (ty-subr (e ps r cv) (* 4 (k-length ps))) (else y 0))))
      (tagcase to
        (cv-cellular () (k-note-conversion x (+ n 1)))
        (cv-native () (k-note-conversion x (+ n 2)))
        (else y #u)))))
(define k-latent-of (subr (maxeff kstate spin) (int) k-effs)
  (lambda (t)
    (tagcase (k-get (k-resolve t))
      (ty-poly (bs body) (k-latent-of body))
      (ty-subr (e ps r cv) (the k-effs (cons e nil)))
      (else y nil))))
;; The atoms of `g` that `w` does not cover.
(define k-uncovered (subr (maxeff kstate spin) (k-eff k-eff) k-eff)
  (lambda (g w)
    (cond ((null? g) nil)
          ((k-within? (k-one (car g)) w) (k-uncovered (cdr g) w))
          (else (the k-eff (cons (car g) (k-uncovered (cdr g) w)))))))
;; The second line of an "is expected here" message, where `got` and `want`
;; are procedures: the atoms of `got`'s latent effect that `want`'s does not
;; cover (`Checker::effect_delta`).
(define* k-effect-delta (subr (maxeff kstate spin) (int int) string)
  (lambda (got want)
    (let ((g (k-latent-of got)) (w (k-latent-of want)))
      (if (or (null? g) (null? w))
          ""
          (let ((beyond (k-uncovered (car g) (car w))))
            (if (null? beyond)
                ""
                (k-cat3 k-newline "  beyond what is expected, it has " (k-show-effect beyond))))))))
;; A module reshaped where it is wanted at a type of fewer values
;; (`check-module-rules.fx`'s `k-reshape-at`, which sets this).
(define k-reshape-hook (ref (subr (maxeff checks spin) (kx int int) bool) @t)
  (new (lambda (x got want) #f)))
;; `got ≤ want`, or an error at `x` saying so.
(define k-expect (subr (maxeff checks spin) (kx int int) unit)
  (lambda (x got want)
    (if (k-subtype got want)
        #u
        (let ((c (k-conversion got want)))
          (cond ((not (null? c)) (k-convert-at x got (car c)))
                (((get k-reshape-hook) x got want) #u)
                (else
                 (k-fail (string-append (k-expected-here (k-show-ty want) (k-show-ty got))
                                        (k-effect-delta got want))
                         (k-start x) (k-end x))))))))
;; Bind each, the first first.
(define k-bind-all (subr (maxeff kstate spin) (k-bindings) unit)
  (lambda (bs)
    (if (null? bs) #u (begin (k-bind (car (car bs)) (cdr (car bs))) (k-bind-all (cdr bs))))))
;; `t` for a variable being bound to it: a `nat` of no known size is given
;; one, a variable of its own named after the variable, so that tests of it
;; can teach facts; and a module's abstract types are named too.
(define k-name-nat (subr (maxeff kstate spin) (symbol int) int)
  (lambda (name t)
    (tagcase (k-get (k-resolve t))
      (ty-module (abs ds vs) (k-name-module name t))
      (ty-nat (z)
        (tagcase z
          (sz-finite ()
            (let ((v (k-new-dvar-of name 5)))
              (begin (set k-skolems (cons v (get k-skolems))) (k-ty-new (ty-nat (k-size-var v))))))
          (else w t)))
      (else y t))))
;; Bind each, the first first, a `nat` of no known size given one.
(define k-bind-named (subr (maxeff kstate spin) (k-bindings) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (let ((n (car (car bs))) (t (cdr (car bs))))
          (begin (k-bind n (k-name-nat n t)) (k-bind-named (cdr bs)))))))
(define k-note-letrec (subr (maxeff kstate spin) (k-letrec-bs bool) unit)
  (lambda (bs spins)
    (if (null? bs)
        #u
        (let ((n (extract (car bs) 1)) (t (extract (car bs) 2)))
          (begin (k-note-known n 0)
                 (if spins (set k-recursive (cons (cons n t) (get k-recursive))) #u)
                 (k-note-letrec (cdr bs) spins))))))
;; The group's members are recursion that says `spin`, if `why` says it may
;; not end, and why is kept for an error.
;; Naming `s`: pure, but for a member of a recursive group that may not
;; end, named in the group. Called, the call says `spin`; given away,
;; whoever calls it could loop through it, so naming it does.
(define k-naming-effect (subr (maxeff kmakes spin) (symbol int) k-eff)
  (lambda (s t)
    (let ((spins (if (k-named-has? (get k-recursive) s t) (k-one (a-spin)) (the k-eff nil))))
      (if (and (get k-globals-effects) (k-global? s))
          (k-insert (a-read (r-global s)) spins)
          spins))))
(define k-bind-letrec (subr (maxeff kstate spin) (k-letrec-bs) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (begin (k-bind (extract (car bs) 1) (extract (car bs) 2)) (k-bind-letrec (cdr bs))))))
;; Whether `x` is a lambda, under any type abstractions and ascriptions.
(define k-lambda? (subr (read @globals) (kx) bool)
  (lambda (x)
    (tagcase x
      (x-lambda (ps body a b) #t)
      (x-rlambda (r l a b) #t)
      (x-plambda (bs e a b) (k-lambda? e))
      (x-the (t e a b) (k-lambda? e))
      (else y #f))))
;; How many of `ns` are `n`.
(define k-count-name (subr (read @globals) (k-names symbol) int)
  (lambda (ns n)
    (cond ((null? ns) 0)
          ((symbol=? (car ns) n) (+ 1 (k-count-name (cdr ns) n)))
          (else (k-count-name (cdr ns) n)))))
;; Note each `let` binding of a lambda as known, once bound: of several of
;; one name, each is as many from the innermost as come after it. The
;; names, in order.
(define k-note-let-lambdas (subr (maxeff kstate spin) (k-let-bs) k-names)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((later (k-note-let-lambdas (cdr bs)))
               (n (extract (car bs) 1))
               (x (extract (car bs) 2))
               (noted (if (k-lambda? x) (k-note-known n (k-count-name later n)) #u)))
          (the k-names (cons n later))))))
;; Whether a `plambda` body `x` with effect `e` may be generalized: pure, as
;; the value restriction has it; or an `rlambda`, under ascriptions and other
;; `plambda`s, whose effect only allocates. Making a closure makes no mutable
;; data a type could be generalized over: it holds only variables bound
;; outside.
(define k-rlambda-under? (subr (read @globals) (kx) bool)
  (lambda (x)
    (tagcase x
      (x-rlambda (r l a b) #t)
      (x-plambda (bs e a b) (k-rlambda-under? e))
      (x-the (t e a b) (k-rlambda-under? e))
      (else y #f))))
(define k-only-alloc? (subr kreads (k-eff) bool)
  (lambda (e)
    (or (null? e) (and (tagcase (car e) (a-alloc (r) #t) (else y #f)) (k-only-alloc? (cdr e))))))
(define k-generalizable? (subr kreads (kx k-eff) bool)
  (lambda (x e) (or (null? e) (and (k-rlambda-under? x) (k-only-alloc? e)))))
(define k-letrec-not-lambda (subr (read @globals) (symbol) string)
  (lambda (n)
    (k-cat3 (k-quote (symbol->string n))
            " is bound recursively, so it must be a lambda: "
            "nothing may run before every binding exists")))

;; Binder `v`'s name, quoted.
(define k-quote-dvar (subr kreads (int) string)
  (lambda (v) (k-quote (symbol->string (k-dvar-name v)))))
;; Description `d`, given where one of kind `k` is wanted: a `select` given
;; for a description function, resolved, and taken as one.
(define k-select-fun (subr (maxeff checks spin) (k-desc int int int) k-desc)
  (lambda (d k a b)
    (let ((t (tagcase d (dt (x) x) (df (x) x) (else y -1))))
      (if (and (k-arrow-kind? k) (>= t 0) (tagcase (k-get t) (ty-select (m n) #t) (else y #f)))
          (df (k-resolve-selects t a b))
          d))))
(define k-proj-map (subr (maxeff checks spin) (k-binders k-descs int int) k-map)
  (lambda (bs ds a b)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2))
               ;; A function given as a `select`: resolved first.
               (d (k-select-fun (car ds) k a b))
               (ok (k-desc-of-kind? d k)))
          (if ok
              (cons (cons v d) (k-proj-map (cdr bs) (cdr ds) a b))
              (k-fail (k-cat4 (k-quote-dvar v) " is bound as a " (k-kind-word k)
                              ", and the description given is not one")
                      a b))))))
(define k-param-types (subr checks (k-typed-params k-ids int int) k-bindings)
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
(define k-binding-types (subr kmakes (k-bindings) k-ids)
  (lambda (bs) (if (null? bs) nil (cons (cdr (car bs)) (k-binding-types (cdr bs))))))
(define k-some-untyped? (subr kreads (k-typed-params) bool)
  (lambda (ps)
    (cond ((null? ps) #f)
          ((null? (extract (car ps) 2)) #t)
          (else (k-some-untyped? (cdr ps))))))

(define k-unannotated? (subr kreads (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (k-some-untyped? ps)) (else y #f))))
;; A `lambda` missing parameter types, or a thunk: better told than asked.
(define k-needs-telling? (subr kreads (kx) bool)
  (lambda (x)
    (tagcase x (x-lambda (ps body a b) (or (null? ps) (k-some-untyped? ps))) (else y #f))))))

(define k-part-find (with check-subtype-module k-part-find))
(define k-benv-set (with check-subtype-module k-benv-set))
(define k-label-of? (with check-subtype-module k-label-of?))
(define k-label (with check-subtype-module k-label))
(define k-nlist-tail (with check-subtype-module k-nlist-tail))
(define k-sub-module (with check-subtype-module k-sub-module))
(define k-inv (with check-subtype-module k-inv))
(define k-sub (with check-subtype-module k-sub))
(define k-subtype (with check-subtype-module k-subtype))
(define k-part-index (with check-subtype-module k-part-index))
(define k-rewriting (with check-subtype-module k-rewriting))
(define k-conversion (with check-subtype-module k-conversion))
(define k-convert-at (with check-subtype-module k-convert-at))
(define k-latent-of (with check-subtype-module k-latent-of))
(define k-reshape-hook (with check-subtype-module k-reshape-hook))
(define k-expect (with check-subtype-module k-expect))
(define k-bind-all (with check-subtype-module k-bind-all))
(define k-name-nat (with check-subtype-module k-name-nat))
(define k-bind-named (with check-subtype-module k-bind-named))
(define k-note-letrec (with check-subtype-module k-note-letrec))
(define k-naming-effect (with check-subtype-module k-naming-effect))
(define k-bind-letrec (with check-subtype-module k-bind-letrec))
(define k-lambda? (with check-subtype-module k-lambda?))
(define k-note-let-lambdas (with check-subtype-module k-note-let-lambdas))
(define k-generalizable? (with check-subtype-module k-generalizable?))
(define k-letrec-not-lambda (with check-subtype-module k-letrec-not-lambda))
(define k-quote-dvar (with check-subtype-module k-quote-dvar))
(define k-proj-map (with check-subtype-module k-proj-map))
(define k-param-types (with check-subtype-module k-param-types))
(define k-binding-types (with check-subtype-module k-binding-types))
(define k-some-untyped? (with check-subtype-module k-some-untyped?))
(define k-needs-telling? (with check-subtype-module k-needs-telling?))
(define-type k-trail (select check-subtype-module k-trail))
(define-type k-benv (select check-subtype-module k-benv))
(define-type k-benvs (select check-subtype-module k-benvs))
(define-type k-strail (select check-subtype-module k-strail))
(define-type k-label-list (select check-subtype-module k-label-list))
(define-type k-labels (select check-subtype-module k-labels))
(define-type k-sub-rule (select check-subtype-module k-sub-rule))
(define-type k-saying (select check-subtype-module k-saying))
