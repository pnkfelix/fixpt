;;; The checker, in FX-26: subtyping, errors, and calls that may not end.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ subtyping
;;; `a ≤ b`. Recursive types are compared coinductively: a pair already
;;; being compared is assumed to hold.

(define-type k-trail (ref k-pairs @t))
(define k-bool=? (subr pure (bool bool) bool) (lambda (x y) (if x y (not y))))
(define k-part-find (subr kreads (k-parts symbol) int)
  (lambda (ps l)
    (cond ((null? ps) -1)
          ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2))
          (else (k-part-find (cdr ps) l)))))

;; A subtype question's binder environment, for one side: each `poly`
;; binder in scope, by the name its pair of binders was given, so bodies are
;; compared as they are, not substituted, and a cycle through a `poly` comes
;; back to a pair, and an environment, already on the trail.
(define-type k-benv k-pairs)
;; Both sides' environments.
(define-type k-benvs (pairof k-benv k-benv @t))
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
(define k-benv-effect (subr kmakes (k-benv k-eff) k-eff)
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
                  (a-var (v) (a-var (k-benv-var env v))))
                rest)))))
;; What one subtype question remembers: the pairs assumed (FX-87's trail),
;; each with the environments it was asked under; and the names given to
;; pairs of `poly` binders, by the pair of nodes and the position.
(define-type k-assumed (listof (productof (1 int) (2 int) (3 k-benv) (4 k-benv)) acyclic))
(define-type k-strail (ref k-assumed @t))
(define-type k-label-entry (productof (1 int) (2 int) (3 int) (4 int)))
(define-type k-label-list (listof k-label-entry acyclic))
(define-type k-labels (ref k-label-list @t))
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
;; Each lemma that fits a pair of types: its hypotheses, instantiated.
(define-type k-instances (listof k-hyps acyclic))

;; Modules' types compared, by `check-module-rules.fx`, which sets this.
(define-type k-sub-rule
  (subr (maxeff kstate spin) (int int k-ty k-ty k-benv k-benv k-strail k-labels) bool))
(define k-sub-module (ref k-sub-rule @t) (new (lambda (a b ta tb ea eb trail labels) #f)))

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
                   (dc (a) (tagcase y (dc (b) (k-conv=? a b)) (else z #f)))))
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
            (ty-module (abs ds vs) ((get k-sub-module) a b ta tb ea eb trail labels))
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
                   (dc (c) (tagcase (car ys) (dc (d) (k-conv-same? c d ea eb)) (else z #f)))))
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
                         (k-sub-sum (cdr sa) sb ea eb trail labels))))))))
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
;; A computation checked, and what makes a message of W and G.
(define-type k-checking (subr (maxeff checks spin) () k-te))
(define-type k-saying (subr (maxeff checks spin) (string string string) string))

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
;; The latent effect of `t`, a `subr` under any `poly`s, in a list; or none.
(define-type k-effs (listof k-eff acyclic))
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

;; Whether description `d` is of kind `k`, as a binder of that kind takes.
(define k-desc-of-kind? (subr kreads (k-desc int) bool)
  (lambda (d k)
    (tagcase d
      (dr (r) (or (= k 0) (and (= k 3) (k-place? r))))
      (de (e) (= k 1))
      (dt (t) (or (= k 2) (= k 4)))
      (dz (z) (= k 5))
      (dc (c) (= k 6)))))
;; Binder `v`'s name, quoted.
(define k-quote-dvar (subr kreads (int) string)
  (lambda (v) (k-quote (symbol->string (k-dvar-name v)))))
(define k-proj-map (subr checks (k-binders k-descs int int) k-map)
  (lambda (bs ds a b)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2))
               (d (car ds))
               (ok (k-desc-of-kind? d k)))
          (if ok
              (cons (cons v d) (k-proj-map (cdr bs) (cdr ds) a b))
              (k-fail (k-cat4 (k-quote-dvar v) " is bound as a " (k-kind-debug k)
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
    (tagcase x (x-lambda (ps body a b) (or (null? ps) (k-some-untyped? ps))) (else y #f))))

;;; ------------------------------------------------------------ calls that may not end

;; Whether a procedure of type `t` could be given itself: a cycle in `t`
;; runs through a parameter of a procedure (or the argument of a
;; continuation). A type that is merely recursive, as a list is, does not let
;; anything loop. `path`: the nodes on the way down, newest first, each with
;; whether it was reached through a parameter.
(define-type k-cpath (listof (pairof int bool @t) acyclic))
(define k-on-path? (subr kreads (k-cpath int) bool)
  (lambda (path t) (and (not (null? path)) (or (= (car (car path)) t) (k-on-path? (cdr path) t)))))
;; Whether a node newer than `t` on the path was reached through a parameter.
(define k-newer-param? (subr kreads (k-cpath int) bool)
  (lambda (path t)
    (and (not (= (car (car path)) t)) (or (cdr (car path)) (k-newer-param? (cdr path) t)))))
(define-rec
  (k-cyclic-from? (subr (maxeff kstate spin) (int bool k-cpath) bool)
    (lambda (t by path)
      (let ((t (k-resolve t)))
        (cond ((k-on-path? path t) (or by (k-newer-param? path t)))
              ;; Too deep to follow: it may loop, the cautious answer.
              ((> (k-length path) 64) #t)
              (else
               (let ((p (the k-cpath (cons (cons t by) path))))
                 (tagcase (k-get t)
                   (ty-subr (e ps r cv) (or (k-cyclic-list? ps #t p) (k-cyclic-from? r #f p)))
                   (ty-comp (x a e r) (or (k-cyclic-from? x #t p) (k-cyclic-from? a #f p)))
                   (ty-tag (a h e r) (or (k-cyclic-from? a #f p) (k-cyclic-from? h #f p)))
                   (ty-poly (bs x) (k-cyclic-from? x #f p))
                   (ty-ref (a r) (k-cyclic-from? a #f p))
                   (ty-array (a r) (k-cyclic-from? a #f p))
                   (ty-icell (a r) (k-cyclic-from? a #f p))
                   (ty-markkey (a r) (k-cyclic-from? a #f p))
                   (ty-pair (a b r) (or (k-cyclic-from? a #f p) (k-cyclic-from? b #f p)))
                   (ty-bloblet (fs z r) (k-cyclic-list? fs #f p))
                   (ty-product (ps) (k-cyclic-parts? ps p))
                   (ty-sum (ps) (k-cyclic-parts? ps p))
                   ;; Through its representation; what it was given,
                   ;; cautiously, as if taken as a parameter.
                   (ty-named (g ds)
                     (or (k-cyclic-from? (extract (k-gen-of g) 4) #f p)
                         (k-cyclic-list? (k-desc-types ds) #t p)))
                   (ty-nlist (e z r) (k-cyclic-from? e #f p))
                   (else x #f))))))))
  (k-cyclic-list? (subr (maxeff kstate spin) (k-ids bool k-cpath) bool)
    (lambda (ts by path)
      (and (not (null? ts))
           (or (k-cyclic-from? (car ts) by path) (k-cyclic-list? (cdr ts) by path)))))
  (k-cyclic-parts? (subr (maxeff kstate spin) (k-parts k-cpath) bool)
    (lambda (ps path)
      (and (not (null? ps))
           (or (k-cyclic-from? (extract (car ps) 2) #f path) (k-cyclic-parts? (cdr ps) path))))))
(define k-cyclic? (subr (maxeff kstate spin) (int) bool)
  (lambda (t) (k-cyclic-from? t #f nil)))
;; `f` under any projections and ascriptions.
(define k-under (subr (read @globals) (kx) kx)
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b) (k-under body))
      (x-the (t body a b) (k-under body))
      (else y f))))
;; Whether `k` is named in `x` only as the operator of calls, evaluated as
;; `x` is: not under a `lambda` (which could be called later) or a prompt
;; (whose captures could be composed later).
(define-rec
  (k-only-called? (subr kmakes (kx symbol) bool)
    (lambda (x k)
      (tagcase x
        (x-var (s a b) (not (symbol=? s k)))
        (x-const (t v a b) #t)
        (x-app (f args a b)
          (and (or (tagcase f (x-var (s fa fb) (symbol=? s k)) (else y #f)) (k-only-called? f k))
               (k-only-called-list? args k)))
        (x-lambda (ps body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-plambda (bs body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-rlambda (r l a b) (not (k-has-name? (k-free-vars x) k)))
        (x-letrec (bs body a b) (not (k-has-name? (k-free-vars x) k)))
        (x-prompt (t body h a b) (not (k-has-name? (k-free-vars x) k)))
        (x-let (bs body a b)
          (and (k-only-called-lets? bs k)
               (or (k-has-name? (k-let-names bs nil) k) (k-only-called? body k))))
        (x-letregion (m r i body a b) (or (symbol=? (k-dvar-name r) k) (k-only-called? body k)))
        (x-tagcase (s arms els a b)
          (and (k-only-called? s k)
               (k-only-called-arms? arms k)
               (k-only-called-else? els k)))
        (x-proj (body ds a b) (k-only-called? body k))
        (x-the (t body a b) (k-only-called? body k))
        (x-convention (c body a b) (k-only-called? body k))
        (x-extract (body l a b) (k-only-called? body k))
        (x-sum (l body a b) (k-only-called? body k))
        (x-if (p c d a b) (and (k-only-called? p k) (k-only-called? c k) (k-only-called? d k)))
        (x-begin (xs a b) (k-only-called-list? xs k))
        (x-bloblet (o i xs a b) (k-only-called-list? xs k))
        (x-product (fs a b) (k-only-called-lets? fs k))
        (x-module (items a b) (not (k-has-name? (k-free-vars x) k)))
        (x-with (m body a b) (not (k-has-name? (k-free-vars x) k))))))
  (k-only-called-list? (subr kmakes (kxs symbol) bool)
    (lambda (xs k)
      (or (null? xs) (and (k-only-called? (car xs) k) (k-only-called-list? (cdr xs) k)))))
  (k-only-called-lets? (subr kmakes (k-let-bs symbol) bool)
    (lambda (bs k)
      (or (null? bs)
          (and (k-only-called? (extract (car bs) 2) k) (k-only-called-lets? (cdr bs) k)))))
  (k-only-called-arms? (subr kmakes (k-arms symbol) bool)
    (lambda (arms k)
      (or (null? arms)
          (and (or (k-has-name? (extract (car arms) 3) k) (k-only-called? (extract (car arms) 4) k))
               (k-only-called-arms? (cdr arms) k)))))
  ;; A `tagcase`'s `else` arm, if any, unless its variable is `k`.
  (k-only-called-else? (subr kmakes (k-let-bs symbol) bool)
    (lambda (els k)
      (or (null? els)
          (symbol=? (extract (car els) 1) k)
          (k-only-called? (extract (car els) 2) k)))))
;; Whether an effect has a `comefrom`.
(define k-has-comefrom? (subr kreads (k-eff) bool)
  (lambda (e)
    (and (not (null? e))
         (or (tagcase (car e) (a-comefrom (r) #t) (else y #f)) (k-has-comefrom? (cdr e))))))
;; Whether the receiver of `cwcc` at type `ft` may capture a continuation:
;; its latent effect has a `comefrom`. Unknown counts as may.
(define k-receiver-captures? (subr (maxeff kmakes spin) (int) bool)
  (lambda (ft)
    (let ((c (k-as-subr ft)))
      (or (null? c) (null? (extract (car c) 2))
          (let ((r (k-as-subr (k-resolve (car (extract (car c) 2))))))
            (or (null? r) (k-has-comefrom? (extract (car r) 1))))))))
;; Whether `r`, given to `cwcc`, is a `lambda` whose continuation can only
;; be called while `cwcc` runs, so can only leave it
;; (`docs/research/soundness-findings.md`, F3).
(define k-escape-only? (subr kmakes (kx) bool)
  (lambda (r)
    (tagcase r
      (x-the (t body a b) (k-escape-only? body))
      (x-lambda (ps body a b)
        (and (not (null? ps)) (null? (cdr ps)) (k-only-called? body (extract (car ps) 1))))
      (else y #f))))
;; The name `f` is, under any projections and ascriptions, if a variable.
(define k-callee-name (subr (maxeff (read @globals) (alloc @t)) (kx) (listof symbol acyclic))
  (lambda (f)
    (tagcase f
      (x-proj (body ds a b) (k-callee-name body))
      (x-the (t body a b) (k-callee-name body))
      (x-var (n a b) (the (listof symbol acyclic) (cons n nil)))
      (else y (the (listof symbol acyclic) nil)))))
;; Whether `f` names a known procedure.
(define k-known-callee? (subr (maxeff kstate spin) (kx) bool)
  (lambda (f)
    (let ((s (k-callee-name f)))
      (and (not (null? s)) (let ((t (k-lookup (car s)))) (and (>= t 0) (k-known? (car s))))))))
;; Whether a call of `f` (instantiated to `ft`) may run for an unbounded
;; time beyond what its latent effect says: a call, in a recursive group's
;; lambdas, of the group; or a call through a recursive type of anything but
;; known code (self-application loops with no store at all). A knot through
;; the store needs nothing here: `k-no-knot` makes its type say `spin`.
(define k-may-spin? (subr (maxeff kstate spin) (kx int kxs) bool)
  (lambda (f ft args)
    (let* ((s (k-callee-name f))
           (t (if (null? s) -1 (k-lookup (car s)))))
      (cond ;; A continuation called after `cwcc` has returned comes back to
            ;; it again, as often as it is called: only one that can only
            ;; leave needs no `spin`.
            ;; And the receiver must capture no continuation, which could
            ;; hold a call of `k` and be run after `cwcc` returns (F9): a
            ;; `comefrom` in its latent effect, `cwcc`'s `e` as solved.
            ((and (>= t 0) (string=? (symbol->string (car s)) "cwcc")
                  (k-named-has? (get k-std) (car s) t))
             (or (k-receiver-captures? ft)
                 (not (and (not (null? args)) (null? (cdr args)) (k-escape-only? (car args))))))
            ((and (>= t 0) (k-named-has? (get k-recursive) (car s) t)) #t)
            ((and (>= t 0) (or (k-known? (car s)) (k-named-has? (get k-std) (car s) t))) #f)
            ((k-lambda? (k-under f)) #f)
            (else (k-cyclic? ft))))))
