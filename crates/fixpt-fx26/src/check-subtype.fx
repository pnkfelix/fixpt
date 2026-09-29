;;; The checker, in FX-26: subtyping, and errors.
;;; Part of the checker, `check-types.fx` first (PLAN.md §11, step 10).

;;; ------------------------------------------------------------ subtyping
;;; `a ≤ b`. Recursive types are compared coinductively: a pair already
;;; being compared is assumed to hold.

(define-type k-trail (ref (listof (pairof int int @t) acyclic) @t))
(define k-trail-has? (subr (maxeff (read @globals) (read @t)) ((listof (pairof int int @t) acyclic) int int) bool)
  (lambda (ps a b) (cond ((null? ps) #f) ((and (= (car (car ps)) a) (= (cdr (car ps)) b)) #t) (else (k-trail-has? (cdr ps) a b)))))
(define k-bool=? (subr pure (bool bool) bool) (lambda (x y) (if x y (not y))))
(define k-part-find (subr (maxeff (read @globals) (read @t)) (k-parts symbol) int)
  (lambda (ps l) (cond ((null? ps) -1) ((symbol=? (extract (car ps) 1) l) (extract (car ps) 2)) (else (k-part-find (cdr ps) l)))))

;; A subtype question's binder environment, for one side: each `poly`
;; binder in scope, by the name its pair of binders was given, so bodies are
;; compared as they are, not substituted, and a cycle through a `poly` comes
;; back to a pair, and an environment, already on the trail.
(define-type k-benv (listof (pairof int int @t) acyclic))
(define k-benv-var (subr (maxeff (read @globals) (read @t)) (k-benv int) int)
  (lambda (env v) (cond ((null? env) v) ((= (car (car env)) v) (cdr (car env))) (else (k-benv-var (cdr env) v)))))
;; `env` with `v` named `l`, in place of any name it had: re-entering a scope
;; shadows it, so the environments stay finitely many.
;; Whether a procedure called in convention `a` may be used as one called
;; in `b`: the same, or any of FX-26's own as `fx`; binders by the binders
;; they stand for.
(define k-conv-sub? (subr (maxeff (read @globals) (read @t)) (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (= (k-benv-var ea x) (k-benv-var eb y))) (else z #f)))
      (else y (or (k-conv=? a b) (tagcase b (cv-fx () #t) (else z #f)))))))
;; Whether two conventions are the same, binders by what they stand for.
(define k-conv-same? (subr (maxeff (read @globals) (read @t)) (k-conv k-conv k-benv k-benv) bool)
  (lambda (a b ea eb)
    (tagcase a
      (cv-var (x) (tagcase b (cv-var (y) (= (k-benv-var ea x) (k-benv-var eb y))) (else z #f)))
      (else y (k-conv=? a b)))))
(define k-benv-set (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-benv int int) k-benv)
  (lambda (env v l)
    (letrec ((drop (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-benv) k-benv)
               (lambda (e) (cond ((null? e) nil) ((= (car (car e)) v) (cdr e)) (else (cons (car e) (drop (cdr e))))))))
      (the k-benv (cons (the (pairof int int @t) (cons v l)) (drop env))))))
(define k-benv-within? (subr (maxeff (read @globals) (read @t)) (k-benv k-benv) bool)
  (lambda (x y) (or (null? x) (and (= (k-benv-var y (car (car x))) (cdr (car x))) (k-benv-within? (cdr x) y)))))
(define k-benv=? (subr (maxeff (read @globals) (read @t)) (k-benv k-benv) bool)
  (lambda (x y) (and (= (k-length x) (k-length y)) (k-benv-within? x y))))
;; `a ≤ b` for frozen data: the same, or finite data seen as possibly
;; cyclic, in one place.
(define k-frozen-le? (subr (maxeff (read @globals) spin) (k-region k-region) bool)
  (lambda (a b)
    (or (k-region=? a b)
        (tagcase a
          (r-frozen (p f) (and f (tagcase b (r-frozen (q g) (and (= p q) (not g))) (else y #f))))
          (else y #f)))))
(define k-benv-region (subr (maxeff (read @globals) (read @t)) (k-benv k-region) k-region)
  (lambda (env r)
    (if (null? env)
        r
        (tagcase r
          (r-var (v) (r-var (k-benv-var env v)))
          (r-frozen (p f) (if (< p 0) r (r-frozen (k-benv-var env p) f)))
          (else y r)))))
(define k-benv-effect (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-benv k-eff) k-eff)
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
(define-type k-strail (ref (listof (productof (1 int) (2 int) (3 k-benv) (4 k-benv)) acyclic) @t))
(define-type k-labels (ref (listof (productof (1 int) (2 int) (3 int) (4 int)) acyclic) @t))
(define k-strail-has? (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 int) (2 int) (3 k-benv) (4 k-benv)) acyclic) int int k-benv k-benv) bool)
  (lambda (ps a b ea eb)
    (and (not (null? ps))
         (or (and (= (extract (car ps) 1) a) (and (= (extract (car ps) 2) b)
                  (and (k-benv=? (extract (car ps) 3) ea) (k-benv=? (extract (car ps) 4) eb))))
             (k-strail-has? (cdr ps) a b ea eb)))))
(define k-label (subr kstate (k-labels int int int) int)
  (lambda (labels a b i)
    (letrec ((find (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 int) (2 int) (3 int) (4 int)) acyclic)) int)
               (lambda (ls)
                 (cond ((null? ls) 0)
                       ((and (= (extract (car ls) 1) a) (and (= (extract (car ls) 2) b) (= (extract (car ls) 3) i)))
                        (extract (car ls) 4))
                       (else (find (cdr ls)))))))
      (let ((found (find (get labels))))
        (if (< found 0)
            found
            (let ((l (- -1000 (k-length (get labels)))))
              (begin (set labels (cons (product (1 a) (2 b) (3 i) (4 l)) (get labels))) l)))))))

;; Name each pair of binders of two `poly` nodes `a` and `b` by the pair and
;; its position: the environments inside, for each side.
(define k-name-binders (subr kstate (k-binders k-binders int int int k-benv k-benv k-labels) (pairof k-benv k-benv @t))
  (lambda (ba bb a b i ea eb labels)
    (if (null? ba)
        (cons ea eb)
        (let ((l (k-label labels a b i)))
          (k-name-binders (cdr ba) (cdr bb) a b (+ i 1)
                          (k-benv-set ea (extract (car ba) 1) l) (k-benv-set eb (extract (car bb) 1) l) labels)))))
;; Bounded region binders must have the same bounds.
(define k-same-bounds? (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (k-binders k-binders k-benv k-benv) bool)
  (lambda (ba bb ea eb)
    (or (null? ba)
        (let ((x (k-bound-of (extract (car ba) 1))) (y (k-bound-of (extract (car bb) 1))))
          (and (cond ((and (null? x) (null? y)) #t)
                     ((or (null? x) (null? y)) #f)
                     (else (k-region=? (k-benv-region ea (car x)) (k-benv-region eb (car y)))))
               (k-same-bounds? (cdr ba) (cdr bb) ea eb))))))

(define-rec
  (k-subs-contra (subr (maxeff kstate spin) (k-ids k-ids k-benv k-benv k-strail k-labels) bool)
    (lambda (xs ys ea eb trail labels)
      (cond ((null? xs) (null? ys)) ((null? ys) #f)
            (else (and (k-sub (car ys) (car xs) eb ea trail labels) (k-subs-contra (cdr xs) (cdr ys) ea eb trail labels))))))
  (k-inv (subr (maxeff kstate spin) (int int k-benv k-benv k-strail k-labels) bool)
    (lambda (x y ea eb trail labels) (and (k-sub x y ea eb trail labels) (k-sub y x eb ea trail labels))))
  (k-sub-callable (subr (maxeff kstate spin) (k-callable k-callable k-benv k-benv k-strail k-labels) bool)
    (lambda (ca cb ea eb trail labels)
      (and (= (k-length (extract ca 2)) (k-length (extract cb 2)))
           (k-within? (k-benv-effect ea (extract ca 1)) (k-benv-effect eb (extract cb 1)))
           (k-subs-contra (extract ca 2) (extract cb 2) ea eb trail labels)
           (k-sub (extract ca 3) (extract cb 3) ea eb trail labels))))
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
                  (if (k-sub-rules a b ea eb trail labels)
                      #t
                      (begin
                        (set trail st)
                        (set labels sl)
                        (set trail (cons (product (1 ra) (2 rb) (3 ea) (4 eb)) (get trail)))
                        (k-sub-by-lemmas (k-lemma-instances (the (listof k-lemma acyclic) (reverse (get k-lemmas))) ra rb)
                                         ea eb trail labels)))))))))
  (k-sub-by-lemmas (subr (maxeff kstate spin) ((listof k-hyps acyclic) k-benv k-benv k-strail k-labels) bool)
    (lambda (insts ea eb trail labels)
      (and (not (null? insts))
           (let ((st (get trail)) (sl (get labels)))
             (or (k-sub-hyps (car insts) ea eb trail labels)
                 (begin (set trail st) (set labels sl) (k-sub-by-lemmas (cdr insts) ea eb trail labels)))))))
  (k-sub-hyps (subr (maxeff kstate spin) (k-hyps k-benv k-benv k-strail k-labels) bool)
    (lambda (hs ea eb trail labels)
      (or (null? hs) (and (k-sub (car (car hs)) (cdr (car hs)) ea eb trail labels) (k-sub-hyps (cdr hs) ea eb trail labels)))))
  (k-same-ty? (subr (maxeff kstate spin) (int int) bool)
    (lambda (x y)
      (and (k-sub x y (the k-benv nil) (the k-benv nil) (the k-strail (new nil)) (the k-labels (new nil)))
           (k-sub y x (the k-benv nil) (the k-benv nil) (the k-strail (new nil)) (the k-labels (new nil))))))
  ;; Each lemma of `ls` that fits `a` and `b`: its hypotheses, instantiated.
  (k-lemma-instances (subr (maxeff kstate spin) ((listof k-lemma acyclic) int int) (listof k-hyps acyclic))
    (lambda (ls a b)
      (if (null? ls)
          nil
          (let* ((l (car ls))
                 (m (the (ref k-map @t) (new nil)))
                 (seen (the (ref (listof (pairof int int @t) acyclic) @t) (new nil)))
                 (fits (and (k-match-ty l (extract l 2) a m seen) (k-match-ty l (extract l 3) b m seen)
                            (k-all-bound? (extract l 1) (get m))))
                 (mine (if fits (the (listof k-hyps acyclic) (cons (k-subst-hyps (extract l 4) (get m)) nil)) (the (listof k-hyps acyclic) nil)))
                 (rest (k-lemma-instances (cdr ls) a b)))
            (if (null? mine) rest (the (listof k-hyps acyclic) (cons (car mine) rest)))))))
  ;; Whether `t` is `pat` with the lemma's binders standing for something,
  ;; recorded in `m`.
  (k-match-ty (subr (maxeff kstate spin) (k-lemma int int (ref k-map @t) (ref (listof (pairof int int @t) acyclic) @t)) bool)
    (lambda (l pat t m seen)
      (let ((pat (k-resolve pat)) (t (k-resolve t)))
        (if (k-pair-seen? (get seen) pat t)
            #t
            (begin
              (set seen (cons (cons pat t) (get seen)))
              (let ((bs (extract l 1)) (tt (k-get t)))
                (letrec ((mt (subr (maxeff (read @globals) kstate spin) (int int) bool) (lambda (x y) (k-match-ty l x y m seen)))
                         (mr (subr (maxeff (read @globals) kstate spin) (k-region k-region) bool) (lambda (r q) (k-match-region bs r q m)))
                         (same (subr (maxeff (read @globals) kstate spin) () bool) (lambda () (k-same-ty? pat t))))
                  (tagcase (k-get pat)
                    (ty-var (v)
                      (if (k-binder-has? bs v)
                          (let ((f (k-map-find (get m) v)))
                            (if (null? f)
                                (begin (set m (cons (cons v (dt t)) (get m))) #t)
                                (tagcase (cdr (car f)) (dt (u) (k-same-ty? u t)) (else z #f))))
                          (same)))
                    (ty-named (g xs) (tagcase tt (ty-named (h ys) (and (= g h) (k-match-descs l xs ys m seen))) (else z (same))))
                    (ty-pair (a1 b1 r1) (tagcase tt (ty-pair (a2 b2 r2) (and (mr r1 r2) (mt a1 a2) (mt b1 b2))) (else z (same))))
                    (ty-ref (x r) (tagcase tt (ty-ref (y q) (and (mr r q) (mt x y))) (else z (same))))
                    (ty-array (x r) (tagcase tt (ty-array (y q) (and (mr r q) (mt x y))) (else z (same))))
                    (ty-icell (x r) (tagcase tt (ty-icell (y q) (and (mr r q) (mt x y))) (else z (same))))
                    (ty-product (ps) (tagcase tt (ty-product (qs) (k-match-parts l ps qs m seen)) (else z (same))))
                    (ty-sum (ps) (tagcase tt (ty-sum (qs) (k-match-parts l ps qs m seen)) (else z (same))))
                    (ty-subr (e1 p1 r1 c1)
                      (tagcase tt
                        (ty-subr (e2 p2 r2 c2)
                          (and (k-conv=? c1 c2) (k-eff=? e1 e2) (= (k-length p1) (k-length p2)) (k-match-list l p1 p2 m seen) (mt r1 r2)))
                        (else z (same))))
                    (else z (same))))))))))
  (k-match-list (subr (maxeff kstate spin) (k-lemma k-ids k-ids (ref k-map @t) (ref (listof (pairof int int @t) acyclic) @t)) bool)
    (lambda (l xs ys m seen) (or (null? xs) (and (k-match-ty l (car xs) (car ys) m seen) (k-match-list l (cdr xs) (cdr ys) m seen)))))
  (k-match-parts (subr (maxeff kstate spin) (k-lemma k-parts k-parts (ref k-map @t) (ref (listof (pairof int int @t) acyclic) @t)) bool)
    (lambda (l ps qs m seen)
      (and (= (k-length ps) (k-length qs))
           (letrec ((each (subr (maxeff (read @globals) kstate spin) (k-parts k-parts) bool)
                          (lambda (ps qs)
                            (or (null? ps)
                                (and (symbol=? (extract (car ps) 1) (extract (car qs) 1))
                                     (k-match-ty l (extract (car ps) 2) (extract (car qs) 2) m seen)
                                     (each (cdr ps) (cdr qs)))))))
             (each ps qs)))))
  (k-match-descs (subr (maxeff kstate spin) (k-lemma (listof k-desc acyclic) (listof k-desc acyclic) (ref k-map @t) (ref (listof (pairof int int @t) acyclic) @t)) bool)
    (lambda (l xs ys m seen)
      (or (null? xs)
          (and (tagcase (car xs)
                 (dt (a) (tagcase (car ys) (dt (b) (k-match-ty l a b m seen)) (else z #f)))
                 (dr (r) (tagcase (car ys) (dr (q) (k-match-region (extract l 1) r q m)) (else z #f)))
                 (de (d) (tagcase (car ys) (de (e) (k-match-effect (extract l 1) d e m)) (else z #f)))
                 (dz (a) (tagcase (car ys) (dz (b) (k-size=? a b)) (else z #f)))
                 (dc (a) (tagcase (car ys) (dc (b) (k-conv=? a b)) (else z #f))))
               (k-match-descs l (cdr xs) (cdr ys) m seen)))))
  (k-match-region (subr (maxeff kstate spin) (k-binders k-region k-region (ref k-map @t)) bool)
    (lambda (bs r q m)
      (tagcase r
        (r-var (v)
          (if (k-binder-has? bs v)
              (let ((f (k-map-find (get m) v)))
                (if (null? f) (begin (set m (cons (cons v (dr q)) (get m))) #t) (tagcase (cdr (car f)) (dr (x) (k-region=? x q)) (else z #f))))
              (k-region=? r q)))
        (else z (k-region=? r q)))))
  (k-match-effect (subr (maxeff kstate spin) (k-binders k-eff k-eff (ref k-map @t)) bool)
    (lambda (bs d e m)
      (let ((v (if (and (not (null? d)) (null? (cdr d))) (tagcase (car d) (a-var (x) (if (k-binder-has? bs x) x -1)) (else z -1)) -1)))
        (if (< v 0)
            (k-eff=? d e)
            (let ((f (k-map-find (get m) v)))
              (if (null? f) (begin (set m (cons (cons v (de e)) (get m))) #t) (tagcase (cdr (car f)) (de (x) (k-eff=? x e)) (else z #f))))))))
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
             (let* ((ta (k-get a)) (tb (k-get b))
                    (same-named (tagcase ta (ty-named (g xs) (tagcase tb (ty-named (h ys) (= g h)) (else z #f))) (else z #f)))
                    (a-void (tagcase ta (ty-void () #t) (else z #f)))
                    ;; Inside a generative type's own conversions, its name
                    ;; is its representation; everywhere else only itself.
                    (a-open (tagcase ta (ty-named (g xs) (k-has-id? (get k-transparent) g)) (else z #f)))
                    (b-open (tagcase tb (ty-named (g xs) (k-has-id? (get k-transparent) g)) (else z #f))))
               (cond
                ((and (not same-named) (not a-void) a-open)
                 (tagcase ta (ty-named (g xs) (k-sub (k-unfold g xs) b ea eb trail labels)) (else z #f)))
                ((and (not same-named) (not a-void) b-open)
                 (tagcase tb (ty-named (g ys) (k-sub a (k-unfold g ys) ea eb trail labels)) (else z #f)))
                (else
               (if (and (tagcase ta (ty-comp (x y e r) #t) (else z #f)) (tagcase tb (ty-subr (e ps r cv) #t) (else z #f)))
                   (k-sub-callable (car (k-as-subr a)) (car (k-as-subr b)) ea eb trail labels)
                   (tagcase ta
                     (ty-void () #t)
                     (ty-base (x) (tagcase tb (ty-base (y) (symbol=? x y)) (else z #f)))
                     ;; A natural is an integer; one of a known size, a natural.
                     (ty-nat (m) (tagcase tb (ty-base (y) (symbol=? y 'int)) (ty-nat (n) (k-size-le? m n)) (else z #f)))
                     (ty-var (x) (tagcase tb (ty-var (y) (= (k-benv-var ea x) (k-benv-var eb y))) (else z #f)))
                     (ty-subr (e ps r cv)
                       (tagcase tb
                         (ty-subr (e2 ps2 r2 cv2)
                           (and (k-conv-sub? cv cv2 ea eb) (k-sub-callable (car (k-as-subr a)) (car (k-as-subr b)) ea eb trail labels)))
                         (else z #f)))
                     (ty-ref (x r) (tagcase tb (ty-ref (y s) (and (k-region=? (k-benv-region ea r) (k-benv-region eb s)) (k-inv x y ea eb trail labels))) (else z #f)))
                     (ty-array (x r) (tagcase tb (ty-array (y s) (and (k-region=? (k-benv-region ea r) (k-benv-region eb s)) (k-inv x y ea eb trail labels))) (else z #f)))
                     (ty-icell (x r) (tagcase tb (ty-icell (y s) (and (k-region=? (k-benv-region ea r) (k-benv-region eb s)) (k-inv x y ea eb trail labels))) (else z #f)))
                     (ty-place (r) (tagcase tb (ty-place (s) (k-region=? (k-benv-region ea r) (k-benv-region eb s))) (else z #f)))
                     (ty-pair (x1 x2 r)
                       (tagcase tb
                         (ty-pair (y1 y2 s)
                           (and (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))
                                ;; Frozen pairs cannot be written, so, as a
                                ;; frozen bloblet's fields, their contents are
                                ;; covariant; and finite data may be seen as
                                ;; possibly cyclic.
                                (if (tagcase r (r-frozen (p f) #t) (else z #f))
                                    (and (k-sub x1 y1 ea eb trail labels) (k-sub x2 y2 ea eb trail labels))
                                    (and (k-inv x1 y1 ea eb trail labels) (k-inv x2 y2 ea eb trail labels)))))
                         ;; A finite list is a `nlist` of some length.
                         (ty-nlist (y sz s)
                           (and (tagcase sz (sz-finite () #t) (else z #f))
                                (tagcase r (r-frozen (p f) f) (else z #f))
                                (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))
                                (k-sub x1 y ea eb trail labels)
                                (k-sub x2 b ea eb trail labels)))
                         (else z #f)))
                     (ty-tag (a1 h1 d1 r1)
                       (tagcase tb
                         (ty-tag (a2 h2 d2 r2)
                           (and (k-region=? (k-benv-region ea r1) (k-benv-region eb r2)) (k-eff=? (k-benv-effect ea d1) (k-benv-effect eb d2))
                                (k-inv a1 a2 ea eb trail labels) (k-inv h1 h2 ea eb trail labels)))
                         (else z #f)))
                     (ty-comp (t1 a1 d1 r1)
                       (tagcase tb
                         (ty-comp (t2 a2 d2 r2)
                           (and (k-region=? (k-benv-region ea r1) (k-benv-region eb r2)) (k-within? (k-benv-effect ea d1) (k-benv-effect eb d2))
                                (k-sub t2 t1 eb ea trail labels) (k-sub a1 a2 ea eb trail labels)))
                         (else z #f)))
                     (ty-markkey (x r) (tagcase tb (ty-markkey (y s) (and (k-region=? (k-benv-region ea r) (k-benv-region eb s)) (k-inv x y ea eb trail labels))) (else z #f)))
                     (ty-bloblet (fa za r)
                       (tagcase tb
                         (ty-bloblet (fb zb s)
                           (and (if za (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s)) (k-region=? (k-benv-region ea r) (k-benv-region eb s)))
                                (k-bool=? za zb) (= (k-length fa) (k-length fb))
                                (k-sub-fields fa fb za ea eb trail labels)))
                         (else z #f)))
                     (ty-product (pa)
                       (tagcase tb (ty-product (pb) (and (= (k-length pa) (k-length pb)) (k-sub-product pa pb ea eb trail labels))) (else z #f)))
                     (ty-sum (sa) (tagcase tb (ty-sum (sb) (k-sub-sum sa sb ea eb trail labels)) (else z #f)))
                     (ty-poly (ba xa)
                       (tagcase tb
                         (ty-poly (bb xb)
                           (and (= (k-length ba) (k-length bb)) (k-same-kinds? ba bb)
                                (let* ((named (k-name-binders ba bb a b 0 ea eb labels))
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
                           (and (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s)) (k-size-le? m n) (k-sub x y ea eb trail labels)))
                         (ty-pair (y tail s)
                           (let ((k (k-size-as-lit m)))
                             (and (k-frozen-le? (k-benv-region ea r) (k-benv-region eb s))
                                  (k-sub x y ea eb trail labels)
                                  (tagcase m
                                    ;; A `nlist` of some length has for its tail the same type.
                                    (sz-finite () (k-sub a tail ea eb trail labels))
                                    (else w (or (= k 0) (k-sub (k-ty-new (ty-nlist x (k-tail-size m) r)) tail ea eb trail labels)))))))
                         (else z #f)))
                     ;; A generative type is related only to itself, argument
                     ;; by argument, as its variance says.
                     (ty-named (g xs)
                       (tagcase tb
                         (ty-named (h ys) (and (= g h) (k-sub-descs xs ys (extract (k-gen-of g) 3) ea eb trail labels)))
                         (else z #f)))
                     (else z #f))))))))))))
  (k-sub-descs (subr (maxeff kstate spin) ((listof k-desc acyclic) (listof k-desc acyclic) k-ids k-benv k-benv k-strail k-labels) bool)
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
                   (dr (r) (tagcase (car ys) (dr (q) (k-region=? (k-benv-region ea r) (k-benv-region eb q))) (else z #f)))
                   (de (d)
                     (tagcase (car ys)
                       (de (e) (let ((d2 (k-benv-effect ea d)) (e2 (k-benv-effect eb e)))
                                 (cond ((= v 0) (k-within? d2 e2)) ((= v 1) (k-within? e2 d2)) (else (k-eff=? d2 e2)))))
                       (else z #f)))
                   (dz (m) (tagcase (car ys) (dz (n) (k-size-eq? m n)) (else z #f)))
                   (dc (c) (tagcase (car ys) (dc (d) (k-conv-same? c d ea eb)) (else z #f)))))
               (k-sub-descs (cdr xs) (cdr ys) (cdr vs) ea eb trail labels)))))
  (k-sub-fields (subr (maxeff kstate spin) (k-ids k-ids bool k-benv k-benv k-strail k-labels) bool)
    (lambda (fa fb frozen ea eb trail labels)
      (cond ((null? fa) #t)
            (else (and (k-sub (car fa) (car fb) ea eb trail labels) (or frozen (k-sub (car fb) (car fa) eb ea trail labels))
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
                    (and (>= y 0) (k-sub (extract (car sa) 2) y ea eb trail labels) (k-sub-sum (cdr sa) sb ea eb trail labels))))))))
(define k-subtype (subr (maxeff kstate spin) (int int) bool)
  (lambda (a b)
    (k-sub a b (the k-benv nil) (the k-benv nil)
           (the k-strail (new nil)) (the k-labels (new nil)))))
(define k-part-index (subr (maxeff (read @globals) (read @t)) (k-parts symbol int) int)
  (lambda (ps l i) (cond ((null? ps) -1) ((symbol=? (extract (car ps) 1) l) i) (else (k-part-index (cdr ps) l (+ i 1))))))

;;; ------------------------------------------------------------ errors

;; Run `f`, and if it fails at `a`..`b` with "a W is expected here, and
;; this is a G", fail instead with what `say` makes of W and G.
(define k-expected-split (subr (maxeff (read @globals) spin) (string) string)
  (lambda (m) (if (= (string-search m "a " 0) 0) (substring m 2 (string-length m)) "")))
(define k-sep string " is expected here, and this is a ")

(define k-rewriting (subr (maxeff (read @globals) checks spin) ((subr (maxeff checks spin) () k-te) int int (subr (maxeff checks spin) (string string string) string)) k-te)
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
(define k-prefixing (subr (maxeff (read @globals) checks) ((subr checks () k-te) int int (subr checks () string)) k-te)
  (lambda (f a b prefix)
    (let ((r (prompt k-tag (k-done (f)) (lambda (r) r))))
      (tagcase r
        (k-done (te) te)
        (k-err (m ea eb) (if (and (= ea a) (= eb b)) (k-fail (string-append (prefix) m) ea eb) (k-fail m ea eb)))
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
            (if (and (not (k-conv=? from to)) (k-subtype (k-ty-new (ty-subr e ps r to)) want)) (cons to nil) nil))
          (else y nil)))
      (else y nil))))
;; Conversion `code` at `x`'s span, among the facts `checked-extracts` gives.
(define k-note-conversion (subr (maxeff checks spin) (kx int) unit)
  (lambda (x code)
    (set k-extracts (cons (product (1 (k-start x)) (2 (k-end x)) (3 (- -1000 code))) (get k-extracts)))))
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
;; `got ≤ want`, or an error at `x` saying so.
(define k-expect (subr (maxeff checks spin) (kx int int) unit)
  (lambda (x got want)
    (if (k-subtype got want)
        #u
        (let ((c (k-conversion got want)))
          (if (null? c)
              (k-fail (k-cat4 "a " (k-show-ty want) " is expected here, and this is a " (k-show-ty got)) (k-start x) (k-end x))
              (k-convert-at x got (car c)))))))
;; Bind each, the first first.
(define k-bind-all (subr (maxeff kstate spin) (k-bindings) unit)
  (lambda (bs) (if (null? bs) #u (begin (k-bind (car (car bs)) (cdr (car bs))) (k-bind-all (cdr bs))))))
;; `t` for a variable being bound to it: a `nat` of no known size is given
;; one, a variable of its own named after the variable, so that tests of it
;; can teach facts.
(define k-name-nat (subr (maxeff kstate spin) (symbol int) int)
  (lambda (name t)
    (tagcase (k-get (k-resolve t))
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
        (begin (k-bind (car (car bs)) (k-name-nat (car (car bs)) (cdr (car bs)))) (k-bind-named (cdr bs))))))
(define k-note-letrec (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 int) (3 kx)) acyclic) bool) unit)
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
(define k-naming-effect (subr (maxeff (read @globals) (read @t) (alloc @t) spin) (symbol int) k-eff)
  (lambda (s t)
    (let ((spins (if (k-named-has? (get k-recursive) s t) (the k-eff (cons (a-spin) nil)) (the k-eff nil))))
      (if (and (get k-globals-effects) (k-global? s)) (k-insert (a-read (r-global s)) spins) spins))))
(define k-bind-letrec (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 int) (3 kx)) acyclic)) unit)
  (lambda (bs) (if (null? bs) #u (begin (k-bind (extract (car bs) 1) (extract (car bs) 2)) (k-bind-letrec (cdr bs))))))
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
  (lambda (ns n) (cond ((null? ns) 0) ((symbol=? (car ns) n) (+ 1 (k-count-name (cdr ns) n))) (else (k-count-name (cdr ns) n)))))
;; Note each `let` binding of a lambda as known, once bound: of several of
;; one name, each is as many from the innermost as come after it. The
;; names, in order.
(define k-note-let-lambdas (subr (maxeff kstate spin) ((listof (productof (1 symbol) (2 kx)) acyclic)) k-names)
  (lambda (bs)
    (if (null? bs)
        nil
        (let* ((later (k-note-let-lambdas (cdr bs)))
               (n (extract (car bs) 1))
               (noted (if (k-lambda? (extract (car bs) 2)) (k-note-known n (k-count-name later n)) #u)))
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
(define k-only-alloc? (subr (maxeff (read @globals) (read @t)) (k-eff) bool)
  (lambda (e) (or (null? e) (and (tagcase (car e) (a-alloc (r) #t) (else y #f)) (k-only-alloc? (cdr e))))))
(define k-generalizable? (subr (maxeff (read @globals) (read @t)) (kx k-eff) bool)
  (lambda (x e) (or (null? e) (and (k-rlambda-under? x) (k-only-alloc? e)))))
(define k-letrec-not-lambda (subr (read @globals) (symbol) string)
  (lambda (n)
    (string-append (k-quote (symbol->string n))
                   " is bound recursively, so it must be a lambda: nothing may run before every binding exists")))

(define k-proj-map (subr checks (k-binders (listof k-desc acyclic) int int) k-map)
  (lambda (bs ds a b)
    (if (null? bs)
        nil
        (let* ((v (extract (car bs) 1)) (k (extract (car bs) 2))
               (d (car ds))
               (ok (tagcase d (dr (r) (or (= k 0) (and (= k 3) (k-place? r)))) (de (e) (= k 1)) (dt (t) (or (= k 2) (= k 4))) (dz (z) (= k 5)) (dc (c) (= k 6)))))
          (if ok
              (cons (cons v d) (k-proj-map (cdr bs) (cdr ds) a b))
              (k-fail (k-cat4 (k-quote (symbol->string (k-dvar-name v))) " is bound as a " (k-kind-debug k)
                              ", and the description given is not one")
                      a b))))))
(define k-param-types (subr checks ((listof (productof (1 symbol) (2 k-ids)) acyclic) k-ids int int) k-bindings)
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
(define k-binding-types (subr (maxeff (read @globals) (read @t) (alloc @t)) (k-bindings) k-ids)
  (lambda (bs) (if (null? bs) nil (cons (cdr (car bs)) (k-binding-types (cdr bs))))))
(define k-some-untyped? (subr (maxeff (read @globals) (read @t)) ((listof (productof (1 symbol) (2 k-ids)) acyclic)) bool)
  (lambda (ps) (cond ((null? ps) #f) ((null? (extract (car ps) 2)) #t) (else (k-some-untyped? (cdr ps))))))

(define k-unannotated? (subr (maxeff (read @globals) (read @t)) (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (k-some-untyped? ps)) (else y #f))))
;; A `lambda` missing parameter types, or a thunk: better told than asked.
(define k-needs-telling? (subr (maxeff (read @globals) (read @t)) (kx) bool)
  (lambda (x) (tagcase x (x-lambda (ps body a b) (or (null? ps) (k-some-untyped? ps))) (else y #f))))
