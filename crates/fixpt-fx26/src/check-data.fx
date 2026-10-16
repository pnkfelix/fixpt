;;; The `data` kind (`docs/fx26.md`, "The `data` kind"): what a `data`
;;; binder takes, and at which place. `(t data p)` takes data whose frozen
;;; parts are in the heap or in place `p`; plain `(t data)`, data in the heap
;;; only (`docs/research/shapes.md`; `soundness-findings.md`, F13). The
;;; Rust checker's `is_data`, `is_data_at` and `data_places`, rule for rule.
;;; And what may be sent to a process, its `sendable` kind with it
;;; (`k-untransmissible`, the Rust checker's `untransmissible`).

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((check-types-types (load-module "fx26:check-types-types.fx"))
       (check-print-types (load-module "fx26:check-print-types.fx"))
       (check-print-parts-types (load-module "fx26:check-print-parts-types.fx"))
       (check-expect-types (load-module "fx26:check-expect-types.fx"))
       (check-effects-types (load-module "fx26:check-effects-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-sub-env-types (load-module "fx26:check-sub-env-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((check-types (select check-types-types check-types-sig))
           (check-print (select check-print-types check-print-sig))
           (check-expect (select check-expect-types check-expect-sig))
           (check-effects (select check-effects-types check-effects-sig))
           (check-subst (select check-subst-types check-subst-sig))
           (check-print-parts (select check-print-parts-types check-print-parts-sig))
           (check-sub-env (select check-sub-env-types check-sub-env-sig)))
    (module

;; The types it uses of the files before it.
(hide (include check-types-types))
;; What it uses of the modules it is given: all of each, hidden.
(hide (include check-types) (include check-print-parts) (include check-print)
      (include check-expect) (include check-effects) (include check-subst))

;; Data, and what a wider bloblet type may forget: `check-sub-env.fx`'s,
;; which the subtype test, before this file, asks.
(import check-sub-env k-data-place k-data-var-place k-is-data? k-is-data-at?)

(define k-region-in? (->* (k-regions k-region) bool)
  (lambda (rs q) (and (not (null? rs)) (or (k-region=? (car rs) q) (k-region-in? (cdr rs) q)))))
;; `q` added to `out`, unless it is the heap or there already.
(define k-note-place (->* ((ref k-regions @t) k-region) unit)
  (lambda (out q)
    (if (or (k-region=? q (r-heap)) (k-region-in? (get out) q))
        #u
        (set out (cons q (get out))))))
;; The places, other than the heap, that data `t`'s parts are in, into `out`.
(define-rec
  (k-data-places (->* (int int (ref k-regions @t)) unit)
    (lambda (t seen out)
      (let ((t (k-resolve t)))
        (if (k-visit? t seen)
            #u
            (tagcase (k-get t)
              (ty-var (v) (if (k-data-var? v) (k-note-place out (k-data-var-place v)) #u))
              (ty-product (ps) (k-data-places-parts ps seen out))
              (ty-sum (ps) (k-data-places-parts ps seen out))
              (ty-union (ms) (k-data-places-list ms seen out))
              (ty-pair (a b r nl)
                (begin (k-note-place out (k-data-place r)) (k-data-places a seen out)
                       (k-data-places b seen out)))
              (ty-bloblet (fs z r)
                (begin (k-note-place out (k-data-place r)) (k-data-places-list fs seen out)))
              (ty-nlist (e z r)
                (begin (k-note-place out (k-data-place r)) (k-data-places e seen out)))
              (else y #u))))))
  (k-data-places-parts (->* (k-parts int (ref k-regions @t)) unit)
    (lambda (ps seen out)
      (if (null? ps)
          #u
          (begin (k-data-places (extract (car ps) 2) seen out)
                 (k-data-places-parts (cdr ps) seen out)))))
  (k-data-places-list (->* (k-ids int (ref k-regions @t)) unit)
    (lambda (ts seen out)
      (if (null? ts)
          #u
          (begin (k-data-places (car ts) seen out) (k-data-places-list (cdr ts) seen out))))))

;; The variable a binder's bound names, or -1.
(define k-bound-var (->* (k-regions) int)
  (lambda (bd) (if (null? bd) -1 (tagcase (car bd) (r-var (p) p) (else y -1)))))
;; The type a description is, or -1.
(define k-desc-type-id (->* (k-desc) int)
  (lambda (d) (tagcase d (dt (t) t) (else z -1))))
;; Whether `v` is among binders `bs`.
(define k-binder-in? (->* (k-binders int) bool)
  (lambda (bs v)
    (and (not (null? bs)) (or (= (extract (car bs) 1) v) (k-binder-in? (cdr bs) v)))))
;; `m` with place binder `p` solved as where data `t` is: the one place its
;; parts are in, or the heap; unsolved if they are in two.
(define k-solve-data-place (->* (int int k-map) k-map)
  (lambda (p t m)
    (let ((out (the (ref k-regions @t) (new nil))))
      (begin
        (k-data-places t (k-new-epoch) out)
        (let ((ps (get out)))
          (cond ((null? ps) (cons (cons p (dr (r-heap))) m))
                ((null? (cdr ps)) (cons (cons p (dr (car ps))) m))
                (else m)))))))
;; `m`, with each `data` binder's place that nothing else says solved as where
;; its data is (F13).
(define k-data-places-solved (->* (k-binders k-binders k-map) k-map)
  (lambda (kinds all m)
    (if (null? kinds)
        m
        (let* ((v (extract (car kinds) 1))
               (p (if (= (extract (car kinds) 2) 4) (k-bound-var (k-bound-of v)) -1))
               (f (k-map-find m v))
               (t (if (null? f) -1 (k-desc-type-id (cdr (car f))))))
          (k-data-places-solved
           (cdr kinds) all
           (if (and (>= p 0) (>= t 0) (null? (k-map-find m p)) (k-binder-in? all p))
               (k-solve-data-place p t m)
               m))))))
;;; ------------------------------------------------------------ transmissible

;; The generative types of processes (`check::ADDR`, `INBOX`, `PROCESS`).
(define k-addr-index int 10)
(define k-inbox-index int 11)
(define k-process-index int 12)

;; Why a value of type `t` may not cross into another process, or "" if it
;; may (the Rust checker's `untransmissible`), `bound` the binders of the
;; `poly`s around.
(define-rec
  (k-untransmissible (->* (int k-ids k-ids) string)
    (lambda (t seen bound)
      (let ((t (k-resolve t)))
        (if (k-has-id? seen t)
            ""
            (let ((seen (the k-ids (cons t seen))))
              (tagcase (k-get t)
                (ty-base (s) "") (ty-void () "") (ty-nil () "") (ty-nat (z) "") (ty-false () "")
                (ty-proving (p q) "")
                (ty-var (v) (k-var-untransmissible v bound))
                (ty-product (ps) (k-parts-untransmissible ps seen bound))
                (ty-sum (ps) (k-parts-untransmissible ps seen bound))
                (ty-union (ms) (k-ids-untransmissible ms seen bound))
                (ty-pair (x y r nl)
                  (k-or-else (k-data-at r bound "pair")
                             (lambda () (k-ids-untransmissible (the k-ids (list x y)) seen bound))))
                (ty-nlist (x z r)
                  (k-or-else (k-data-at r bound "list")
                             (lambda () (k-untransmissible x seen bound))))
                (ty-array (x z r)
                  (k-or-else (k-data-at r bound "array")
                             (lambda () (k-untransmissible x seen bound))))
                (ty-ref (x r)
                  (k-or-else (k-data-at r bound "reference")
                             (lambda () (k-untransmissible x seen bound))))
                (ty-bloblet (fs z r)
                  (k-or-else (if z "" (k-data-at r bound "bloblet"))
                             (lambda () (k-ids-untransmissible fs seen bound))))
                (ty-icell (x r) (k-untransmissible x seen bound))
                (ty-named (w ds) (k-named-untransmissible w ds t bound))
                (ty-subr (e ps res cv)
                  (let ((bad (k-crossing-bad e bound)))
                    (if (null? bad)
                        (k-ids-untransmissible (k-snoc ps res) seen bound)
                        (string-append "a procedure that has " (k-show-effect bad)))))
                (ty-poly (bs body) (k-untransmissible body seen (k-binder-ids bs bound)))
                (else y (string-append "a " (k-show-ty t)))))))))
  (k-parts-untransmissible (->* (k-parts k-ids k-ids) string)
    (lambda (ps seen bound)
      (if (null? ps)
          ""
          (k-or-else (k-untransmissible (extract (car ps) 2) seen bound)
                     (lambda () (k-parts-untransmissible (cdr ps) seen bound))))))
  (k-ids-untransmissible (->* (k-ids k-ids k-ids) string)
    (lambda (ts seen bound)
      (if (null? ts)
          ""
          (k-or-else (k-untransmissible (car ts) seen bound)
                     (lambda () (k-ids-untransmissible (cdr ts) seen bound)))))))
;; `why`, or if it is "", what `next` says.
(define k-or-else (->* (string (subr (maxeff kstate spin) () string)) string)
  (lambda (why next) (if (string=? why "") (next) why)))
(define k-snoc (->* (k-ids int) k-ids)
  (lambda (xs x) (if (null? xs) (the k-ids (list x)) (cons (car xs) (k-snoc (cdr xs) x)))))
(define k-binder-ids (->* (k-binders k-ids) k-ids)
  (lambda (bs acc) (if (null? bs) acc (cons (extract (car bs) 1) (k-binder-ids (cdr bs) acc)))))
;; A type variable: transmissible if a binder around, of kind `sendable`,
;; or of kind `data` in the heap.
(define k-var-untransmissible (->* (int k-ids) string)
  (lambda (v bound)
    (cond ((k-has-id? bound v) "")
          ((= (k-dvar-kind v) 8) "")
          ((k-heap-data-var? v) "")
          (else (k-cat3 "a `" (symbol->string (k-dvar-name v)) "`, which could be anything")))))
;; Whether `v` is of kind `data` in the heap.
(define k-heap-data-var? (->* (int) bool)
  (lambda (v)
    (and (k-data-var? v)
         (let ((b (k-bound-of v))) (or (null? b) (k-region=? (car b) (r-heap)))))))
;; Data at `r`: transmissible only frozen in the heap, or at a binder around.
(define k-data-at (->* (k-region k-ids string) string)
  (lambda (r bound what)
    (cond ((tagcase r (r-frozen (p f) (< p 0)) (else y #f)) "")
          ((tagcase r (r-var (v) (k-has-id? bound v)) (else y #f)) "")
          (else (k-cat5 "a " what " at " (k-region-show r) ", which can be written")))))
(define k-named-untransmissible (->* (int k-descs int k-ids) string)
  (lambda (w ds t bound)
    (cond ((or (= w k-addr-index) (= w k-process-index)) "")
          ;; A procedure's parameter, at a region it binds, the caller's.
          ((and (= w k-inbox-index) (k-bound-inbox? ds bound)) "")
          ((= w k-inbox-index) "a process's own mailbox, which only it may take from")
          (else (string-append "a " (k-show-ty t))))))
;; Whether an inbox's descriptions `ds` name a region in `bound`.
(define k-bound-inbox? (->* (k-descs k-ids) bool)
  (lambda (ds bound)
    (and (= (k-length ds) 2)
         (tagcase (car (cdr ds))
           (dr (q) (tagcase q (r-var (v) (k-has-id? bound v)) (else y #f)))
           (else y #f)))))

;; Whether atom `a` is one a process may have that is seen outside it: a
;; send, a fill or an await, I/O, `spin`, `nondet`, reading globals'
;; bindings or data frozen in the heap, allocating at a region that is no
;; place (a constant, or the heap) (the Rust checker's `crossing_atom`).
(define k-crossing-atom? (->* (k-atom) bool)
  (lambda (a)
    (tagcase a
      (a-send (r) #t) (a-init (r) #t) (a-await (r) #t) (a-io (k) #t) (a-spin () #t) (a-nondet () #t)
      (a-read (r)
        (tagcase r (r-global (g) #t) (r-globals () #t) (r-frozen (p f) (< p 0)) (else y #f)))
      (a-alloc (r) (tagcase r (r-const (n) #t) (r-fresh (i n) #t) (r-heap () #t) (else y #f)))
      (else y #f))))
;; The first atom of `e` a procedure crossing into a process may not have,
;; alone in an effect; none if none: what is on a binder in `bound`, which
;; its caller gives, it may.
(define k-crossing-bad (->* (k-eff k-ids) k-eff)
  (lambda (e bound)
    (cond ((null? e) nil)
          ((let ((a (car e)))
             (tagcase a
               (a-var (v) (k-has-id? bound v))
               (else y (or (k-crossing-atom? a)
                           (tagcase (k-atom-region a)
                             (r-var (v) (and (k-has-region? a) (k-has-id? bound v)))
                             (else z #f))))))
           (k-crossing-bad (cdr e) bound))
          (else (k-one (car e))))))

;; `sendable` binder `v`, as `m` solves it, takes only what may be sent to a
;; process; or an error (the Rust checker's `check_bounds`).
(define k-check-sendable (->* (int k-map int int) unit)
  (lambda (v m a b)
    (let* ((f (k-map-find m v))
           (t (if (null? f) -1 (k-desc-type-id (cdr (car f)))))
           (why (if (< t 0) "" (k-untransmissible t nil nil))))
      (if (string=? why "")
          #u
          (k-fail (k-cat5 (k-quote-dvar v) " is bound as sendable, and a " (k-show-ty t)
                          " is not: " why)
                  a b)))))
;; `data` binder `v`, bound `bd`, as `m` solves it, takes only data, at its
;; place; or an error.
(define k-check-data (->* (int k-regions k-map int int) unit)
  (lambda (v bd m a b)
    (let* ((f (k-map-find m v))
           (t (if (null? f) -1 (k-desc-type-id (cdr (car f)))))
           (place (k-subst-region (if (null? bd) (r-heap) (car bd)) m)))
      (cond ((< t 0) #u)
            ((not (k-is-data? t))
             (k-fail (k-cat4 (k-quote-dvar v) " is bound as data, and a " (k-show-ty t)
                             " is not data")
                     a b))
            ((not (k-is-data-at? t place))
             (k-fail (k-cat5 (k-quote-dvar v) " is bound as data at " (k-region-show place)
                             ", and a " (k-cat3 (k-show-ty t) " is data in another place" ""))
                     a b))
            (else #u))))))))
