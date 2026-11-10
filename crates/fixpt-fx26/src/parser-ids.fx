;;; The FX-26 parser, in FX-26: each expression's identity
;;; (`parser-types.fx`): its position, its number in a walk of the
;;; program's trees that takes each expression before what is in it, the
;;; forms in order, from 0. Where it starts and ends are its provenance,
;;; kept beside. What the checkers find of an expression is kept by it, so
;;; two are never taken for one, not a desugaring's made where what it
;;; desugars is, nor a macro's argument placed twice
;;; (`docs/research/loads-and-places.md`, "Decided: identity by
;;; position"); the Rust front end numbers its trees alike (`ids.rs`).
;;; Each number is a key of the mode the walk is in (`keys`, "Decided:
;;; three keys"): `path`, the count of the session's walk, which goes on
;;; from one text to the next; `digest`, the count within the form, beside
;;; the form's reading; `full` (and `validate`), the digest of the path down
;;; from the form, beside the form's reading.
;;; Part of the parser, after `parser-exps.fx`, before `parser-top.fx`.

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
(define parser-types ((proj (load-module "fx26:parser-types.fx") rs re rm rc rp)))
(define tables (load-module "fx26:table.fx"))
(import tables make-table table-ref table-set! (type table))
(import parser-types e-var e-int e-bool e-str e-char e-float e-sym e-quote e-unit e-lambda e-app
        e-plambda e-proj e-if e-letrec e-let e-begin e-prompt e-letregion e-rlambda e-the
        e-convention e-bloblet e-product e-extract e-sum e-tagcase e-module e-with t-define
        t-define-rec t-exp
        (type exp top exp-list let-list letrec-list arm-list mod-items top-list keys given))
(define readings ((proj (load-module "fx26:readings.fx") rs re rm rc)))
(import readings fold1 read-again-reading)

;; Where the walk is down a form (`full`): each expression around the one
;; walked, the innermost first, by the digest of its path and how many of
;; what is in it have been walked; the form itself last.
(define-type frames (listof (productof (1 int) (2 int)) acyclic))
;; The walk of a session's text: how many expressions of the form have been
;; walked; the form's reading, what every expression it numbers is of, in a
;; field of its own beside its number (0 in `path`); the mode; how many the
;; session walked before the form; the frames; the keys given (`given`),
;; the last first; and the session's state after the forms walked.
(define-type seen
  (productof (1 (ref int rs)) (2 (ref int rs)) (3 int) (4 (ref int rs)) (5 (ref frames rs))
             (6 (ref given rs)) (7 (ref int rs))))

(define-effect counts (maxeff (read @globals) spin (read rs) (write rs) (alloc rs)))

;; `validate` (`docs/research/loads-and-places.md`, "Decided: three keys"):
;; each cheap key given, `path`'s and `digest`'s, with the full key given
;; the same expression, as long as the parser lasts (its front end's): a
;; cheap key given again with another full key would take two expressions
;; for one in its mode. By a digest of the cheap key, each with the
;; cheap key and the full one.
(define-type keys-seen (listof (productof (1 int) (2 int) (3 int) (4 int)) acyclic))
(define int-hash (subr pure (int) int) (lambda (a) a))
(define int=? (subr pure (int int) bool) (lambda (a b) (= a b)))
(define path-seen (ref (table int keys-seen rs) rs) (new (make-table int-hash int=?)))
(define digest-seen (ref (table int keys-seen rs) rs) (new (make-table int-hash int=?)))
;; What the parse found wrong, the first, and where; "" if nothing.
(define validate-why (ref string rs) (new ""))
(define validate-at (ref (productof (1 int) (2 int)) rs) (new (product (1 0) (2 0))))
;; `c` `cr`, the `mode` key given the expression at `a`..`b`, whose full
;; key is `z` `r`, recorded in `seen`; or, given before with another full
;; key, said (`validate-why`).
(define validated! (->* ((ref (table int keys-seen rs) rs) string int int int int int int) unit)
  (lambda (seen mode c cr z r a b)
    (letrec ((find (subr (maxeff (read @globals) spin) (keys-seen) keys-seen)
               (lambda (ks)
                 (cond ((null? ks) nil)
                       ((and (= (extract (car ks) 1) c) (= (extract (car ks) 2) cr)) ks)
                       (else (find (cdr ks)))))))
      (let* ((h (fold1 c cr)) (bucket (table-ref (get seen) h nil)) (found (find bucket)))
        (cond ((null? found)
               (table-set! (get seen) h
                           (the keys-seen (cons (product (1 c) (2 cr) (3 z) (4 r)) bucket))))
              ((and (= (extract (car found) 3) z) (= (extract (car found) 4) r)) #u)
              ((not (string=? (get validate-why) "")) #u)
              (else
               (let ((key (lambda ((x int) (y int))
                            (string-append "(" (int->string x) " " (int->string y) ")"))))
                 (begin
                   (set validate-why
                        (string-append "validate: the `" mode "` key " (key c cr)
                                       " was given another expression before: its full key "
                                       (key (extract (car found) 3) (extract (car found) 4))
                                       ", this one's " (key z r)))
                   (set validate-at (product (1 a) (2 b)))))))))))

;; The next expression's number, the one walked next (at `a`..`b`, which
;; does not matter: its provenance), as the mode keys it.
(define next-kth (->* (seen int int) int)
  (lambda (t a b)
    (let ((n (get (extract t 1))) (mode (extract t 3)))
      (begin
        (set (extract t 1) (+ n 1))
        (if (= mode 0)
            (+ (get (extract t 4)) n)
            (let* ((r (get (extract t 2))) (k (if (= mode 1) n (next-in-path t))))
              (begin (set (extract t 6) (cons (product (1 k) (2 r)) (get (extract t 6))))
                     (if (= mode 3)
                         (begin (validated! path-seen "path" (+ (get (extract t 4)) n) 0 k r a b)
                                (validated! digest-seen "digest" n r k r a b))
                         #u)
                     k)))))))
;; The path's digest of the expression walked next: its parent's, and its
;; place among the parent's, from 0; its frame, the innermost now.
(define next-in-path (->* (seen) int)
  (lambda (t)
    (let* ((fs (get (extract t 5))) (up (car fs)) (z (fold1 (extract up 1) (extract up 2))))
      (begin
        (set (extract t 5)
             (cons (product (1 z) (2 0))
                   (cons (product (1 (extract up 1)) (2 (+ (extract up 2) 1))) (cdr fs))))
        z))))
;; The walk out of the expression walked last: its frame gone.
(define walked-out! (->* (seen) unit)
  (lambda (t) (if (>= (extract t 3) 2) (set (extract t 5) (cdr (get (extract t 5)))) #u)))

;; Each `number-` gives what it was given, not a copy, where nothing in it
;; changed: as the parser numbers every expression 0, the first.
(define-rec
  ;; `x` and what is in it, numbered.
  (number-exp (->* (seen exp) exp)
    (lambda (t x) (let ((y (number-exp-in t x))) (begin (walked-out! t) y))))
  (number-exp-in (->* (seen exp) exp)
    (lambda (t x)
      (let ((reading (get (extract t 2))))
      (tagcase x
        (e-var (s a b k kr)
               (let ((n (next-kth t a b)))
                    (if (and (= n k) (= reading kr)) x (e-var s a b n reading))))
        (e-int (v a b k kr)
               (let ((n (next-kth t a b)))
                    (if (and (= n k) (= reading kr)) x (e-int v a b n reading))))
        (e-bool (v a b k kr)
                (let ((n (next-kth t a b)))
                     (if (and (= n k) (= reading kr)) x (e-bool v a b n reading))))
        (e-str (v a b k kr)
               (let ((n (next-kth t a b)))
                    (if (and (= n k) (= reading kr)) x (e-str v a b n reading))))
        (e-char (v a b k kr)
                (let ((n (next-kth t a b)))
                     (if (and (= n k) (= reading kr)) x (e-char v a b n reading))))
        (e-float (v a b k kr)
                 (let ((n (next-kth t a b)))
                      (if (and (= n k) (= reading kr)) x (e-float v a b n reading))))
        (e-sym (v a b k kr)
               (let ((n (next-kth t a b)))
                    (if (and (= n k) (= reading kr)) x (e-sym v a b n reading))))
        (e-quote (v a b k kr)
                 (let ((n (next-kth t a b)))
                      (if (and (= n k) (= reading kr)) x (e-quote v a b n reading))))
        (e-unit (a b k kr)
                (let ((n (next-kth t a b)))
                     (if (and (= n k) (= reading kr)) x (e-unit a b n reading))))
        (e-lambda (ps body a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x (e-lambda ps body2 a b n reading))))
        (e-app (f xs a b k kr)
          (let* ((n (next-kth t a b)) (f2 (number-exp t f)) (xs2 (number-exps t xs)))
            (if (and (= n k) (= reading kr) (eq? f f2) (eq? xs xs2)) x
                (e-app f2 xs2 a b n reading))))
        (e-plambda (d body a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x (e-plambda d body2 a b n reading))))
        (e-proj (body ds a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x (e-proj body2 ds a b n reading))))
        (e-if (p c d a b k kr)
          (let* ((n (next-kth t a b)) (p2 (number-exp t p)) (c2 (number-exp t c))
                 (d2 (number-exp t d)))
            (if (and (= n k) (= reading kr) (eq? p p2) (eq? c c2) (eq? d d2)) x
                (e-if p2 c2 d2 a b n reading))))
        (e-letrec (bs body a b k kr)
          (let* ((n (next-kth t a b)) (bs2 (number-recs t bs)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? bs bs2) (eq? body body2)) x
                (e-letrec bs2 body2 a b n reading))))
        (e-let (bs body a b k kr)
          (let* ((n (next-kth t a b)) (bs2 (number-lets t bs)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? bs bs2) (eq? body body2)) x
                (e-let bs2 body2 a b n reading))))
        (e-begin (xs a b k kr)
          (let* ((n (next-kth t a b)) (xs2 (number-exps t xs)))
            (if (and (= n k) (= reading kr) (eq? xs xs2)) x (e-begin xs2 a b n reading))))
        (e-prompt (g body h a b k kr)
          (let* ((n (next-kth t a b)) (g2 (number-exp t g)) (body2 (number-exp t body))
                 (h2 (number-exp t h)))
            (if (and (= n k) (= reading kr) (eq? g g2) (eq? body body2) (eq? h h2))
                x
                (e-prompt g2 body2 h2 a b n reading))))
        (e-letregion (f r i body a b k kr)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x
                (e-letregion f r i body2 a b n reading))))
        (e-rlambda (r l a b k kr)
          (let* ((n (next-kth t a b)) (r2 (number-exp t r)) (l2 (number-exp t l)))
            (if (and (= n k) (= reading kr) (eq? r r2) (eq? l l2)) x
                (e-rlambda r2 l2 a b n reading))))
        (e-the (d e a b k kr)
          (let* ((n (next-kth t a b)) (e2 (number-exp t e)))
            (if (and (= n k) (= reading kr) (eq? e e2)) x (e-the d e2 a b n reading))))
        (e-convention (c e a b k kr)
          (let* ((n (next-kth t a b)) (e2 (number-exp t e)))
            (if (and (= n k) (= reading kr) (eq? e e2)) x (e-convention c e2 a b n reading))))
        (e-bloblet (o i xs g a b k kr)
          (let* ((n (next-kth t a b)) (xs2 (number-exps t xs)))
            (if (and (= n k) (= reading kr) (eq? xs xs2)) x (e-bloblet o i xs2 g a b n reading))))
        (e-product (fs a b k kr)
          (let* ((n (next-kth t a b)) (fs2 (number-lets t fs)))
            (if (and (= n k) (= reading kr) (eq? fs fs2)) x (e-product fs2 a b n reading))))
        (e-extract (e l g a b k kr)
          (let* ((n (next-kth t a b)) (e2 (number-exp t e)))
            (if (and (= n k) (= reading kr) (eq? e e2)) x (e-extract e2 l g a b n reading))))
        (e-sum (l e a b k kr)
          (let* ((n (next-kth t a b)) (e2 (number-exp t e)))
            (if (and (= n k) (= reading kr) (eq? e e2)) x (e-sum l e2 a b n reading))))
        (e-tagcase (s arms els g a b k kr)
          (let* ((n (next-kth t a b)) (s2 (number-exp t s)) (arms2 (number-arms t arms))
                 (els2 (number-lets t els)))
            (if (and (= n k) (= reading kr) (eq? s s2) (eq? arms arms2) (eq? els els2))
                x
                (e-tagcase s2 arms2 els2 g a b n reading))))
        (e-module (items a b k kr)
          (let* ((n (next-kth t a b)) (items2 (number-items t items)))
            (if (and (= n k) (= reading kr) (eq? items items2)) x (e-module items2 a b n reading))))
        (e-with (m body a b k kr wrl)
          (let* ((n (next-kth t a b)) (body2 (number-exp t body)))
            (if (and (= n k) (= reading kr) (eq? body body2)) x
                (e-with m body2 a b n reading wrl))))))))
  (number-exps (->* (seen exp-list) exp-list)
    (lambda (t xs)
      (if (null? xs)
          xs
          (let* ((x (number-exp t (car xs))) (rest (number-exps t (cdr xs))))
            (if (and (eq? x (car xs)) (eq? rest (cdr xs))) xs (cons x rest))))))
  ;; A `let`'s bindings, a product's fields, a `tagcase`'s `else`.
  (number-lets (->* (seen let-list) let-list)
    (lambda (t bs)
      (if (null? bs)
          bs
          (let* ((x (number-exp t (extract (car bs) 2))) (rest (number-lets t (cdr bs))))
            (if (and (eq? x (extract (car bs) 2)) (eq? rest (cdr bs)))
                bs
                (cons (product (1 (extract (car bs) 1)) (2 x)) rest))))))
  (number-recs (->* (seen letrec-list) letrec-list)
    (lambda (t bs)
      (if (null? bs)
          bs
          (let* ((x (number-exp t (extract (car bs) 3))) (rest (number-recs t (cdr bs))))
            (if (and (eq? x (extract (car bs) 3)) (eq? rest (cdr bs)))
                bs
                (cons (product (1 (extract (car bs) 1)) (2 (extract (car bs) 2)) (3 x)) rest))))))
  (number-arms (->* (seen arm-list) arm-list)
    (lambda (t arms)
      (if (null? arms)
          arms
          (let* ((arm (car arms)) (x (number-exp t (extract arm 4)))
                 (rest (number-arms t (cdr arms))))
            (if (and (eq? x (extract arm 4)) (eq? rest (cdr arms)))
                arms
                (cons (product (1 (extract arm 1)) (2 (extract arm 2)) (3 (extract arm 3)) (4 x))
                      rest))))))
  (number-items (->* (seen mod-items) mod-items)
    (lambda (t items)
      (if (null? items)
          items
          (let* ((it (car items)) (xs (number-exps t (extract it 4)))
                 (rest (number-items t (cdr items))))
            (if (and (eq? xs (extract it 4)) (eq? rest (cdr items)))
                items
                (cons (product (1 (extract it 1)) (2 (extract it 2)) (3 (extract it 3)) (4 xs))
                      rest)))))))

;; Form `x`, its expressions numbered.
(define number-top (->* (seen top) top)
  (lambda (t x)
    (tagcase x
      (t-define (n ty e a b) (let ((e2 (number-exp t e))) (if (eq? e e2) x (t-define n ty e2 a b))))
      (t-define-rec (bs a b)
        (let ((bs2 (number-recs t bs))) (if (eq? bs bs2) x (t-define-rec bs2 a b))))
      (t-exp (e) (let ((e2 (number-exp t e))) (if (eq? e e2) x (t-exp e2))))
      (else y x))))
(define number-each (->* (seen top-list) top-list)
  (lambda (t ts)
    (if (null? ts) nil (let* ((x (number-top t (car ts)))) (cons x (number-each t (cdr ts)))))))
;; How many expressions this parser has walked, in every text it read, kept
;; or not: `path`'s numbers go on from it, so that none is given twice
;; while the parser lasts, the key space its front end's tables are of
;; (the compiler's, `validate`'s).
(define walked-total (ref int rs) (new 0))
;; The keys the last text was read with, and the session's state after it:
;; what a form checked again while that text is checked is read again in
;; (`read-again`).
(define last-keys (ref keys rs) (new (product (1 0) (2 0) (3 ""))))
(define last-state (ref int rs) (new 0))
;; The walk of a text read with `keys`, before its first form, after all the
;; parser walked before.
(define walk-of (->* (keys) seen)
  (lambda (keys)
    (begin
     (set validate-why "")
     (set last-keys keys)
     (product (1 (the (ref int rs) (new 0))) (2 (the (ref int rs) (new 0))) (3 (extract keys 1))
             (4 (the (ref int rs) (new (get walked-total)))) (5 (the (ref frames rs) (new nil)))
             (6 (the (ref given rs) (new nil))) (7 (the (ref int rs) (new (extract keys 2))))))))
;; What `validate` found wrong in the walk, if anything (`validated!`): its
;; message, "" if nothing, and where.
(define walk-wrong (->* () (productof (1 string) (2 int) (3 int)))
  (lambda ()
    (product (1 (get validate-why)) (2 (extract (get validate-at) 1))
             (3 (extract (get validate-at) 2)))))
;; A form's trees `ts` (what it makes, and the hidden globals of the files
;; it loads first), each expression numbered, of the form's reading `r`
;; (`readings.fx`'s `form-reading`), the state after it.
(define number-form (->* (seen int top-list) top-list)
  (lambda (t r ts)
    (let ((mode (extract t 3)))
      (begin
        (set (extract t 1) 0)
        (set (extract t 2) (if (= mode 0) 0 r))
        (if (>= mode 2) (set (extract t 5) (cons (product (1 r) (2 0)) nil)) #u)
        (let ((out (number-each t ts)))
          (begin (set (extract t 4) (+ (get (extract t 4)) (get (extract t 1))))
                 (set (extract t 7) r)
                 out))))))
;; The session's state after the forms walked, and how many the parser has
;; walked, these too.
(define walk-state (->* (seen) int) (lambda (t) (get (extract t 7))))
(define walk-count (->* (seen) int) (lambda (t) (get (extract t 4))))
;; The walk done, whether its text parsed or not: the parser's count past it,
;; and the state after it.
(define walk-done! (->* (seen) unit)
  (lambda (t) (begin (set walked-total (get (extract t 4))) (set last-state (get (extract t 7))))))
;; Form `x`, read before at reading `r`, read again: a definition the
;; checker checks again, after a name it uses was redefined (`k-rerun`),
;; in the state the text being checked left (`last-state`), as the mode
;; that text was read in keys it: its keys new, so that what this check
;; finds is never taken for what the first found, nor the reverse.
(define read-again (->* (int top) top)
  (lambda (r x)
    (let* ((keys (get last-keys))
           (t (walk-of (product (1 (extract keys 1)) (2 (get last-state)) (3 (extract keys 3)))))
           (out (number-form t (read-again-reading (get last-state) r)
                             (the top-list (cons x nil)))))
      (begin (set walked-total (get (extract t 4))) (car out)))))
;; The keys the walk gave, in its order (none in `path`).
(define walk-given (->* (seen) given)
  (lambda (t)
    (letrec ((onto (subr (maxeff (read @globals) spin (alloc rs)) (given given) given)
               (lambda (xs ys) (if (null? xs) ys (onto (cdr xs) (cons (car xs) ys))))))
      (onto (get (extract t 6)) nil))))
