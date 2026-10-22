;;; The webs of `native-reps.fx`'s `nr-webs` (`webs` in
;;; `fixpt-native/src/direct/reps.rs`), a slot at a time over the
;;; procedure's basic blocks: register code may use a frame slot for one
;;; variable, then another, so a slot is taken apart into webs, its writes
;;; and reads joined where a write reaches a read (`TODO.md` §114).
;;;
;;; A module file of no state (`TODO.md` §68), which `native-reps.fx` loads.

(hide (define direct-types (load-module "fx26:native-direct-x64-types.fx")))
(import direct-types (type da-bytes da-ints da-bools) (effect da-assembles da-reads))

;; `webs`'s basic blocks (`nr-blocks`), and what it notes of them a slot at
;; a time (`nr-slot-webs`).
(define-type nr-blocks (productof (1 da-ints) (2 (arrayof da-bytes @k)) (3 da-ints)))
(define-type nr-marks
  (productof (1 da-ints) (2 da-bools) (3 da-ints) (4 da-ints) (5 da-ints) (6 da-ints) (7 da-ints)))

;; The union-find's representative of `x`, the way there shortened.
(define nr-find (subr da-assembles (da-ints int) int)
  (lambda (parent x)
    (letrec ((root (subr da-reads (int) int)
               (lambda (r) (if (= (array-ref parent r) r) r (root (array-ref parent r)))))
             (shorten (subr da-assembles (int int) unit)
               (lambda (y r)
                 (if (= (array-ref parent y) r)
                     #u
                     (let ((next (array-ref parent y)))
                       (begin (array-set! parent y r) (shorten next r)))))))
      (let ((r (root x))) (begin (shorten x r) r)))))

;; The procedure's basic blocks (`webs`'s): chains of instructions, each
;; but the first its one predecessor's one successor (and a loop of those,
;; unreachable, cut). By instruction, its block; by block, its last
;; instruction, and the blocks before it. And into `by`, by slot (`sl`),
;; the instructions that touch it, block by block, each block's in order.
(define nr-blocks
  (subr da-assembles ((arrayof da-bytes @k) da-ints (arrayof da-bytes @k)) nr-blocks)
  (lambda (succ sl by)
    (let* ((ns (array-length succ))
           (block (the da-ints (make-array ns -1)))
           (firsts (the da-ints (make-array ns 0)))
           (lasts (the da-ints (make-array ns 0)))
           (preds (the da-ints (make-array ns 0)))
           (only (the da-ints (make-array ns 0))))
      (letrec ((one? (subr da-reads (da-bytes) bool)
                 (lambda (ts) (and (not (null? ts)) (null? (cdr ts)))))
               (count (subr da-assembles (int) unit)
                 (lambda (si)
                   (if (= si ns)
                       #u
                       (begin (count-in si (array-ref succ si)) (count (+ si 1))))))
               (count-in (subr da-assembles (int da-bytes) unit)
                 (lambda (si ts)
                   (if (null? ts)
                       #u
                       (begin (array-set! preds (car ts) (+ (array-ref preds (car ts)) 1))
                              (array-set! only (car ts) si)
                              (count-in si (cdr ts))))))
               (lead? (subr da-reads (int) bool)
                 (lambda (t)
                   (or (= t 0) (not (= (array-ref preds t) 1))
                       (not (one? (array-ref succ (array-ref only t)))))))
               (chain (subr da-assembles (int int) int)
                 (lambda (t b)
                   (let ((ts (array-ref succ t)))
                     (begin
                       (array-set! block t b)
                       (if (and (one? ts) (not (lead? (car ts))) (< (array-ref block (car ts)) 0))
                           (chain (car ts) b)
                           t)))))
               (scan (subr da-assembles (int bool int) int)
                 (lambda (l cut b)
                   (cond ((= l ns) b)
                         ((or (>= (array-ref block l) 0) (not (or cut (lead? l))))
                          (scan (+ l 1) cut b))
                         (else (begin (array-set! firsts b l)
                                      (array-set! lasts b (chain l b))
                                      (scan (+ l 1) cut (+ b 1)))))))
               (walk (subr da-assembles (int int) unit)
                 (lambda (t last)
                   (begin
                     (if (>= (array-ref sl t) 0)
                         (array-set! by (array-ref sl t) (cons t (array-ref by (array-ref sl t))))
                         #u)
                     (if (= t last) #u (walk (car (array-ref succ t)) last)))))
               (blocks (subr da-assembles (int int (arrayof da-bytes @k)) unit)
                 (lambda (b nb bpreds)
                   (if (= b nb)
                       #u
                       (begin (walk (array-ref firsts b) (array-ref lasts b))
                              (link b (array-ref succ (array-ref lasts b)) bpreds)
                              (blocks (+ b 1) nb bpreds)))))
               (link (subr da-assembles (int da-bytes (arrayof da-bytes @k)) unit)
                 (lambda (b ts bpreds)
                   (if (null? ts)
                       #u
                       (let ((c (array-ref block (car ts))))
                         (begin (array-set! bpreds c (cons b (array-ref bpreds c)))
                                (link b (cdr ts) bpreds))))))
               (turn (subr da-assembles (int) unit)
                 (lambda (s)
                   (if (= s (array-length by))
                       #u
                       (begin (array-set! by s (reverse (array-ref by s))) (turn (+ s 1)))))))
        (begin
          (count 0)
          (let* ((nb (scan 0 #t (scan 0 #f 0)))
                 (bpreds (the (arrayof da-bytes @k) (make-array nb nil))))
            (begin (blocks 0 nb bpreds) (turn 0) (product (1 block) (2 bpreds) (3 lasts)))))))))

;; The webs of frame slot `s`, which instructions `touches` read or write,
;; block by block (`webs`'s loop over slots), not a search back from each
;; read (`TODO.md` §114): where the slot is live (a read of it comes before
;; any write) and some write of it has been, every write that reaches there
;; reaches a read, so one web holds them. Each slot's work its own reads
;; and writes, and the blocks (`bl`) where it is live: a frame may have
;; hundreds of slots, and a module's body thousands of instructions and no
;; branch. Each access's `parent` the access standing for its web. `sl` and
;; `rd`: by instruction, its slot (-1 for none), and whether a read.
;; `marks`, by block: for which slot it was last touched (and then whether
;; its first access reads, its last write), live and reached; then the
;; union-find, a node for each instruction and one for each block's start
;; (`ns` + its number): for which slot each was set, its parent.
(define nr-slot-webs
  (subr da-assembles
        (da-ints da-bools (arrayof da-bytes @k) nr-blocks nr-marks da-ints da-bytes int) unit)
  (lambda (sl rd succ bl marks parent touches s)
    (let ((ns (array-length sl)) (block (extract bl 1)) (bpreds (extract bl 2))
          (lasts (extract bl 3)) (touched (extract marks 1)) (first-reads (extract marks 2))
          (last-write (extract marks 3)) (live (extract marks 4)) (reached (extract marks 5))
          (own-of (extract marks 6)) (own (extract marks 7)))
      (letrec ((writes? (subr da-reads (int) bool)
                 (lambda (p) (and (= (array-ref sl p) s) (not (array-ref rd p)))))
               (note (subr da-assembles (da-bytes da-bytes) da-bytes)
                 (lambda (ts bs)
                   (if (null? ts)
                       bs
                       (let* ((si (car ts)) (b (array-ref block si))
                              (new (not (= (array-ref touched b) s))))
                         (begin
                           (if new
                               (begin (array-set! touched b s)
                                      (array-set! first-reads b (not (writes? si)))
                                      (array-set! last-write b -1))
                               #u)
                           (if (writes? si) (array-set! last-write b si) #u)
                           (note (cdr ts) (if new (cons b bs) bs)))))))
               (seeds (subr da-assembles (da-bytes da-bytes) da-bytes)
                 (lambda (bs acc)
                   (cond ((null? bs) acc)
                         ((array-ref first-reads (car bs))
                          (begin (array-set! live (car bs) s) (seeds (cdr bs) (cons (car bs) acc))))
                         (else (seeds (cdr bs) acc)))))
               (writers (subr da-assembles (da-bytes da-bytes) da-bytes)
                 (lambda (bs acc)
                   (cond ((null? bs) acc)
                         ((>= (array-ref last-write (car bs)) 0)
                          (writers (cdr bs) (cons (car bs) acc)))
                         (else (writers (cdr bs) acc)))))
               ;; Live where a block reads the slot first, and back from
               ;; there through blocks that do not touch it.
               (back (subr da-assembles (da-bytes da-bytes da-bytes) da-bytes)
                 (lambda (ps work region)
                   (cond ((not (null? ps))
                          (let ((p (car ps)))
                            (if (or (= (array-ref live p) s) (= (array-ref touched p) s))
                                (back (cdr ps) work region)
                                (begin (array-set! live p s)
                                       (back (cdr ps) (cons p work) (cons p region))))))
                         ((null? work) region)
                         (else (back (array-ref bpreds (car work)) (cdr work) region)))))
               ;; Reached, where live: on from each block that writes it.
               (forth (subr da-assembles (da-bytes da-bytes) unit)
                 (lambda (ts work)
                   (cond ((not (null? ts))
                          (let ((c (array-ref block (car ts))))
                            (if (and (= (array-ref live c) s) (not (= (array-ref reached c) s)))
                                (begin (array-set! reached c s) (forth (cdr ts) (cons c work)))
                                (forth (cdr ts) work))))
                         ((null? work) #u)
                         (else (forth (array-ref succ (array-ref lasts (car work))) (cdr work))))))
               (fresh (subr da-assembles (int) unit)
                 (lambda (x)
                   (if (= (array-ref own-of x) s)
                       #u
                       (begin (array-set! own-of x s) (array-set! own x x)))))
               ;; A web's root an access where it has one.
               (union (subr da-assembles (int int) unit)
                 (lambda (x y)
                   (begin
                     (fresh x)
                     (fresh y)
                     (let ((a (nr-find own x)) (b (nr-find own y)))
                       (if (< a ns) (array-set! own b a) (array-set! own a b))))))
               ;; In a block, a read joined to the write before it, or to
               ;; the block's start.
               (inner (subr da-assembles (da-bytes int int) unit)
                 (lambda (ts b at)
                   (if (null? ts)
                       #u
                       (let* ((si (car ts)) (c (array-ref block si))
                              (at (cond ((= c b) at)
                                        ((= (array-ref reached c) s) (+ ns c))
                                        (else -1))))
                         (cond ((writes? si) (inner (cdr ts) c si))
                               ((>= at 0) (begin (union si at) (inner (cdr ts) c at)))
                               (else (inner (cdr ts) c at)))))))
               ;; Each block's start, where live and reached, to the end of
               ;; each block before it: its last write, or its start.
               (edges (subr da-assembles (da-bytes int da-bytes) unit)
                 (lambda (ps c region)
                   (cond ((not (null? ps))
                          (let ((p (car ps)))
                            (begin
                              (cond ((and (= (array-ref touched p) s)
                                          (>= (array-ref last-write p) 0))
                                     (union (+ ns c) (array-ref last-write p)))
                                    ((= (array-ref reached p) s) (union (+ ns c) (+ ns p)))
                                    (else #u))
                              (edges (cdr ps) c region))))
                         ((null? region) #u)
                         ((= (array-ref reached (car region)) s)
                          (edges (array-ref bpreds (car region)) (car region) (cdr region)))
                         (else (edges nil 0 (cdr region))))))
               (name (subr da-assembles (da-bytes) unit)
                 (lambda (ts)
                   (if (null? ts)
                       #u
                       (begin (fresh (car ts))
                              (array-set! parent (car ts) (nr-find own (car ts)))
                              (name (cdr ts)))))))
        (let* ((bs (note touches nil)) (rs (seeds bs nil)) (region (back nil rs rs)))
          (begin (forth nil (writers bs nil)) (inner touches -1 -1) (edges nil 0 region)
                 (name touches)))))))
