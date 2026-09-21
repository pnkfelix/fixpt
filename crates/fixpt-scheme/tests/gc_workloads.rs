//! Collector workloads, ported from Larceny's `test/GC`.
//!
//! The `gc-stress` feature answers one question — does every safepoint hand the
//! collector a complete root set — and it answers it with whatever allocation
//! the rest of the suite happens to do. That is a narrow question. It says
//! nothing about whether long-lived data survives repeated collection intact,
//! whether large objects are reclaimed, or whether a copying collector
//! preserves sharing rather than quietly duplicating shared structure.
//!
//! Larceny's `test/GC` directory exists precisely because those are different
//! questions, and `permsort.sch` states the taxonomy outright:
//!
//! ```text
//!    perm8            storage allocation
//!    Tenperm8         storage allocation and garbage collection
//!    sumperms         sequential traversal
//!    mergesort        side effects
//! ```
//!
//! …while `grow.sch` notes it is "particularly nice to test the large-object
//! space for space leaks". These are ports of those, turned from benchmarks
//! into assertions: each one checks a *result* (so a collector that corrupts
//! live data fails rather than merely running) and, where the workload is about
//! memory rather than arithmetic, a heap-occupancy property.
//!
//! Sources: `larceny/test/GC/{gcbench0,grow,permsort}.sch`.

use fixpt_engine::Backend;
use fixpt_scheme::Session;

const STEP_LIMIT: u64 = 400_000_000;

fn session(backend: Backend) -> Session {
    let mut s = Session::with_backend(backend);
    s.engine.set_step_limit(Some(STEP_LIMIT));
    s
}

/// Live words after a full collection.
///
/// Safe to collect with an empty root set here: between top-level forms the
/// engine holds nothing, which is the same property the image tests rely on.
fn live_words(s: &mut Session) -> usize {
    s.rt.heap.collect(&mut []);
    s.rt.heap.used()
}

fn eval(s: &mut Session, src: &str) -> String {
    s.eval_to_string("<gc>", src).unwrap_or_else(|e| panic!("{e}\nin: {src}"))
}

/// Under `gc-stress` every safepoint collects, so a workload of *n* allocations
/// performs *n* full collections. The shapes below are what matter, not the
/// counts, so the counts shrink.
const fn small(stressed: usize, normal: usize) -> usize {
    if cfg!(feature = "gc-stress") { stressed } else { normal }
}

// ---------------------------------------------------------------- GCBench

/// Hans Boehm's GCBench, as Larceny carries it (`test/GC/gcbench0.sch`).
///
/// The shape is the point: a big tree is built and dropped to stretch the heap,
/// then a long-lived tree and a long-lived array of flonums are created, and
/// then transient trees are churned at increasing depths. The long-lived data
/// has to survive all of that churn *intact* — which is what the assertions
/// check, rather than just timing the run.
///
/// Flonums are boxed here, so the array is also a few thousand small heap
/// objects reachable only from one vector: exactly the pattern that catches a
/// collector that forwards a slot without forwarding what it points at.
const GCBENCH: &str = r#"
(define (make-node) (make-vector 4 0))
(define (populate! depth node)
  (if (> depth 0)
      (begin
        (vector-set! node 0 (make-node))
        (vector-set! node 1 (make-node))
        (populate! (- depth 1) (vector-ref node 0))
        (populate! (- depth 1) (vector-ref node 1)))))
(define (make-tree depth)
  (if (<= depth 0)
      (make-node)
      (let ((v (make-node)))
        (vector-set! v 0 (make-tree (- depth 1)))
        (vector-set! v 1 (make-tree (- depth 1)))
        v)))
(define (tree-size depth) (- (expt 2 (+ depth 1)) 1))
(define (count-nodes t)
  (if (vector? t)
      (+ 1 (count-nodes (vector-ref t 0)) (count-nodes (vector-ref t 1)))
      0))

(define stretch-depth STRETCH)
(define long-lived-depth (- stretch-depth 2))
(define array-size (* 4 (tree-size long-lived-depth)))
(define half (quotient array-size 2))

;; Stretch the heap with a tree that is dropped immediately.
(make-tree stretch-depth)

;; The data that must survive everything below.
(define long-lived (make-node))
(populate! long-lived-depth long-lived)
(define array (make-vector array-size 0.0))
(do ((i 0 (+ i 1))) ((>= i half))
  (vector-set! array i (/ 1.0 (exact->inexact (+ i 1)))))

;; Churn: transient trees at increasing depths, both ways of building them.
(do ((d 4 (+ d 2))) ((> d long-lived-depth))
  (let ((iters (quotient (* 2 (tree-size stretch-depth)) (tree-size d))))
    (do ((i 0 (+ i 1))) ((>= i iters))
      (populate! d (make-node))
      (make-tree d))))

(list (count-nodes long-lived)
      (vector-length array)
      (= (vector-ref array 0) 1.0)
      (= (vector-ref array (- half 1)) (/ 1.0 (exact->inexact half))))
"#;

#[test]
fn gcbench_long_lived_data_survives_the_churn() {
    let stretch = small(6, 10);
    let long_lived_depth = stretch - 2;
    let nodes = (1usize << (long_lived_depth + 1)) - 1;
    let array_size = 4 * nodes;
    let expected = format!("({nodes} {array_size} #t #t)");

    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        let got = eval(&mut s, &GCBENCH.replace("STRETCH", &stretch.to_string()));
        assert_eq!(got, expected, "{backend:?} lost or corrupted long-lived data");
    }
}

// ------------------------------------------------------------------- grow

/// `test/GC/grow.sch`: build a growable vector by repeated doubling, drop it,
/// repeat. Each generation leaves behind a chain of ever-larger dead vectors.
///
/// Larceny's comment is that this "is particularly nice to test the
/// large-object space for space leaks", and a leak is exactly what is asserted
/// here: after the whole run, a full collection must bring occupancy back to
/// roughly where it started. A collector that retained even one generation of
/// these vectors would show up immediately, and no amount of
/// collect-at-every-safepoint would have noticed, because the answer would
/// still be right.
const GROW: &str = r#"
(define (make-seq) (cons 0 (make-vector 8 0)))
(define (seq-add! s x)
  (let ((next (car s)) (v (cdr s)))
    (if (= next (vector-length v))
        (let ((w (make-vector (* (vector-length v) 2) 0)))
          (do ((i 0 (+ i 1))) ((= i (vector-length v)))
            (vector-set! w i (vector-ref v i)))
          (set-cdr! s w)
          (seq-add! s x))
        (begin (vector-set! v next x)
               (set-car! s (+ next 1))))))
(define (build n)
  (let ((s (make-seq)))
    (do ((i 0 (+ i 1))) ((= i n) (car s))
      (seq-add! s i))))
(define (run reps n)
  (do ((i 0 (+ i 1))) ((= i reps) 'done)
    (build n)))
"#;

#[test]
fn large_objects_are_reclaimed() {
    let reps = small(3, 12);
    let n = small(400, 20_000);
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        eval(&mut s, GROW);
        // Baseline *after* the definitions exist, so the comparison is about
        // the workload rather than about the program that runs it.
        let before = live_words(&mut s);
        assert_eq!(eval(&mut s, &format!("(run {reps} {n})")), "done");
        let after = live_words(&mut s);

        // One live sequence of `n` ints occupies at least `n` words, and the
        // run builds `reps` of them one after another. If even a single
        // generation were retained the heap would be `n` words heavier; the
        // slack here is far below that and far above ordinary session noise.
        let slack = 4_000;
        assert!(
            after <= before + slack,
            "{backend:?} leaked: {before} words before, {after} after \
             ({reps} sequences of {n} were dropped)"
        );
    }
}

// --------------------------------------------------------------- permsort

/// `test/GC/permsort.sch`: Lars Hansen / Will Clinger / Gene Luks.
///
/// A grey code over the permutations of a list, built by repeatedly flipping a
/// prefix. Each flip conses a fresh prefix onto the *shared* tail of the
/// previous permutation, so the 40320 permutations of eight elements occupy
/// 149912 pairs rather than the 322560 an unshared representation would need.
const PERMS: &str = r#"
(define (permutations start)
  (let ((x start) (perms (list start)))
    (letrec ((revloop
              (lambda (l n y)
                (if (= n 0) y (revloop (cdr l) (- n 1) (cons (car l) y)))))
             (drop
              (lambda (l n) (if (= n 0) l (drop (cdr l) (- n 1)))))
             (flip!
              (lambda (n)
                (set! x (revloop x n (drop x n)))
                (set! perms (cons x perms))))
             (walk
              (lambda (n)
                (if (> n 1)
                    (do ((j (- n 1) (- j 1)))
                        ((= j 0) (walk (- n 1)))
                      (walk (- n 1))
                      (flip! n))))))
      (walk (length x))
      perms)))
(define (sum-list l) (if (null? l) 0 (+ (car l) (sum-list (cdr l)))))
(define (sum-lists ls) (if (null? ls) 0 (+ (sum-list (car ls)) (sum-lists (cdr ls)))))
(define (copy-list l) (if (null? l) '() (cons (car l) (copy-list (cdr l)))))
(define (copy-all ls) (if (null? ls) '() (cons (copy-list (car ls)) (copy-all (cdr ls)))))
(define (upto n) (let loop ((i n) (acc '())) (if (= i 0) acc (loop (- i 1) (cons i acc)))))
"#;

/// perm8: allocation with *no* garbage — every pair produced stays live.
///
/// The checksum is what makes it a test: each permutation of `1 … n` sums to
/// `n(n+1)/2`, so the total is that times the number of permutations. A
/// collector that dropped or duplicated a pair under this much pressure would
/// change the count or the sum.
#[test]
fn permutations_are_correct_under_heavy_allocation() {
    let n = small(6, 8);
    let count: usize = (1..=n).product();
    let checksum = count * (n * (n + 1) / 2);
    let expected = format!("({count} {checksum})");

    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        eval(&mut s, PERMS);
        eval(&mut s, &format!("(define start (upto {n}))"));
        // Measured around the construction *alone*. Each top-level form also
        // lowers its own code into the heap, so folding the checksum into the
        // same form would count that code as if it were data.
        let before = live_words(&mut s);
        eval(&mut s, "(define perms (permutations start))");
        let pairs = (live_words(&mut s) - before) / 2 + n;

        let got = eval(&mut s, "(list (length perms) (sum-lists perms))");
        assert_eq!(got, expected, "{backend:?} got the permutations wrong");

        // An external check on the *shape* of what was built, not just its
        // contents. `permsort.sch` documents perm8 as allocating 149912 pairs
        // — a number that only comes out right if the grey-code construction
        // shares tails exactly as Larceny's does, and if the collector then
        // preserves that sharing. A pair here is two words with no header, and
        // the 8 pairs of the starting list are live before the measurement
        // begins, so the figures are directly comparable.
        if n == 8 {
            let documented = 149_912;
            let drift = pairs.abs_diff(documented);
            // Losing the sharing would give 40320 x 8 = 322560 pairs, so the
            // bound only has to be tight enough to tell 150k from 320k. It is
            // far tighter than that: the residual is the handful of words the
            // form's own lowered code occupies.
            assert!(
                drift <= 64,
                "{backend:?}: perm8 built {pairs} pairs; Larceny documents                  {documented}. A difference this large means the sharing                  structure diverged."
            );
        }
    }
}

/// The subtle one: a copying collector must preserve sharing.
///
/// Nothing else in the suite would catch a forwarding-pointer bug that copied a
/// shared tail twice. Every answer would still be *correct* — `equal?` would
/// hold, the checksums would match — and the heap would silently double.
///
/// So this measures rather than inspects: the permutation list is built once
/// with its tails shared, and once with every element copied. If sharing
/// survives collection, the shared one is dramatically smaller. The comparison
/// calibrates itself, so it does not depend on how a pair is represented.
#[test]
fn the_collector_preserves_sharing() {
    let n = small(6, 7);
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        eval(&mut s, PERMS);

        let base = live_words(&mut s);
        eval(&mut s, &format!("(define perms (permutations (upto {n})))"));
        let shared = live_words(&mut s) - base;

        // The same data, with every tail unshared. Built *after* the
        // measurement above so the two do not overlap.
        eval(&mut s, "(define copies (copy-all perms))");
        let with_copies = live_words(&mut s) - base;
        let unshared = with_copies - shared;

        assert!(
            unshared > shared * 3 / 2,
            "{backend:?}: sharing was not preserved — {shared} words shared vs \
             {unshared} words unshared; they should differ substantially"
        );
    }
}

/// Tenperm8: the same allocation, repeated, with each round dropped.
///
/// `permsort.sch` separates this from perm8 deliberately — perm8 is "storage
/// allocation", this is "storage allocation and garbage collection". Occupancy
/// must return to the baseline every time round.
#[test]
fn repeated_allocation_is_fully_reclaimed() {
    let n = small(5, 7);
    let rounds = small(2, 4);
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        eval(&mut s, PERMS);
        let base = live_words(&mut s);
        let mut peak = 0;
        for _ in 0..rounds {
            eval(&mut s, &format!("(define perms (permutations (upto {n})))"));
            peak = peak.max(s.rt.heap.used());
            // Drop it and let the next round start clean.
            eval(&mut s, "(set! perms '())");
            let now = live_words(&mut s);
            assert!(
                now <= base + 2_000,
                "{backend:?} did not reclaim a round: {base} words at rest, {now} after"
            );
        }
        assert!(peak > base, "the workload should actually have allocated something");
    }
}

/// Destructive merge sort over the permutation list: "side effects" in
/// `permsort.sch`'s taxonomy.
///
/// It allocates nothing at all, and instead rewrites `cdr`s among objects that
/// have already survived several collections — creating pointers between old
/// objects, which is the write pattern a generational collector would need a
/// barrier for and which a copying collector must still traverse correctly.
#[test]
fn destructive_sorting_of_survived_data() {
    let n = small(5, 7);
    let count: usize = (1..=n).product();
    for backend in [Backend::Ast, Backend::Bytecode] {
        let mut s = session(backend);
        eval(&mut s, PERMS);
        eval(
            &mut s,
            r#"
            (define (less? a b)
              (cond ((null? a) #f)
                    ((null? b) #f)
                    ((< (car a) (car b)) #t)
                    ((> (car a) (car b)) #f)
                    (else (less? (cdr a) (cdr b)))))
            (define (merge! a b)
              (cond ((null? a) b)
                    ((null? b) a)
                    ((less? (car b) (car a))
                     (set-cdr! b (merge! a (cdr b))) b)
                    (else (set-cdr! a (merge! (cdr a) b)) a)))
            (define (halve l)
              (let loop ((slow l) (fast (cdr l)))
                (if (or (null? fast) (null? (cdr fast)))
                    (let ((rest (cdr slow))) (set-cdr! slow '()) rest)
                    (loop (cdr slow) (cddr fast)))))
            (define (sort! l)
              (if (or (null? l) (null? (cdr l)))
                  l
                  (let ((back (halve l))) (merge! (sort! l) (sort! back)))))
            (define (sorted? l)
              (cond ((null? l) #t)
                    ((null? (cdr l)) #t)
                    ((less? (cadr l) (car l)) #f)
                    (else (sorted? (cdr l)))))
            "#,
        );
        eval(&mut s, &format!("(define perms (permutations (upto {n})))"));
        // Collect between building and sorting, so the sort is rewriting
        // objects that have genuinely moved.
        s.rt.heap.collect(&mut []);
        let got = eval(&mut s, "(set! perms (sort! perms)) (list (length perms) (sorted? perms))");
        assert_eq!(got, format!("({count} #t)"), "{backend:?} sorted wrongly");
    }
}
