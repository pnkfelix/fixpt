;;; ZEBRA -- solve the "zebra" puzzle (who owns the zebra?) by a search
;;; that explores only 3342 possibilities, counting them.
;;;
;;; Copyright Stephen Weeks (sweeks@sweeks.com).  1999-6-21.
;;; From MLton's benchmark suite (benchmark/tests/zebra.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. MLton's driver was not fetched; the
;;; iteration count, 100 searches, is this port's. MLton's `doit n` runs
;;; n*1000+1 searches.
;;; Answer: 3342, the number of consistency checks one search makes (the
;;; original raises Fail unless it is 3342).
;;;
;;; What changed:
;;; - The five enumeration datatypes (cigarette, color, drink, nationality,
;;;   pet) are symbols: their constructors are only ever compared for
;;;   equality (the `toString`s serve `display`, which the original never
;;;   calls). So one `attribute` type serves all five, where SML's is
;;;   polymorphic, and `find` compares with `symbol=?`.
;;; - `tryEach` is used at two element types, symbols and positions: it is
;;;   written twice, as is `@`.
;;; - The exceptions Done, Inconsistent and Continue are one datatype
;;;   aborted to a prompt (`raise`); each `handle` is a prompt whose handler
;;;   re-raises what it does not handle.
;;; - `same`, `adjacent` and `left` are made once, at the top level, where
;;;   SML makes them in each `search`: captured there, with the five finders
;;;   and `num`, they made `isConsistent` a closure over nine variables, which
;;;   the register compiler declines (more than `register-regs`, 8), so
;;;   `search` ran as cellular code, and an abort from native code found no
;;;   prompt (reported, with a reproduction).
;;; - `search` returns the count of consistency checks rather than checking
;;;   it against 3342.

;; The puzzle:
;;
;; There are five houses. Each house has its own unique color. All house
;; owners are of different nationalities. They all have different pets.
;; They all drink different drinks. They all smoke different cigarettes.
;; The Englishman lives in the red house. The Swede has a dog. The Dane
;; drinks tea. The green house is adjacent to the white house on the left.
;; In the green house they drink coffee. The man who smokes Pall Malls has
;; birds. In the yellow house they smoke Dunhills. In the middle house they
;; drink milk. The Norwegian lives in the first house. The man who smokes
;; Blends lives in a house next to the house with cats. In a house next to
;; the house where they have a horse, they smoke Dunhills. The man who
;; smokes Blue Masters drinks beer. The German smokes Princes. The
;; Norwegian lives next to the blue house. They drink water in a house next
;; to the house where they smoke Blends. Who owns the zebra?

(define-type syms (listof symbol @heap))
(define-type ints (listof int @heap))
(define-type known-pair (productof (pos int) (x symbol)))
(define-type knowns (listof known-pair @heap))
(define-type attribute (productof (poss ints) (unknown syms) (known knowns)))
(define-type attr-ref (ref attribute @heap))

(define-datatype pos-option (none) (some int))
(define-datatype known-option (no-known) (some-known known-pair))

;; Everything searching does, and its exceptions, which abort to @z.
(define-effect searching (maxeff (read @heap) (write @heap) (alloc @heap) spin (read @globals)))
(define-effect zeff (maxeff searching (goto @z)))

(define-datatype zexn (done) (inconsistent) (continue (subr zeff () unit)))
(define zebra-tag (prompt-tag unit zexn searching @z) (make-continuation-prompt-tag))
(define* raise (subr (goto @z) (zexn) void)
  (lambda (e) (abort-current-continuation zebra-tag e)))

(define* peek (subr (maxeff (read @heap) spin) (knowns (subr pure (known-pair) bool)) known-option)
  (lambda (l p)
    (if (null? l)
        (no-known)
        (if (p (car l)) (some-known (car l)) (peek (cdr l) p)))))

(define* append-syms (subr (maxeff (read @heap) (alloc @heap) spin) (syms syms) syms)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append-syms (cdr xs) ys)))))
(define* append-ints (subr (maxeff (read @heap) (alloc @heap) spin) (ints ints) ints)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append-ints (cdr xs) ys)))))

(define poss ints (list 1 2 3 4 5))
(define first pos-option (some 1))
(define middle pos-option (some 3))

(define fluid-let (subr zeff (attr-ref attribute (subr zeff () unit)) unit)
  (lambda (r x f)
    (let ((old (get r)))
      (begin
        (set r x)
        (prompt zebra-tag
          (let ((v (f))) (begin (set r old) v))
          (lambda (e)
            (tagcase e
              (done () (raise e))
              (else e (begin (set r old) (raise e))))))))))

(define* init (subr (maxeff (alloc @heap) (read @globals)) (syms) attr-ref)
  (lambda (unknown) (new (product (poss poss) (unknown unknown) (known (the knowns nil))))))

(define* find (subr (maxeff (read @heap) spin (read @globals)) (attr-ref symbol) pos-option)
  (lambda (r x)
    (tagcase (peek (extract (get r) known) (lambda ((py known-pair)) (symbol=? x (extract py x))))
      (no-known () (none))
      (some-known (py) (some (extract py pos))))))

(define make (subr pure ((subr pure (int int) bool)) (subr pure (pos-option pos-option) bool))
  (lambda (f)
    (lambda ((a pos-option) (b pos-option))
      (tagcase a
        (some (x) (tagcase b (some (y) (f x y)) (else b #t)))
        (else a #t)))))

(define same (subr pure (pos-option pos-option) bool) (make (lambda ((x int) (y int)) (= x y))))
(define adjacent (subr pure (pos-option pos-option) bool) (make (lambda ((x int) (y int)) (or (= x (- y 1)) (= y (- x 1))))))
(define left (subr pure (pos-option pos-option) bool) (make (lambda ((x int) (y int)) (= x (- y 1)))))

(define-type each-done (productof (each (subr zeff (attribute) unit)) (finish (subr zeff () unit))))
(define-datatype attrs (none-attr) (one-attr attribute) (many-attr))

(define* search (subr zeff () int)
  (lambda ()
    (let* ((cigarettes (init (list 'Blend 'BlueMaster 'Dunhill 'PallMall 'Prince)))
           (colors (init (list 'Blue 'Green 'Red 'White 'Yellow)))
           (drinks (init (list 'Beer 'Coffee 'Milk 'Tea 'Water)))
           (nationalities (init (list 'Dane 'English 'German 'Norwegian 'Swede)))
           (pets (init (list 'Bird 'Cat 'Dog 'Horse 'Zebra)))
           (num (the (ref int @heap) (new 0))))
      (letrec ((smoke (subr zeff (symbol) pos-option) (lambda (x) (find cigarettes x)))
               (color (subr zeff (symbol) pos-option) (lambda (x) (find colors x)))
               (drink (subr zeff (symbol) pos-option) (lambda (x) (find drinks x)))
               (nat (subr zeff (symbol) pos-option) (lambda (x) (find nationalities x)))
               (pet (subr zeff (symbol) pos-option) (lambda (x) (find pets x)))
               (is-consistent (subr zeff () bool)
                 (lambda ()
                   (begin
                     (set num (+ (get num) 1))
                     (and (same (nat 'English) (color 'Red))
                          (same (nat 'Swede) (pet 'Dog))
                          (same (nat 'Dane) (drink 'Tea))
                          (left (color 'Green) (color 'White))
                          (same (color 'Green) (drink 'Coffee))
                          (same (smoke 'PallMall) (pet 'Bird))
                          (same (color 'Yellow) (smoke 'Dunhill))
                          (same middle (drink 'Milk))
                          (same (nat 'Norwegian) first)
                          (adjacent (smoke 'Blend) (pet 'Cat))
                          (adjacent (pet 'Horse) (smoke 'Dunhill))
                          (same (drink 'Beer) (smoke 'BlueMaster))
                          (same (nat 'German) (smoke 'Prince))
                          (adjacent (nat 'Norwegian) (color 'Blue))
                          (adjacent (drink 'Water) (smoke 'Blend))))))
               (try-each-sym (subr zeff (syms (subr zeff (symbol syms) unit)) unit)
                 (lambda (l f)
                   (letrec ((loop (subr zeff (syms syms) unit)
                              (lambda (l ac)
                                (if (null? l)
                                    #u
                                    (begin (f (car l) (append-syms (cdr l) ac))
                                           (loop (cdr l) (cons (car l) ac)))))))
                     (loop l nil))))
               (try-each-int (subr zeff (ints (subr zeff (int ints) unit)) unit)
                 (lambda (l f)
                   (letrec ((loop (subr zeff (ints ints) unit)
                              (lambda (l ac)
                                (if (null? l)
                                    #u
                                    (begin (f (car l) (append-ints (cdr l) ac))
                                           (loop (cdr l) (cons (car l) ac)))))))
                     (loop l nil))))
               (try (subr zeff (attr-ref (subr zeff () each-done)) unit)
                 (lambda (r f)
                   (let* ((a (get r))
                          (poss (extract a poss))
                          (unknown (extract a unknown))
                          (known (extract a known)))
                     (if (null? unknown)
                         #u
                         (try-each-sym unknown
                           (lambda ((x symbol) (unknown syms))
                             (let ((ed (f)))
                               (begin
                                 (try-each-int poss
                                   (lambda ((p int) (poss ints))
                                     (let ((attr (product (poss poss) (unknown unknown) (known (the knowns (cons (product (pos p) (x x)) known))))))
                                       (fluid-let r attr
                                         (lambda () (if (is-consistent) ((extract ed each) attr) #u))))))
                                 ((extract ed finish))))))))))
               ;; loop takes the current state and either
               ;;   - terminates in the same state if there is no consistent extension
               ;;   - raises Done with the state set at the consistent extension
               (loop (subr zeff () unit)
                 (lambda ()
                   (letrec ((test (subr zeff (attr-ref) unit)
                              (lambda (r)
                                (try r
                                  (lambda ()
                                    (let ((attrs (the (ref attrs @heap) (new (none-attr)))))
                                      (product
                                        (each (lambda ((a attribute))
                                                (tagcase (get attrs)
                                                  (none-attr () (set attrs (one-attr a)))
                                                  (one-attr (b) (set attrs (many-attr)))
                                                  (many-attr () #u))))
                                        (finish (lambda ()
                                                  (tagcase (get attrs)
                                                    (none-attr () (raise (inconsistent)))
                                                    (one-attr (a) (raise (continue (lambda () (fluid-let r a loop)))))
                                                    (many-attr () #u))))))))))
                            (explore (subr zeff (attr-ref) unit)
                              (lambda (r)
                                (try r
                                  (lambda ()
                                    (product (each (lambda ((a attribute)) (loop)))
                                             (finish (lambda () (raise (inconsistent))))))))))
                     (prompt zebra-tag
                       (begin
                         (test cigarettes)
                         (test colors)
                         (test drinks)
                         (test nationalities)
                         (test pets)
                         (explore cigarettes)
                         (explore colors)
                         (explore drinks)
                         (explore nationalities)
                         (explore pets)
                         (raise (done)))
                       (lambda (e)
                         (tagcase e
                           (inconsistent () #u)
                           (continue (f) (f))
                           (else e (raise e)))))))))
        (begin
          (prompt zebra-tag (loop) (lambda (e) (tagcase e (done () #u) (else e (raise e)))))
          (get num))))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define iterations int 100)

(define* run (subr zeff (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (search)))))
(run iterations 0)
