;;; CONFORM -- Type checker, written by Jim Miller.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/conform.scm),
;;; ported to FX-26. Larceny's input: 500 iterations of
;;; (apply test '(a b "c" "d")).
;;; Answer: ("(((b v d) ^ a) v c)" "(c ^ d)" "(b v (a ^ d))" "((a v d) ^ b)"
;;;          "(b v d)" "(b ^ (a v c))" "(a v (c ^ d))" "((b v d) ^ a)"
;;;          "(c v (a v d))" "(a v c)" "(d v (b ^ (a v c)))" "(d ^ (a v c))"
;;;          "((a ^ d) v c)" "((a ^ b) v d)" "(((a v d) ^ b) v (a ^ d))"
;;;          "(b ^ d)" "(b v (a v d))" "(a ^ c)" "(b ^ (c v d))" "(a ^ b)"
;;;          "(a v b)" "((a ^ d) ^ b)" "(a ^ d)" "(a v d)" "d" "(c v d)" "a"
;;;          "b" "c" "any" "none")
;;;
;;; The original's vectors used as records (nodes, blue edges, graphs) are
;;; bloblets, FX-26's mutable records, with the same fields in the same
;;; order; `eq?` of nodes, what the benchmark runs on (`memq`, `assq`,
;;; `adjoin`, the ANY and NONE tests), is exact, since bloblets at a
;;; writable region are mutable objects. `memq` and `adjoin` are
;;; polymorphic, of nodes and of operations (symbols).
;;; The names given to `make-node` are symbols or strings in the original;
;;; here a `datum`, as `test`'s arguments are. A node's blue edges, which
;;; the original starts as `'NOT-A-NODE-YET` (or `#t`, for NONE), start
;;; as `nil`; they are never read before they are set, except ANY's,
;;; which are `'()` in both. `lookup` (of the two-dimensional tables)
;;; returns the entry, or `nil` for `#f`, and `meet` and `join` take its
;;; `cdr`; `lookup-op` returns the list of edges starting with the one
;;; found, or `nil` for `'()`, and `sig` takes its `car`. The edge
;;; setters' `'OK`, for NONE, unused, is `#u`, and the `error`s, never
;;; reached, take only a message. `make-lattice`'s printing, off in the
;;; benchmark, is left out. `setup`'s globals `a` `b` `c` `d`, which it
;;; `set!`s, are references, and its value, `'(made a b c d)`, unused, is
;;; `#u`. `make-graph`, variadic, takes a list. `map`, `for-each`, `memq`
;;; and `assq` are written out, polymorphic.
;;; Larceny checks the result with `equal?` against its input file; here
;;; the list of names is the program's value.

(define-type node (bloblet (fields string (listof node @heap) (listof node @heap)
                                  (listof (bloblet (fields symbol node node) @heap) @heap))
                          @heap))
(define-type edge (bloblet (fields symbol node node) @heap))
(define-type nodes (listof node @heap))
;; A two-dimensional table: `(TABLE (x (y . value) …) …)`.
(define-type line (listof (pairof node node @heap) @heap))
(define-type table (pairof symbol (listof (pairof node line @heap) @heap) @heap))
(define-type graph (bloblet (fields nodes table table) @heap))

;; What the benchmark's procedures do: read, write and build its data,
;; recurse, and call each other.
(define-effect cf
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals map for-each memq adjoin eliminate intersect union
                         sort-list make-internal-node internal-node-name
                         internal-node-green-edges internal-node-red-edges internal-node-blue-edges
                         set-internal-node-name! set-internal-node-green-edges!
                         set-internal-node-red-edges! set-internal-node-blue-edges!
                         make-node copy-node name red-edges green-edges blue-edges
                         set-red-edges! set-green-edges! set-blue-edges!
                         make-blue-edge blue-edge-operation blue-edge-arg-node blue-edge-res-node
                         set-blue-edge-operation! set-blue-edge-arg-node! set-blue-edge-res-node!
                         operation arg-node res-node set-arg-node! set-res-node!
                         lookup-op has-op? make-internal-graph internal-graph-nodes
                         internal-graph-already-met internal-graph-already-joined
                         set-internal-graph-nodes! make-graph graph-nodes already-met already-joined
                         add-graph-nodes! copy-graph clean-graph canonicalize-graph
                         none-node none-node? any-node any-node? green-edge? red-edge?
                         none-comma-any sig arg res conforms? equivalent? classify
                         find-canonical-representative reduce make-empty-table assq lookup insert!
                         blue-edge-operate meet join make-lattice a b c d setup test))))

(define map
  (poly ((s type) (t type) (e effect))
    (subr (maxeff e (read @heap) (alloc @heap) spin) ((subr e (s) t) (listof s @heap)) (listof t @heap)))
  (plambda ((s type) (t type) (e effect))
    (lambda (f l)
      (letrec ((loop (subr (maxeff e (read @heap) (alloc @heap) spin) ((listof s @heap)) (listof t @heap))
                 (lambda (l) (if (null? l) nil (cons (f (car l)) (loop (cdr l)))))))
        (loop l)))))

(define for-each
  (poly ((s type) (e effect))
    (subr (maxeff e (read @heap) spin) ((subr e (s) unit) (listof s @heap)) unit))
  (plambda ((s type) (e effect))
    (lambda (f l)
      (letrec ((loop (subr (maxeff e (read @heap) spin) ((listof s @heap)) unit)
                 (lambda (l) (if (null? l) #u (begin (f (car l)) (loop (cdr l)))))))
        (loop l)))))

;;; Functional and unstable

(define* sort-list (subr cf (nodes (subr cf (node node) bool)) nodes)
  (lambda (obj pred)
    (letrec ((loop (subr cf (nodes) nodes)
               (lambda (l)
                 (if (and (not (null? l)) (not (null? (cdr l))))
                     (split-list l nil nil)
                     l)))
             (split-list (subr cf (nodes nodes nodes) nodes)
               (lambda (l one two)
                 (if (not (null? l))
                     (split-list (cdr l) two (cons (car l) one))
                     (merge (loop one) (loop two)))))
             (merge (subr cf (nodes nodes) nodes)
               (lambda (one two)
                 (cond ((null? one) two)
                       ((pred (car two) (car one))
                        (cons (car two)
                              (merge (cdr two) one)))
                       (else
                        (cons (car one)
                              (merge (cdr one) two)))))))
      (loop obj))))

;; `memq` and `adjoin`, of nodes and of operations (symbols).
(define memq
  (poly ((t type))
    (subr (maxeff (read @heap) spin (read (globals memq))) (t (listof t @heap)) bool))
  (plambda ((t type))
    (lambda (x l)
      (cond ((null? l) #f)
            ((eq? x (car l)) #t)
            (else (memq x (cdr l)))))))

;; SET OPERATIONS
; (representation as lists with distinct elements)

(define adjoin
  (poly ((t type))
    (subr (maxeff (read @heap) (alloc @heap) spin (read (globals memq)))
          (t (listof t @heap)) (listof t @heap)))
  (plambda ((t type))
    (lambda (element set)
      (if (memq element set) set (cons element set)))))

(define* eliminate (subr cf (node nodes) nodes)
  (lambda (element set)
    (cond ((null? set) set)
          ((eq? element (car set)) (cdr set))
          (else (cons (car set) (eliminate element (cdr set)))))))

(define* intersect (subr (maxeff (read @heap) (alloc @heap) spin (read (globals memq))) ((listof symbol @heap) (listof symbol @heap)) (listof symbol @heap))
  (lambda (list1 list2)
    (letrec ((loop (subr (maxeff (read @heap) (alloc @heap) spin (read (globals memq))) ((listof symbol @heap)) (listof symbol @heap))
               (lambda (l)
                 (cond ((null? l) nil)
                       ((memq (car l) list2) (cons (car l) (loop (cdr l))))
                       (else (loop (cdr l)))))))
      (loop list1))))

(define* union (subr (maxeff (read @heap) (alloc @heap) spin (read (globals memq adjoin))) ((listof symbol @heap) (listof symbol @heap)) (listof symbol @heap))
  (lambda (list1 list2)
    (if (null? list1)
        list2
        (union (cdr list1)
               (adjoin (car list1) list2)))))

;; GRAPH NODES

(define* make-internal-node (subr (alloc @heap) (string nodes nodes (listof edge @heap)) node)
  (lambda (name green red blue) (make-bloblet 0 name green red blue)))
(define* internal-node-name (subr (read @heap) (node) string) (lambda (node) (bloblet-ref node 0)))
(define* internal-node-green-edges (subr (read @heap) (node) nodes) (lambda (node) (bloblet-ref node 1)))
(define* internal-node-red-edges (subr (read @heap) (node) nodes) (lambda (node) (bloblet-ref node 2)))
(define* internal-node-blue-edges (subr (read @heap) (node) (listof edge @heap)) (lambda (node) (bloblet-ref node 3)))
(define* set-internal-node-name! (subr (write @heap) (node string) unit) (lambda (node name) (bloblet-set! node 0 name)))
(define* set-internal-node-green-edges! (subr (write @heap) (node nodes) unit) (lambda (node edges) (bloblet-set! node 1 edges)))
(define* set-internal-node-red-edges! (subr (write @heap) (node nodes) unit) (lambda (node edges) (bloblet-set! node 2 edges)))
(define* set-internal-node-blue-edges! (subr (write @heap) (node (listof edge @heap)) unit) (lambda (node edges) (bloblet-set! node 3 edges)))

(define* make-node (subr cf (datum (listof edge @heap)) node)   ; User's constructor
  (lambda (name blue-edges)
    (let ((name (if (datum-symbol? name) (datum-symbol-name name) (datum-string-value name))))
      (make-internal-node name nil nil blue-edges))))

; Selectors

(define* name (subr (read @heap) (node) string) (lambda (node) (internal-node-name node)))

;; USEFUL NODES
;; (Here, before the edge getters and setters, which test for them: an
;; FX-26 definition sees only those before it.)

(define none-node node (make-node (datum-symbol "none") nil))
(define* none-node? (subr (read @heap) (node) bool) (lambda (node) (eq? node none-node)))

(define any-node node (make-node (datum-symbol "any") nil))
(define* any-node? (subr (read @heap) (node) bool) (lambda (node) (eq? node any-node)))

;; `make-edge-getter`, and each getter it makes, which ANY and NONE
;; refuse.
(define make-edge-getter
  (poly ((t type)) (subr pure ((subr (read @heap) (node) (listof t @heap))) (subr cf (node) (listof t @heap))))
  (plambda ((t type))
    (lambda (selector)
      (lambda ((node node))
        (if (or (none-node? node) (any-node? node))
            (error "Can't get edges from the ANY or NONE nodes")
            (selector node))))))
(define red-edges (subr cf (node) nodes) (make-edge-getter internal-node-red-edges))
(define green-edges (subr cf (node) nodes) (make-edge-getter internal-node-green-edges))
(define blue-edges (subr cf (node) (listof edge @heap)) (make-edge-getter internal-node-blue-edges))

; Mutators

(define make-edge-setter
  (poly ((t type)) (subr pure ((subr (write @heap) (node (listof t @heap)) unit)) (subr cf (node (listof t @heap)) unit)))
  (plambda ((t type))
    (lambda (mutator!)
      (lambda ((node node) (value (listof t @heap)))
        (cond ((any-node? node) (error "Can't set edges from the ANY node"))
              ((none-node? node) #u)    ; 'OK
              (else (mutator! node value)))))))
(define set-red-edges! (subr cf (node nodes) unit) (make-edge-setter set-internal-node-red-edges!))
(define set-green-edges! (subr cf (node nodes) unit) (make-edge-setter set-internal-node-green-edges!))
(define set-blue-edges! (subr cf (node (listof edge @heap)) unit) (make-edge-setter set-internal-node-blue-edges!))

;; (`copy-node`, here after the getters it calls.)
(define* copy-node (subr cf (node) node)
  (lambda (node)
    (make-internal-node (name node) nil nil (blue-edges node))))

;; BLUE EDGES

(define* make-blue-edge (subr (alloc @heap) (symbol node node) edge)
  (lambda (op arg res) (make-bloblet 0 op arg res)))
(define* blue-edge-operation (subr (read @heap) (edge) symbol) (lambda (edge) (bloblet-ref edge 0)))
(define* blue-edge-arg-node (subr (read @heap) (edge) node) (lambda (edge) (bloblet-ref edge 1)))
(define* blue-edge-res-node (subr (read @heap) (edge) node) (lambda (edge) (bloblet-ref edge 2)))
(define* set-blue-edge-operation! (subr (write @heap) (edge symbol) unit) (lambda (edge value) (bloblet-set! edge 0 value)))
(define* set-blue-edge-arg-node! (subr (write @heap) (edge node) unit) (lambda (edge value) (bloblet-set! edge 1 value)))
(define* set-blue-edge-res-node! (subr (write @heap) (edge node) unit) (lambda (edge value) (bloblet-set! edge 2 value)))

; Selectors
(define* operation (subr (read @heap) (edge) symbol) (lambda (edge) (blue-edge-operation edge)))
(define* arg-node (subr (read @heap) (edge) node) (lambda (edge) (blue-edge-arg-node edge)))
(define* res-node (subr (read @heap) (edge) node) (lambda (edge) (blue-edge-res-node edge)))

; Mutators
(define* set-arg-node! (subr (write @heap) (edge node) unit) (lambda (edge value) (set-blue-edge-arg-node! edge value)))
(define* set-res-node! (subr (write @heap) (edge node) unit) (lambda (edge value) (set-blue-edge-res-node! edge value)))

; Higher level operations on blue edges

(define* lookup-op (subr cf (symbol node) (listof edge @heap))
  (lambda (op node)
    (letrec ((loop (subr cf ((listof edge @heap)) (listof edge @heap))
               (lambda (edges)
                 (cond ((null? edges) nil)
                       ((eq? op (operation (car edges))) edges)
                       (else (loop (cdr edges)))))))
      (loop (blue-edges node)))))

(define* has-op? (subr cf (symbol node) bool)
  (lambda (op node)
    (not (null? (lookup-op op node)))))

;; GRAPHS

(define* make-internal-graph (subr (alloc @heap) (nodes table table) graph)
  (lambda (nodes met joined) (make-bloblet 0 nodes met joined)))
(define* internal-graph-nodes (subr (read @heap) (graph) nodes) (lambda (graph) (bloblet-ref graph 0)))
(define* internal-graph-already-met (subr (read @heap) (graph) table) (lambda (graph) (bloblet-ref graph 1)))
(define* internal-graph-already-joined (subr (read @heap) (graph) table) (lambda (graph) (bloblet-ref graph 2)))
(define* set-internal-graph-nodes! (subr (write @heap) (graph nodes) unit) (lambda (graph nodes) (bloblet-set! graph 0 nodes)))

;; TWO DIMENSIONAL TABLES
;; (Here, before `make-graph`, which makes two.)

(define* make-empty-table (subr (alloc @heap) () table) (lambda () (cons 'TABLE nil)))

(define assq
  (poly ((v type)) (subr (maxeff (read @heap) spin (read (globals assq))) (node (listof (pairof node v @heap) @heap)) (union nil (pairof node v @heap))))
  (plambda ((v type))
    (lambda (x l)
      (cond ((null? l) no-pair)
            ((eq? x (car (car l))) (car l))
            (else (assq x (cdr l)))))))

;; The entry for `x` and `y`, or `nil` for `#f`.
(define* lookup (subr cf (table node node) (union nil (pairof node node @heap)))
  (lambda (table x y)
    (let ((one (assq x (cdr table))))
      (if (not (null? one))
          (let ((two (assq y (cdr one))))
            (if (not (null? two)) two no-pair))
          no-pair))))

(define* insert! (subr cf (table node node node) unit)
  (lambda (table x y value)
    (letrec ((make-singleton-table (subr (alloc @heap) (node node) line)
               (lambda (x y)
                 (cons (cons x y) nil))))
      (let ((one (assq x (cdr table))))
        (if (not (null? one))
            (set-cdr! one (cons (cons y value) (cdr one)))
            (set-cdr! table (cons (cons x (make-singleton-table y value))
                                  (cdr table))))))))

; Constructor

(define* make-graph (subr cf (nodes) graph)
  (lambda (nodes)
    (make-internal-graph nodes (make-empty-table) (make-empty-table))))

; Selectors

(define* graph-nodes (subr (read @heap) (graph) nodes) (lambda (graph) (internal-graph-nodes graph)))
(define* already-met (subr (read @heap) (graph) table) (lambda (graph) (internal-graph-already-met graph)))
(define* already-joined (subr (read @heap) (graph) table) (lambda (graph) (internal-graph-already-joined graph)))

; Higher level functions on graphs

;; (In the original `nodes` is one node here: it conses it on.)
(define* add-graph-nodes! (subr cf (graph node) unit)
  (lambda (graph nodes)
    (set-internal-graph-nodes! graph (cons nodes (graph-nodes graph)))))

(define* copy-graph (subr cf (graph) graph)
  (lambda (g)
    (letrec ((copy-list (subr cf (nodes) nodes)
               (lambda (l) (array->list (the (arrayof node @heap) (list->array l))))))
      (make-internal-graph
       (copy-list (graph-nodes g))
       (already-met g)
       (already-joined g)))))

(define* clean-graph (subr cf (graph) graph)
  (lambda (g)
    (letrec ((clean-node (subr cf (node) unit)
               (lambda (node)
                 (if (not (or (any-node? node) (none-node? node)))
                     (begin
                       (set-green-edges! node nil)
                       (set-red-edges! node nil))
                     #u))))
      (begin
        (for-each clean-node (graph-nodes g))
        g))))

;; (`canonicalize-graph` is below, after `find-canonical-representative`,
;; which it calls.)

;; COLORED EDGE TESTS

(define* green-edge? (subr cf (node node) bool)
  (lambda (from-node to-node)
    (cond ((any-node? from-node) #f)
          ((none-node? from-node) #t)
          ((memq to-node (green-edges from-node)) #t)
          (else #f))))

(define* red-edge? (subr cf (node node) bool)
  (lambda (from-node to-node)
    (cond ((any-node? from-node) #f)
          ((none-node? from-node) #t)
          ((memq to-node (red-edges from-node)) #t)
          (else #f))))

;; SIGNATURE

; Return signature (i.e. <arg, res>) given an operation and a node

(define none-comma-any (pairof node node @heap) (cons none-node any-node))
(define* sig (subr cf (symbol node) (pairof node node @heap))
  (lambda (op node)                     ; Returns (arg, res)
    (let ((the-edges (lookup-op op node)))
      (if (not (null? the-edges))
          (cons (arg-node (car the-edges)) (res-node (car the-edges)))
          none-comma-any))))

; Selectors from signature

(define* arg (subr (read @heap) ((pairof node node @heap)) node) (lambda (pair) (car pair)))
(define* res (subr (read @heap) ((pairof node node @heap)) node) (lambda (pair) (cdr pair)))

;; CONFORMITY

(define* conforms? (subr cf (node node) bool)
  (lambda (t1 t2)
    (let ((nodes-with-red-edges-out (the (ref nodes @heap) (new nil))))
      (letrec ((add-red-edge! (subr cf (node node) unit)
                 (lambda (from-node to-node)
                   (begin
                     (set-red-edges! from-node (adjoin to-node (red-edges from-node)))
                     (set nodes-with-red-edges-out
                          (adjoin from-node (get nodes-with-red-edges-out))))))
               (greenify-red-edges! (subr cf (node) unit)
                 (lambda (from-node)
                   (begin
                     (set-green-edges! from-node
                                       (append (red-edges from-node) (green-edges from-node)))
                     (set-red-edges! from-node nil))))
               (delete-red-edges! (subr cf (node) unit)
                 (lambda (from-node)
                   (set-red-edges! from-node nil)))
               (does-conform (subr cf (node node) bool)
                 (lambda (t1 t2)
                   (cond ((or (none-node? t1) (any-node? t2)) #t)
                         ((or (any-node? t1) (none-node? t2)) #f)
                         ((green-edge? t1 t2) #t)
                         ((red-edge? t1 t2) #t)
                         (else
                          (begin
                            (add-red-edge! t1 t2)
                            (letrec ((loop (subr cf ((listof edge @heap)) bool)
                                       (lambda (blues)
                                         (if (null? blues)
                                             #t
                                             (let* ((current-edge (car blues))
                                                    (phi (operation current-edge)))
                                               (and (has-op? phi t1)
                                                    (does-conform
                                                     (res (sig phi t1))
                                                     (res (sig phi t2)))
                                                    (does-conform
                                                     (arg (sig phi t2))
                                                     (arg (sig phi t1)))
                                                    (loop (cdr blues))))))))
                              (loop (blue-edges t2)))))))))
        (let ((result (does-conform t1 t2)))
          (begin
            (for-each (if result greenify-red-edges! delete-red-edges!)
                      (get nodes-with-red-edges-out))
            result))))))

(define* equivalent? (subr cf (node node) bool)
  (lambda (a b)
    (and (conforms? a b) (conforms? b a))))

;; EQUIVALENCE CLASSIFICATION
; Given a list of nodes, return a list of equivalence classes

(define* classify (subr cf (nodes) (listof nodes @heap))
  (lambda (nodes)
    (letrec ((node-loop (subr cf ((listof nodes @heap) nodes) (listof nodes @heap))
               (lambda (classes nodes)
                 (if (null? nodes)
                     (map (lambda (class)
                            (sort-list class
                                       (lambda (node1 node2)
                                         (< (string-length (name node1))
                                            (string-length (name node2))))))
                          classes)
                     (let ((this-node (car nodes)))
                       (letrec ((add-node (subr cf ((listof nodes @heap)) (listof nodes @heap))
                                  (lambda (classes)
                                    (cond ((null? classes) (cons (cons this-node nil) nil))
                                          ((equivalent? this-node (car (car classes)))
                                           (cons (cons this-node (car classes))
                                                 (cdr classes)))
                                          (else (cons (car classes)
                                                      (add-node (cdr classes))))))))
                         (node-loop (add-node classes)
                                    (cdr nodes))))))))
      (node-loop nil nodes))))

; Given a node N and a classified set of nodes,
; find the canonical member corresponding to N

(define* find-canonical-representative (subr cf (node (listof nodes @heap)) node)
  (lambda (element classification)
    (letrec ((loop (subr cf ((listof nodes @heap)) node)
               (lambda (classes)
                 (cond ((null? classes) (error "Can't classify")) ; element too, in the original
                       ((memq element (car classes)) (car (car classes)))
                       (else (loop (cdr classes)))))))
      (loop classification))))

(define* canonicalize-graph (subr cf (graph (listof nodes @heap)) graph)
  (lambda (graph classes)
    (letrec ((fix (subr cf (node) node)
               (lambda (node)
                 (letrec ((fix-set (subr cf (node (subr cf (node) nodes) (subr cf (node nodes) unit)) unit)
                            (lambda (object selector mutator)
                              (mutator object
                                       (map (lambda (node)
                                              (find-canonical-representative node classes))
                                            (selector object))))))
                   (begin
                     (if (not (or (none-node? node) (any-node? node)))
                         (begin
                           (fix-set node green-edges set-green-edges!)
                           (fix-set node red-edges set-red-edges!)
                           (for-each
                            (lambda (blue-edge)
                              (begin
                                (set-arg-node! blue-edge
                                               (find-canonical-representative (arg-node blue-edge) classes))
                                (set-res-node! blue-edge
                                               (find-canonical-representative (res-node blue-edge) classes))))
                            (blue-edges node)))
                         #u)
                     node))))
             (fix-table (subr cf (table) table)
               (lambda (table)
                 (letrec ((canonical? (subr cf (node) bool)
                            (lambda (node) (eq? node (find-canonical-representative node classes))))
                          (fix-line (subr cf (line) line)
                            (lambda (line)
                              (letrec ((filter-and-fix (subr cf (line) line)
                                         (lambda (list)
                                           (cond ((null? list) nil)
                                                 ((canonical? (car (car list)))
                                                  (cons (cons (car (car list))
                                                              (find-canonical-representative (cdr (car list)) classes))
                                                        (filter-and-fix (cdr list))))
                                                 (else (filter-and-fix (cdr list)))))))
                                (filter-and-fix line))))
                          (filter-and-fix (subr cf ((listof (pairof node line @heap) @heap)) (listof (pairof node line @heap) @heap))
                            (lambda (list)
                              (cond ((null? list) nil)
                                    ((canonical? (car (car list)))
                                     (cons (cons (car (car list)) (fix-line (cdr (car list))))
                                           (filter-and-fix (cdr list))))
                                    (else (filter-and-fix (cdr list)))))))
                   ;; (The original's `table` is never '(): it is `(TABLE …)`.)
                   (the table
                        (cons (car table)
                              (filter-and-fix (cdr table))))))))
      (make-internal-graph
       (map (lambda (class) (fix (car class))) classes)
       (fix-table (already-met graph))
       (fix-table (already-joined graph))))))

; Reduce a graph by taking only one member of each equivalence
; class and canonicalizing all outbound pointers

(define* reduce (subr cf (graph) graph)
  (lambda (graph)
    (let ((classes (classify (graph-nodes graph))))
      (canonicalize-graph graph classes))))

;; MEET/JOIN
; These update the graph when computing the node for node1*node2

(define* blue-edge-operate (subr cf ((subr cf (graph node node) node) (subr cf (graph node node) node) graph symbol
                                     (pairof node node @heap) (pairof node node @heap))
                                 edge)
  (lambda (arg-fn res-fn graph op sig1 sig2)
    (make-blue-edge op
                    (arg-fn graph (arg sig1) (arg sig2))
                    (res-fn graph (res sig1) (res sig2)))))

(define-rec
  (meet (subr cf (graph node node) node)
    (lambda (graph node1 node2)
      (let ((found (lookup (already-met graph) node1 node2)))
        (cond ((eq? node1 node2) node1)
              ((or (any-node? node1) (any-node? node2)) any-node) ; canonicalize
              ((none-node? node1) node2)
              ((none-node? node2) node1)
              ((not (null? found)) (cdr found)) ; return it if found
              ((conforms? node1 node2) node2)
              ((conforms? node2 node1) node1)
              (else
               (let ((result
                      (make-node (datum-string (string-append "(" (string-append (name node1) (string-append " ^ " (string-append (name node2) ")")))))
                                 nil)))
                 (begin
                   (add-graph-nodes! graph result)
                   (insert! (already-met graph) node1 node2 result)
                   (set-blue-edges! result
                                    (map
                                     (lambda (op)
                                       (blue-edge-operate join meet graph op (sig op node1) (sig op node2)))
                                     (intersect (map operation (blue-edges node1))
                                                (map operation (blue-edges node2)))))
                   result)))))))
  (join (subr cf (graph node node) node)
    (lambda (graph node1 node2)
      (let ((found (lookup (already-joined graph) node1 node2)))
        (cond ((eq? node1 node2) node1)
              ((any-node? node1) node2)
              ((any-node? node2) node1)
              ((or (none-node? node1) (none-node? node2)) none-node) ; canonicalize
              ((not (null? found)) (cdr found)) ; return it if found
              ((conforms? node1 node2) node1)
              ((conforms? node2 node1) node2)
              (else
               (let ((result
                      (make-node (datum-string (string-append "(" (string-append (name node1) (string-append " v " (string-append (name node2) ")")))))
                                 nil)))
                 (begin
                   (add-graph-nodes! graph result)
                   (insert! (already-joined graph) node1 node2 result)
                   (set-blue-edges! result
                                    (map
                                     (lambda (op)
                                       (blue-edge-operate meet join graph op (sig op node1) (sig op node2)))
                                     (union (map operation (blue-edges node1))
                                            (map operation (blue-edges node2)))))
                   result))))))))

;; MAKE A LATTICE FROM A GRAPH

(define* make-lattice (subr cf (graph) graph)
  (lambda (g)
    (letrec ((step (subr cf (graph) graph)
               (lambda (g)
                 (let* ((copy (copy-graph g))
                        (nodes (graph-nodes copy)))
                   (begin
                     (for-each (lambda (first)
                                 (for-each (lambda (second)
                                             (begin (meet copy first second) (join copy first second) #u))
                                           nodes))
                               nodes)
                     copy))))
             (loop (subr cf (graph int) graph)
               (lambda (g count)
                 (let ((lattice (step g)))
                   (let* ((new-g (reduce lattice))
                          (new-count (list-length (graph-nodes new-g))))
                     (if (= new-count count)
                         new-g
                         (loop new-g new-count)))))))
      (let ((graph
             (make-graph
              (adjoin any-node (adjoin none-node (graph-nodes (clean-graph g)))))))
        (loop graph (list-length (graph-nodes graph)))))))

;; DEBUG and TEST

(define a (ref node @heap) (new any-node))
(define b (ref node @heap) (new any-node))
(define c (ref node @heap) (new any-node))
(define d (ref node @heap) (new any-node))

(define* setup (subr cf (datum datum datum datum) unit)
  (lambda (a0 b0 c0 d0)
    (begin
      (set a (make-node a0 nil))
      (set b (make-node b0 nil))
      (set-blue-edges! (get a) (cons (make-blue-edge 'phi any-node (get b)) nil))
      (set-blue-edges! (get b) (list (make-blue-edge 'phi any-node (get a))
                                     (make-blue-edge 'theta any-node (get b))))
      (set c (make-node c0 nil))
      (set d (make-node d0 nil))
      (set-blue-edges! (get c) (cons (make-blue-edge 'theta any-node (get b)) nil))
      (set-blue-edges! (get d) (list (make-blue-edge 'phi any-node (get c))
                                     (make-blue-edge 'theta any-node (get d))))
      #u)))                             ; '(made a b c d)

(define* test (subr cf (datum datum datum datum) (listof string @heap))
  (lambda (a0 b0 c0 d0)
    (begin
      (setup a0 b0 c0 d0)
      (map name
           (graph-nodes (make-lattice (make-graph (list (get a) (get b) (get c) (get d) any-node none-node))))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace. `(a b "c" "d")`:
(define input1 datum
  (datum-cons (datum-symbol "a")
              (datum-cons (datum-symbol "b")
                          (datum-cons (datum-string "c")
                                      (datum-cons (datum-string "d")
                                                  (datum-list (the (listof datum @heap) nil)))))))
(define iterations int 500)

;; `(apply test input1)`
(define* apply-test (subr (maxeff cf (read (globals test))) (datum) (listof string @heap))
  (lambda (l)
    (test (datum-car l)
          (datum-car (datum-cdr l))
          (datum-car (datum-cdr (datum-cdr l)))
          (datum-car (datum-cdr (datum-cdr (datum-cdr l)))))))

(define* run (subr (maxeff cf (read (globals apply-test input1))) (int (listof string @heap)) (listof string @heap))
  (lambda (i result) (if (= i 0) result (run (- i 1) (apply-test input1)))))
(run iterations nil)
