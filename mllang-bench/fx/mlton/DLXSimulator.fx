;;; DLXSIMULATOR -- a simulator of the DLX processor (Patterson and
;;; Hennessy's RISC) with a small level 1 cache in front of a 65536-word
;;; memory, running five DLX programs: Simple, Twos, Abs, Fact and GCD.
;;;
;;; Matthew Thomas Fluet, Harvey Mudd College; minor tweaks by Stephen
;;; Weeks (2001-07-17) to make it a benchmark, and more by Matthew Fluet
;;; (2017-12-06).
;;; From MLton's benchmark suite (benchmark/tests/DLXSimulator.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): (Main.doit 1), each of the five programs run once.
;;; Where the original prints, the port hashes: each character printed
;;; updates h := (h * 131 + code) mod 1000000007, from h = 0.
;;; Answer: 477019433, that hash of the 1404 characters the original
;;; prints: each program's outputs ("Output: 47", "Output: ~10", "Output:
;;; 10", "Output: 479001600", "Output: 1") and its cache and memory
;;; statistics. A Python transcription of the simulator gives the same
;;; text, and so the same hash; only the last run prints, and no run
;;; prints an error, so the answer is the same for any count.
;;;
;;; What changed:
;;; - Word32.word is `u32`. FX-26 has no literals of type u32, so each
;;;   constant is `int->u32` of an int. `u32-shl` and `u32-shr` take their
;;;   count modulo 32, where SML's `<<` and `>>` give 0 for 32 or more, and
;;;   `~>>` the sign: `shl`, `shr` and `ashr` are SML's. `Word32.toIntX` is
;;;   `to-intx`; MLton's Int is 32 bits, so the ALU's signed `ADD` and `SUB`
;;;   overflow outside them, as the original's raise Overflow, and the ALU's
;;;   handler prints its error and gives 0 (`int32`). `Word32.fromString`
;;;   is `from-string`, of hex digits, the only form the programs use.
;;; - ImmArray is a list, as the original's is, and does the same work:
;;;   `update` copies the prefix twice (`take`, then `@`), in two reversals
;;;   here, so that no recursion is as deep as the memory is long; so is
;;;   `tabulate`'s. Only the ImmArray functions used are written; ImmArray2,
;;;   never used, is left out, and so are Memory's LoadHWord ... StoreByte,
;;;   which the cache (the simulator's memory) never calls, and the cache's
;;;   StoreHWord, which the simulator never calls (its SH calls StoreByte).
;;; - A branch's target, `Word32.fromInt (Int.+ ...)`, would raise Overflow
;;;   past 32 bits, uncaught; here it wraps. No program branches that far.
;;; - The functors are applied once, as the benchmark applies them: the
;;;   cache's specification is L1CacheSpec1's, its memory is Memory, and
;;;   the simulator's memory is the cache (`DLXSimulatorC1`). Two memories'
;;;   procedures of one name are prefixed: `mem-` for Memory's, `c-` for the
;;;   cache's. The ALU's operations are `A-ADD`, ... apart from the
;;;   register-register function codes, `ADD`, ...
;;; - SML's records and tuples are products; the trap's polymorphic
;;;   `'state` is the benchmark's (inputs, outputs), and a trap's functions
;;;   take and give that state rather than records of it.
;;; - `run_file` (file input) is left out. Printing is hashing, into the
;;;   global `out-hash`; `rand`'s seed is a global too.

(define-type words (listof u32 @i))
(define-type ints (listof int @i))

;; What the simulator does, and procedures given to others (to `foldr`,
;; `map`, the trap, a load or store) may do: the globals are those they read.
(define-effect cb
  (maxeff (read @i) (alloc @i) (read @o) (write @o) spin
          (read (globals Associativity BlockOffsetBits BlockSize CacheName CacheSize IndexBits
                         TagBits WriteHit WriteMiss align-hw-address align-w-address ashr
                         block-address c-in-cache c-in-entry c-in-set c-load c-load-byte-of
                         c-load-cache c-load-entry c-load-hword-of c-load-set c-read-cache
                         c-read-entry c-read-set c-statistics c-store c-write-cache
                         c-write-entry c-write-set cmem concat get-block-offset get-index
                         get-tag ia-foldr ia-map ia-nth ia-tabulate ia-update int-to-string
                         load-block mem-load mem-load-word mem-statistics mem-store
                         mem-store-word memory-error out-hash print-string rand rand-entry seed
                         shl shr store-block tstate-of word-toint zero-block))))

;; ---- Printing, hashed.

(define out-hash (ref int @o) (new 0))

(define* print-string (subr (maxeff (read @o) (write @o) spin) (string) unit)
  (lambda (s)
    (letrec ((loop (subr (maxeff (read @o) (write @o) spin (read (globals out-hash))) (int) unit)
               (lambda (i)
                 (if (< i (string-length s))
                     (begin
                       (set out-hash (modulo (+ (* (get out-hash) 131)
                                                (char->integer (string-ref s i)))
                                             1000000007))
                       (loop (+ i 1)))
                     #u))))
      (loop 0))))

;; Int.toString: a negative number's sign is ~.
(define* int-to-string (subr pure (int) string)
  (lambda (n) (if (< n 0) (string-append "~" (int->string (- 0 n))) (int->string n))))

;; String.concat
(define* concat (subr spin ((listof string acyclic)) string)
  (lambda (l) (if (null? l) "" (string-append (car l) (concat (cdr l))))))

;; ---- Word32

;; SML's <<, >> and ~>>: a count of 32 or more shifts every bit out.
(define* shl (subr pure (u32 int) u32) (lambda (x n) (if (>= n 32) (int->u32 0) (u32-shl x n))))
(define* shr (subr pure (u32 int) u32) (lambda (x n) (if (>= n 32) (int->u32 0) (u32-shr x n))))
(define* ashr (subr pure (u32 int) u32)
  (lambda (x n)
    (let ((n (if (>= n 32) 31 n)))
      (if (u32< x (int->u32 2147483648)) (u32-shr x n) (u32-not (u32-shr (u32-not x) n))))))

;; Word.fromLarge (Word32.toLarge w), as a shift's count.
(define* word-toint (subr pure (u32) int) (lambda (w) (u32->int w)))

;; Word32.toIntX
(define* to-intx (subr pure (u32) int)
  (lambda (w) (let ((v (u32->int w))) (if (< v 2147483648) v (- v 4294967296)))))

;; Word32.fromString of hex digits.
(define-datatype word-option (NONE) (SOME u32))
(define* from-string (subr spin (string) word-option)
  (lambda (s)
    (letrec ((loop (subr (maxeff spin (read (globals NONE SOME))) (int int) word-option)
               (lambda (i acc)
                 (if (= i (string-length s))
                     (SOME (int->u32 acc))
                     (let ((c (char->integer (string-ref s i))))
                       (cond ((and (>= c 48) (<= c 57)) (loop (+ i 1) (+ (* acc 16) (- c 48))))
                             ((and (>= c 65) (<= c 70)) (loop (+ i 1) (+ (* acc 16) (- c 55))))
                             ((and (>= c 97) (<= c 102)) (loop (+ i 1) (+ (* acc 16) (- c 87))))
                             (else (NONE))))))))
      (if (= (string-length s) 0) (NONE) (loop 0 0)))))

;; sweeks added rand: from page 284 of Numerical Recipes in C.
(define seed (ref u32 @o) (new (int->u32 13)))
(define* rand (subr (maxeff (read @o) (write @o)) () u32)
  (lambda ()
    (let ((res (u32+ (u32* (int->u32 1664525) (get seed)) (int->u32 1013904223))))
      (begin (set seed res) res))))

;; ---- ImmArray: an immutable array is a list.

(define ia-tabulate (poly ((a type)) (subr (maxeff (alloc @i) spin) (int (subr pure (int) a))
                                           (listof a @i)))
  (plambda ((a type))
    (lambda (n f)
      (letrec ((loop (subr (maxeff (alloc @i) spin) (int (listof a @i)) (listof a @i))
                 (lambda (i acc) (if (< i 0) acc (loop (- i 1) (cons (f i) acc))))))
        (loop (- n 1) nil)))))

(define ia-nth (poly ((a type)) (subr (maxeff (read @i) spin) ((listof a @i) int) a))
  (plambda ((a type))
    (lambda (l i)
      (letrec ((loop (subr (maxeff (read @i) spin) ((listof a @i) int) a)
                 (lambda (l i) (if (= i 0) (car l) (loop (cdr l) (- i 1))))))
        (loop l i)))))

;; ImmArray.update (IA ia, i, x) = IA ((List.take (ia, i)) @ (x :: List.drop (ia, i + 1))).
(define ia-update
  (poly ((a type)) (subr (maxeff (read @i) (alloc @i) spin) ((listof a @i) int a) (listof a @i)))
  (plambda ((a type))
    (lambda (l i x)
      (letrec ((rev-take (subr (maxeff (read @i) (alloc @i) spin)
                               ((listof a @i) int (listof a @i)) (listof a @i))
                 (lambda (l i acc) (if (= i 0) acc (rev-take (cdr l) (- i 1) (cons (car l) acc)))))
               (rev-onto (subr (maxeff (read @i) (alloc @i) spin)
                               ((listof a @i) (listof a @i)) (listof a @i))
                 (lambda (r l) (if (null? r) l (rev-onto (cdr r) (cons (car r) l)))))
               (drop (subr (maxeff (read @i) spin) ((listof a @i) int) (listof a @i))
                 (lambda (l i) (if (= i 0) l (drop (cdr l) (- i 1))))))
        (rev-onto (rev-take l i nil) (cons x (drop l (+ i 1))))))))

(define ia-foldr (poly ((a type) (b type)) (subr cb ((subr cb (a b) b) b (listof a @i)) b))
  (plambda ((a type) (b type))
    (lambda (f b l)
      (letrec ((loop (subr cb ((listof a @i)) b)
                 (lambda (l) (if (null? l) b (f (car l) (loop (cdr l)))))))
        (loop l)))))

(define ia-map (poly ((a type) (b type)) (subr cb ((subr cb (a) b) (listof a @i)) (listof b @i)))
  (plambda ((a type) (b type))
    (lambda (f l)
      (letrec ((loop (subr cb ((listof a @i)) (listof b @i))
                 (lambda (l) (if (null? l) nil (cons (f (car l)) (loop (cdr l)))))))
        (loop l)))))

;; ---- RegisterFile

(define* init-register-file (subr (maxeff (read @i) (alloc @i) spin) () words)
  (lambda ()
    (let ((upd (proj ia-update u32)))
      (upd (upd (upd (upd ((proj ia-tabulate u32) 32 (lambda (i) (int->u32 0)))
                          0 (int->u32 0))
                     28 (int->u32 0))
                29 (int->u32 262144))
           30 (int->u32 262144)))))

(define* load-register (subr (maxeff (read @i) spin) (words int) u32)
  (lambda (rf reg) ((proj ia-nth u32) rf reg)))

(define* store-register (subr (maxeff (read @i) (alloc @i) spin) (words int u32) words)
  (lambda (rf reg data) ((proj ia-update u32) rf reg data)))

;; ---- ALU

(define-datatype aluop
  (A-SLL) (A-SRL) (A-SRA) (A-ADD) (A-ADDU) (A-SUB) (A-SUBU) (A-AND) (A-OR) (A-XOR)
  (A-SEQ) (A-SNE) (A-SLT) (A-SGT) (A-SLE) (A-SGE))

;; The ALU's handler: "Error : ALU returning 0".
(define* alu-error (subr (maxeff (read @o) (write @o) spin) () u32)
  (lambda () (begin (print-string "Error : ALU returning 0\n") (int->u32 0))))

;; Int.+ and Int.- on MLton's 32-bit Int: outside it, Overflow, which the
;; ALU handles.
(define* int32 (subr (maxeff (read @o) (write @o) spin) (int) u32)
  (lambda (n) (if (and (>= n -2147483648) (< n 2147483648)) (int->u32 n) (alu-error))))

(define* flag (subr pure (bool) u32) (lambda (b) (if b (int->u32 1) (int->u32 0))))

(define* perform-al (subr (maxeff (read @o) (write @o) spin) (aluop u32 u32) u32)
  (lambda (opcode s1 s2)
    (tagcase opcode
      (A-SLL () (shl s1 (word-toint s2)))
      (A-SRL () (shr s1 (word-toint s2)))
      (A-SRA () (ashr s1 (word-toint s2)))
      (A-ADD () (int32 (+ (to-intx s1) (to-intx s2))))
      (A-ADDU () (u32+ s1 s2))
      (A-SUB () (int32 (- (to-intx s1) (to-intx s2))))
      (A-SUBU () (u32- s1 s2))
      (A-AND () (u32-and s1 s2))
      (A-OR () (u32-or s1 s2))
      (A-XOR () (u32-xor s1 s2))
      (A-SEQ () (flag (u32= s1 s2)))
      (A-SNE () (flag (not (u32= s1 s2))))
      (A-SLT () (flag (< (to-intx s1) (to-intx s2))))
      (A-SGT () (flag (> (to-intx s1) (to-intx s2))))
      (A-SLE () (flag (<= (to-intx s1) (to-intx s2))))
      (A-SGE () (flag (>= (to-intx s1) (to-intx s2)))))))

;; ---- Memory: its words, and counts of reads and writes.

(define-type memory (productof (words words) (reads int) (writes int)))
(define-type mem-word (productof (mem memory) (word u32)))

(define* mem-init (subr (maxeff (alloc @i) spin) () memory)
  (lambda ()
    (product (words ((proj ia-tabulate u32) (u32->int (int->u32 65536)) (lambda (i) (int->u32 0))))
             (reads 0) (writes 0))))

(define* align-w-address (subr pure (u32) u32) (lambda (a) (shl (shr a 2) 2)))
(define* align-hw-address (subr pure (u32) u32) (lambda (a) (shl (shr a 1) 1)))

;; Load and Store: errorless access to memory.
(define* mem-load (subr (maxeff (read @i) spin) (memory u32) mem-word)
  (lambda (m address)
    (let* ((aligned-address (align-w-address address))
           (use-address (shr aligned-address 2)))
      (product (mem (product (words (extract m words)) (reads (+ (extract m reads) 1))
                             (writes (extract m writes))))
               (word ((proj ia-nth u32) (extract m words) (u32->int use-address)))))))

(define* mem-store (subr (maxeff (read @i) (alloc @i) spin) (memory u32 u32) memory)
  (lambda (m address data)
    (let* ((aligned-address (align-w-address address))
           (use-address (shr aligned-address 2)))
      (product (words ((proj ia-update u32) (extract m words) (u32->int use-address) data))
               (reads (extract m reads)) (writes (+ (extract m writes) 1))))))

(define* mem-load-word (subr (maxeff (read @i) (read @o) (write @o) spin) (memory u32) mem-word)
  (lambda (m address)
    (mem-load m (if (u32= address (align-w-address address))
                    address
                    (begin (print-string "Error LW: Memory using aligned address\n")
                           (align-w-address address))))))

(define* mem-store-word
  (subr (maxeff (read @i) (alloc @i) (read @o) (write @o) spin) (memory u32 u32) memory)
  (lambda (m address data)
    (mem-store m (if (u32= address (align-w-address address))
                     address
                     (begin (print-string "Error SW: Memory using aligned address\n")
                            (align-w-address address)))
               data)))

(define* mem-statistics (subr spin (memory) string)
  (lambda (m)
    (concat (list "Memory :\n"
                  "Memory Reads : " (int-to-string (extract m reads)) "\n"
                  "Memory Writes : " (int-to-string (extract m writes)) "\n"))))

;; ---- L1CacheSpec1: a small level 1 cache.

(define-datatype write-hit-option (Write_Through) (Write_Back))
(define-datatype write-miss-option (Write_Allocate) (Write_No_Allocate))

(define CacheName string "Level 1 Cache")
(define CacheSize int 256)
(define BlockSize int 4)
(define Associativity int 2)
(define WriteHit write-hit-option (Write_Through))
(define WriteMiss write-miss-option (Write_No_Allocate))

;; ---- CachedMemory (structure CS = L1CacheSpec1; structure MEM = Memory)

(define-type cacheline (productof (valid bool) (dirty bool) (tag u32) (block words)))
(define-type cacheset (listof cacheline @i))
(define-type cache (listof cacheset @i))
(define-type cmemory
  (productof (cac cache) (rh int) (rm int) (wh int) (wm int) (mem memory)))
(define-type cmem-word (productof (mem cmemory) (word u32)))

;; Performs log[base2] on an integer.
(define* exp2 (subr spin (int) int) (lambda (n) (if (= n 0) 1 (* 2 (exp2 (- n 1))))))
(define* log2 (subr spin (int) int)
  (lambda (x)
    (letrec ((log2-aux (subr (maxeff spin (read (globals exp2))) (int) int)
               (lambda (n) (if (> (exp2 n) x) (- n 1) (log2-aux (+ n 1))))))
      (log2-aux 0))))

(define IndexSize int (quotient CacheSize (* BlockSize Associativity)))
(define BlockOffsetBits int (log2 (* BlockSize 4)))
(define IndexBits int (log2 IndexSize))
(define TagBits int (- (- 32 BlockOffsetBits) IndexBits))

;; RandEntry: a random number in [0, Associativity - 1], by Word.mod.
(define* rand-entry (subr (maxeff (read @o) (write @o)) () int)
  (lambda ()
    (let ((modulus (int->u32 (- Associativity 1))))
      (u32->int (u32-remainder (rand) modulus)))))

(define* zero-block (subr (maxeff (alloc @i) spin) () words)
  (lambda () ((proj ia-tabulate u32) BlockSize (lambda (i) (int->u32 0)))))

(define* init-cache (subr (maxeff (alloc @i) spin) () cache)
  (lambda ()
    (let* ((cacheline (product (valid #f) (dirty #f) (tag (int->u32 0)) (block (zero-block))))
           (cacheset ((proj ia-tabulate cacheline) Associativity (lambda (i) cacheline))))
      ((proj ia-tabulate cacheset) IndexSize (lambda (i) cacheset)))))

(define* c-init (subr (maxeff (alloc @i) spin) () cmemory)
  (lambda ()
    (product (cac (init-cache)) (rh 0) (rm 0) (wh 0) (wm 0) (mem (mem-init)))))

(define* get-tag (subr pure (u32) u32)
  (lambda (address) (shr address (+ IndexBits BlockOffsetBits))))

(define* get-index (subr pure (u32) u32)
  (lambda (address)
    (let* ((bits (+ IndexBits BlockOffsetBits))
           (mask (u32-not (shl (shr (int->u32 4294967295) bits) bits))))
      (shr (u32-and address mask) BlockOffsetBits))))

(define* get-block-offset (subr pure (u32) u32)
  (lambda (address)
    (let ((mask (u32-not (shl (shr (int->u32 4294967295) BlockOffsetBits) BlockOffsetBits))))
      (u32-and address mask))))

;; InCache: whether the word at address is in the cache, and valid.
(define* c-in-entry (subr pure (cacheline u32) bool)
  (lambda (entry address) (and (u32= (extract entry tag) (get-tag address)) (extract entry valid))))

(define* c-in-set (subr cb (cacheset u32) bool)
  (lambda (set address)
    ((proj ia-foldr cacheline bool)
     (lambda (entry result) (or (c-in-entry entry address) result)) #f set)))

(define* c-in-cache (subr cb (cache u32) bool)
  (lambda (cac address)
    (c-in-set ((proj ia-nth cacheset) cac (u32->int (get-index address))) address)))

;; ReadCache: the word at address in the cache.
(define* c-read-entry (subr (maxeff (read @i) spin) (cacheline u32) u32)
  (lambda (entry address)
    ((proj ia-nth u32) (extract entry block) (u32->int (shr (get-block-offset address) 2)))))

(define* c-read-set (subr cb (cacheset u32) u32)
  (lambda (set address)
    ((proj ia-foldr cacheline u32)
     (lambda (entry result)
       (if (c-in-entry entry address) (c-read-entry entry address) result))
     (int->u32 0) set)))

(define* c-read-cache (subr cb (cache u32) u32)
  (lambda (cac address)
    (c-read-set ((proj ia-nth cacheset) cac (u32->int (get-index address))) address)))

;; WriteCache: the cache with data stored at address.
(define* c-write-entry (subr (maxeff (read @i) (alloc @i) spin) (cacheline u32 u32) cacheline)
  (lambda (entry address data)
    (let ((ndirty (tagcase WriteHit (Write_Through () #f) (Write_Back () #t))))
      (product (valid #t) (dirty ndirty) (tag (extract entry tag))
               (block ((proj ia-update u32) (extract entry block)
                                            (u32->int (shr (get-block-offset address) 2))
                                            data))))))

(define* c-write-set (subr cb (cacheset u32 u32) cacheset)
  (lambda (set address data)
    ((proj ia-map cacheline cacheline)
     (lambda (entry)
       (if (c-in-entry entry address) (c-write-entry entry address data) entry))
     set)))

(define* c-write-cache (subr cb (cache u32 u32) cache)
  (lambda (cac address data)
    (let* ((index (u32->int (get-index address)))
           (nset (c-write-set ((proj ia-nth cacheset) cac index) address data)))
      ((proj ia-update cacheset) cac index nset))))

;; The address of word `offset` of the block holding address.
(define* block-address (subr pure (u32 int) u32)
  (lambda (address offset)
    (u32+ (shl (shr address BlockOffsetBits) BlockOffsetBits) (shl (int->u32 offset) 2))))

(define-type block-mem (productof (block words) (mem memory)))

;; LoadBlock: memory, and the block holding address loaded from it.
(define* load-block (subr cb (memory u32) block-mem)
  (lambda (mem address)
    ((proj ia-foldr int block-mem)
     (lambda (offset acc)
       (let* ((r (mem-load-word (extract acc mem) (block-address address offset))))
         (product (block ((proj ia-update u32) (extract acc block) offset (extract r word)))
                  (mem (extract r mem)))))
     (product (block (zero-block)) (mem mem))
     ((proj ia-tabulate int) BlockSize (lambda (i) i)))))

;; StoreBlock: memory with block stored into the block holding address.
(define* store-block (subr cb (words memory u32) memory)
  (lambda (block mem address)
    ((proj ia-foldr int memory)
     (lambda (offset mem)
       (mem-store-word mem (block-address address offset) ((proj ia-nth u32) block offset)))
     mem
     ((proj ia-tabulate int) BlockSize (lambda (i) i)))))

(define-type line-mem (productof (line cacheline) (mem memory)))
(define-type set-mem (productof (set cacheset) (mem memory)))
(define-type cache-mem (productof (cac cache) (mem memory)))

;; LoadCache: the cache and memory, the block holding address loaded into
;; the cache, and dirty data written back to memory first.
(define* c-load-entry (subr cb (cacheline memory u32) line-mem)
  (lambda (entry mem address)
    (let* ((saddress (u32-or (shl (extract entry tag) TagBits)
                             (shl (get-index address) IndexBits)))
           (nmem (if (and (extract entry valid) (extract entry dirty))
                     (store-block (extract entry block) mem saddress)
                     mem))
           (r (load-block nmem address)))
      (product (line (product (valid #t) (dirty #f) (tag (get-tag address))
                              (block (extract r block))))
               (mem (extract r mem))))))

(define* c-load-set (subr cb (cacheset memory u32) set-mem)
  (lambda (set mem address)
    (let* ((entry (rand-entry))
           (r (c-load-entry ((proj ia-nth cacheline) set entry) mem address))
           (nset ((proj ia-update cacheline) set entry (extract r line))))
      (product (set nset) (mem (extract r mem))))))

(define* c-load-cache (subr cb (cache memory u32) cache-mem)
  (lambda (cac mem address)
    (let* ((index (u32->int (get-index address)))
           (r (c-load-set ((proj ia-nth cacheset) cac index) mem address)))
      (product (cac ((proj ia-update cacheset) cac index (extract r set))) (mem (extract r mem))))))

;; A cached memory of a cache, counts and memory.
(define* cmem (subr pure (cache int int int int memory) cmemory)
  (lambda (cac rh rm wh wm mem) (product (cac cac) (rh rh) (rm rm) (wh wh) (wm wm) (mem mem))))

;; Load and Store: errorless access to the cached memory.
(define* c-load (subr cb (cmemory u32) cmem-word)
  (lambda (m address)
    (let ((aligned-address (align-w-address address))
          (cac (extract m cac)) (rh (extract m rh)) (rm (extract m rm))
          (wh (extract m wh)) (wm (extract m wm)) (mem (extract m mem)))
      (if (c-in-cache cac aligned-address)
          (product (mem (cmem cac (+ rh 1) rm wh wm mem))
                   (word (c-read-cache cac aligned-address)))
          (let ((r (c-load-cache cac mem aligned-address)))
            (product (mem (cmem (extract r cac) rh (+ rm 1) wh wm (extract r mem)))
                     (word (c-read-cache (extract r cac) aligned-address))))))))

(define* c-store (subr cb (cmemory u32 u32) cmemory)
  (lambda (m address data)
    (let ((aligned-address (align-w-address address))
          (cac (extract m cac)) (rh (extract m rh)) (rm (extract m rm))
          (wh (extract m wh)) (wm (extract m wm)) (mem (extract m mem)))
      (if (c-in-cache cac aligned-address)
          (let ((ncac (c-write-cache cac aligned-address data)))
            (tagcase WriteHit
              (Write_Through ()
                (cmem ncac rh rm (+ wh 1) wm (mem-store-word mem aligned-address data)))
              (Write_Back () (cmem ncac rh rm (+ wh 1) wm mem))))
          (tagcase WriteMiss
            (Write_Allocate ()
              (let* ((r (c-load-cache cac mem aligned-address))
                     (nncac (c-write-cache (extract r cac) aligned-address data)))
                (tagcase WriteHit
                  (Write_Through ()
                    (cmem nncac rh rm wh (+ wm 1)
                          (mem-store-word (extract r mem) aligned-address data)))
                  (Write_Back () (cmem nncac rh rm wh (+ wm 1) (extract r mem))))))
            (Write_No_Allocate ()
              (cmem cac rh rm wh (+ wm 1) (mem-store-word mem aligned-address data))))))))

(define* c-load-word (subr cb (cmemory u32) cmem-word)
  (lambda (m address)
    (c-load m (if (u32= address (align-w-address address))
                  address
                  (begin (print-string "Error LW: Memory using aligned address\n")
                         (align-w-address address))))))

(define* c-store-word (subr cb (cmemory u32 u32) cmemory)
  (lambda (m address data)
    (c-store m (if (u32= address (align-w-address address))
                   address
                   (begin (print-string "Error SW: Memory using aligned address\n")
                          (align-w-address address)))
             data)))

;; "Error LH: Memory returning 0", and the like.
(define* memory-error (subr (maxeff (read @o) (write @o) spin) (string string) unit)
  (lambda (name what) (print-string (concat (list "Error " name ": Memory " what "\n")))))

;; LoadHWord and LoadHWordU: `signed` says which; `name`, for errors.
(define* c-load-hword-of (subr cb (cmemory u32 bool string) cmem-word)
  (lambda (m address signed name)
    (let* ((aligned-address
            (if (u32= address (align-hw-address address))
                address
                (begin (memory-error name "using aligned address")
                       (align-hw-address address))))
           (r (c-load m aligned-address))
           (l-word (extract r word))
           (a (u32->int aligned-address)))
      (product (mem (extract r mem))
               (word (cond ((= a 0) (if signed (ashr (shl l-word 16) 16) (shr (shl l-word 16) 16)))
                           ((= a 16) (if signed (ashr (shl l-word 0) 16) (shr (shl l-word 0) 16)))
                           (else (begin (memory-error name "returning 0")
                                        (int->u32 0)))))))))

;; LoadByte and LoadByteU.
(define* c-load-byte-of (subr cb (cmemory u32 bool string) cmem-word)
  (lambda (m address signed name)
    (let* ((r (c-load m address))
           (l-word (extract r word))
           (a (u32->int address))
           (byte (lambda ((s int)) (if signed (ashr (shl l-word s) 24) (shr (shl l-word s) 24)))))
      (product (mem (extract r mem))
               (word (cond ((= a 0) (byte 24))
                           ((= a 8) (byte 16))
                           ((= a 16) (byte 8))
                           ((= a 24) (byte 0))
                           (else (begin (memory-error name "returning 0")
                                        (int->u32 0)))))))))

;; StoreByte: the memory Load gives is dropped, as the original's is.
(define* c-store-byte (subr cb (cmemory u32 u32) cmemory)
  (lambda (m address data)
    (let* ((s-word (extract (c-load m address) word))
           (a (u32->int address))
           (put (lambda ((mask int) (s int))
                  (c-store m address (u32-or (u32-and (int->u32 mask) s-word)
                                             (shl (u32-and (int->u32 255) data) s))))))
      (cond ((= a 0) (put 4294967040 0))
            ((= a 8) (put 4294902015 8))
            ((= a 16) (put 4278255615 16))
            ((= a 24) (put 16777215 24))
            (else (begin (print-string "Error SB: Memory unchanged\n") m))))))

(define* c-statistics (subr spin (cmemory) string)
  (lambda (m)
    (let* ((rh (extract m rh)) (rm (extract m rm)) (wh (extract m wh)) (wm (extract m wm))
           (th (+ rh wh))
           (tm (+ rm wm))
           (who (tagcase WriteHit (Write_Through () "Write Through") (Write_Back () "Write Back")))
           (wmo (tagcase WriteMiss
                  (Write_Allocate () "Write Allocate")
                  (Write_No_Allocate () "Write No Allocate"))))
      (concat (list CacheName " :\n"
                    "CacheSize : " (int-to-string CacheSize) "\n"
                    "BlockSize : " (int-to-string BlockSize) "\n"
                    "Associativity : " (int-to-string Associativity) "\n"
                    "Write Hit : " who "\n"
                    "Write Miss : " wmo "\n"
                    "Read hits : " (int-to-string rh) "\n"
                    "Read misses : " (int-to-string rm) "\n"
                    "Write hits : " (int-to-string wh) "\n"
                    "Write misses : " (int-to-string wm) "\n"
                    "Total hits : " (int-to-string th) "\n"
                    "Total misses : " (int-to-string tm) "\n"
                    (mem-statistics (extract m mem)))))))

;; ---- DLXSimulatorFun (structure RF = RegisterFile; structure ALU = ALU;
;; ---- structure MEM = L1Cache1)

(define-datatype opcode
  (SPECIAL)
  (BEQZ) (BNEZ) (ADDI) (ADDUI) (SUBI) (SUBUI) (ANDI) (ORI) (XORI) (LHI) (SLLI) (SRLI) (SRAI)
  (SEQI) (SNEI) (SLTI) (SGTI) (SLEI) (SGEI) (LB) (LBU) (SB) (LH) (LHU) (SH) (LW) (SW)
  (J) (JAL) (TRAP) (JR) (JALR)
  (NON_OP))

(define-datatype rr-funct-code
  (NOP) (SLL) (SRL) (SRA) (ADD) (ADDU) (SUB) (SUBU) (AND) (OR) (XOR)
  (SEQ) (SNE) (SLT) (SGT) (SLE) (SGE) (NON_FUNCT))

;; An I-type is (opcode, rs1, rd, immediate), an R-type (opcode, rs1, rs2,
;; rd, shamt, funct), a J-type (opcode, offset); an ILLEGAL ends the run.
(define-datatype instruction
  (ITYPE opcode int int u32)
  (RTYPE opcode int int int int rr-funct-code)
  (JTYPE opcode u32)
  (ILLEGAL))

;; The trap's state, the benchmark's: the inputs left, the outputs made.
(define-type tstate (productof (inputs ints) (outputs ints)))
(define-type input-state (productof (input int) (state tstate)))
(define-type trap
  (productof (input-fn (subr cb (tstate) input-state))
             (output-fn (subr cb (int tstate) tstate))
             (state tstate)))

;; (PC, rf, mem, trap)
(define-type machine (productof (pc u32) (rf words) (mem cmemory) (trap trap)))

(define* machine-of (subr pure (u32 words cmemory trap) machine)
  (lambda (pc rf mem trap) (product (pc pc) (rf rf) (mem mem) (trap trap))))

;; Bits `at` and up of instr, masked.
(define* field (subr pure (u32 int int) u32)
  (lambda (instr at mask) (u32-and (shr instr at) (int->u32 mask))))

(define* i-opcode (subr (maxeff (read @o) (write @o) spin) (int) opcode)
  (lambda (opc)
    (cond ((= opc 4) (BEQZ)) ((= opc 5) (BNEZ)) ((= opc 8) (ADDI)) ((= opc 9) (ADDUI))
          ((= opc 10) (SUBI)) ((= opc 11) (SUBUI)) ((= opc 12) (ANDI)) ((= opc 13) (ORI))
          ((= opc 14) (XORI)) ((= opc 15) (LHI)) ((= opc 20) (SLLI)) ((= opc 22) (SRLI))
          ((= opc 23) (SRAI)) ((= opc 24) (SEQI)) ((= opc 25) (SNEI)) ((= opc 26) (SLTI))
          ((= opc 27) (SGTI)) ((= opc 28) (SLEI)) ((= opc 29) (SGEI)) ((= opc 32) (LB))
          ((= opc 36) (LBU)) ((= opc 40) (SB)) ((= opc 33) (LH)) ((= opc 37) (LHU))
          ((= opc 41) (SH)) ((= opc 35) (LW)) ((= opc 43) (SW))
          (else (begin (print-string "Error : Non I-Type opcode\n") (NON_OP))))))

(define* decode-i-type (subr (maxeff (read @o) (write @o) spin) (u32) instruction)
  (lambda (instr)
    (let ((opcode (i-opcode (u32->int (field instr 26 63))))
          (rs1 (u32->int (field instr 21 31)))
          (rd (u32->int (field instr 16 31)))
          (immediate (ashr (shl instr 16) 16)))
      (tagcase opcode
        (NON_OP () (ILLEGAL))
        (else o (ITYPE opcode rs1 rd immediate))))))

(define* r-funct (subr (maxeff (read @o) (write @o) spin) (int) rr-funct-code)
  (lambda (funct)
    (cond ((= funct 0) (NOP)) ((= funct 4) (SLL)) ((= funct 6) (SRL)) ((= funct 7) (SRA))
          ((= funct 32) (ADD)) ((= funct 33) (ADDU)) ((= funct 34) (SUB)) ((= funct 35) (SUBU))
          ((= funct 36) (AND)) ((= funct 37) (OR)) ((= funct 38) (XOR)) ((= funct 40) (SEQ))
          ((= funct 41) (SNE)) ((= funct 42) (SLT)) ((= funct 43) (SGT)) ((= funct 44) (SLE))
          ((= funct 45) (SGE))
          (else (begin (print-string "Error : Non R-type funct\n") (NON_FUNCT))))))

(define* decode-r-type (subr (maxeff (read @o) (write @o) spin) (u32) instruction)
  (lambda (instr)
    (let ((rs1 (u32->int (field instr 21 31)))
          (rs2 (u32->int (field instr 16 31)))
          (rd (u32->int (field instr 11 31)))
          (shamt (u32->int (field instr 6 31)))
          (functcode (r-funct (u32->int (u32-and instr (int->u32 63))))))
      (tagcase functcode
        (NON_FUNCT () (ILLEGAL))
        (else o (RTYPE (SPECIAL) rs1 rs2 rd shamt functcode))))))

(define* decode-j-type (subr (maxeff (read @o) (write @o) spin) (u32) instruction)
  (lambda (instr)
    (let* ((opc (u32->int (field instr 26 63)))
           (opcode (cond ((= opc 2) (J)) ((= opc 3) (JAL)) ((= opc 17) (TRAP)) ((= opc 18) (JR))
                         ((= opc 19) (JALR))
                         (else (begin (print-string "Error : Non J-type opcode\n") (NON_OP)))))
           (offset (ashr (shl instr 6) 6)))
      (tagcase opcode
        (NON_OP () (ILLEGAL))
        (else o (JTYPE opcode offset))))))

(define* decode-instr (subr (maxeff (read @o) (write @o) spin) (u32) instruction)
  (lambda (instr)
    (let ((opcode (u32->int (field instr 26 63))))
      (cond ((= opcode 0) (decode-r-type instr))
            ((or (= opcode 2) (= opcode 3) (= opcode 17) (= opcode 18) (= opcode 19))
             (decode-j-type instr))
            ((or (= opcode 4) (= opcode 5) (and (>= opcode 8) (<= opcode 15))
                 (and (>= opcode 22) (<= opcode 29))
                 (= opcode 32) (= opcode 36) (= opcode 40) (= opcode 33) (= opcode 37)
                 (= opcode 41) (= opcode 35) (= opcode 43))
             (decode-i-type instr))
            (else (begin (print-string "Error : Unrecognized opcode\n") (ILLEGAL)))))))

;; Word32.fromInt (Int.+ (Word32.toIntX PC, Word32.toIntX (<< (offset, 0w2)))).
(define* branch-target (subr pure (u32 u32) u32)
  (lambda (pc offset) (int->u32 (+ (to-intx pc) (to-intx (shl offset 2))))))

;; An I-type instruction of the ALU: rd := rs1 op immediate.
(define* perform-alu-i (subr cb (aluop int int u32 machine) machine)
  (lambda (op rs1 rd immediate m)
    (let ((rf (extract m rf)))
      (machine-of (extract m pc)
                  (store-register rf rd (perform-al op (load-register rf rs1) immediate))
                  (extract m mem) (extract m trap)))))

;; A load, of MEM's `load`, into rd.
(define-type loader (subr cb (cmemory u32) cmem-word))
(define* perform-load (subr cb (loader int int u32 machine) machine)
  (lambda (load rs1 rd immediate m)
    (let* ((rf (extract m rf))
           (r (load (extract m mem) (u32+ (load-register rf rs1) immediate))))
      (machine-of (extract m pc) (store-register rf rd (extract r word)) (extract r mem)
                  (extract m trap)))))

;; A store, of MEM's `store`, of rd masked.
(define-type storer (subr cb (cmemory u32 u32) cmemory))
(define* perform-store (subr cb (storer int int u32 u32 machine) machine)
  (lambda (store rs1 rd immediate mask m)
    (let ((rf (extract m rf)))
      (machine-of (extract m pc) rf
                  (store (extract m mem) (u32+ (load-register rf rs1) immediate)
                         (u32-and mask (load-register rf rd)))
                  (extract m trap)))))

;; An I-type shift of rs1 by the immediate, into rd.
(define* perform-shift-i (subr cb ((subr pure (u32 int) u32) int int u32 machine) machine)
  (lambda (shift rs1 rd immediate m)
    (let ((rf (extract m rf)))
      (machine-of (extract m pc)
                  (store-register rf rd (shift (load-register rf rs1) (word-toint immediate)))
                  (extract m mem) (extract m trap)))))

(define* perform-branch (subr cb (bool int u32 machine) machine)
  (lambda (if-zero rs1 immediate m)
    (let ((pc (extract m pc)) (rf (extract m rf)))
      (if (let ((zero (u32= (load-register rf rs1) (int->u32 0)))) (if if-zero zero (not zero)))
          (machine-of (branch-target pc immediate) rf (extract m mem) (extract m trap))
          m))))

(define* perform-i-type (subr cb (opcode int int u32 machine) machine)
  (lambda (opcode rs1 rd immediate m)
    (let ((all-bits (int->u32 4294967295)))
      (tagcase opcode
        (BEQZ () (perform-branch #t rs1 immediate m))
        (BNEZ () (perform-branch #f rs1 immediate m))
        (ADDI () (perform-alu-i (A-ADD) rs1 rd immediate m))
        (ADDUI () (perform-alu-i (A-ADDU) rs1 rd immediate m))
        (SUBI () (perform-alu-i (A-SUB) rs1 rd immediate m))
        (SUBUI () (perform-alu-i (A-SUBU) rs1 rd immediate m))
        (ANDI () (perform-alu-i (A-AND) rs1 rd immediate m))
        (ORI () (perform-alu-i (A-OR) rs1 rd immediate m))
        (XORI () (perform-alu-i (A-XOR) rs1 rd immediate m))
        (LHI () (machine-of (extract m pc) (store-register (extract m rf) rd (shl immediate 16))
                            (extract m mem) (extract m trap)))
        (SLLI () (perform-shift-i shl rs1 rd immediate m))
        (SRLI () (perform-shift-i shr rs1 rd immediate m))
        (SRAI () (perform-shift-i ashr rs1 rd immediate m))
        (SEQI () (perform-alu-i (A-SEQ) rs1 rd immediate m))
        (SNEI () (perform-alu-i (A-SNE) rs1 rd immediate m))
        (SLTI () (perform-alu-i (A-SLT) rs1 rd immediate m))
        (SGTI () (perform-alu-i (A-SGT) rs1 rd immediate m))
        (SLEI () (perform-alu-i (A-SLE) rs1 rd immediate m))
        (SGEI () (perform-alu-i (A-SGE) rs1 rd immediate m))
        (LB () (perform-load (lambda (mem a) (c-load-byte-of mem a #t "LB")) rs1 rd immediate m))
        (LBU () (perform-load (lambda (mem a) (c-load-byte-of mem a #f "LBU")) rs1 rd immediate m))
        (SB () (perform-store c-store-byte rs1 rd immediate (int->u32 255) m))
        (LH () (perform-load (lambda (mem a) (c-load-hword-of mem a #t "LH")) rs1 rd immediate m))
        (LHU () (perform-load (lambda (mem a) (c-load-hword-of mem a #f "LHU")) rs1 rd immediate m))
        ;; SH stores with StoreByte, as the original's does.
        (SH () (perform-store c-store-byte rs1 rd immediate (int->u32 65535) m))
        (LW () (perform-load c-load-word rs1 rd immediate m))
        (SW () (perform-store c-store-word rs1 rd immediate all-bits m))
        (else o (begin (print-string "Error : Non I-Type opcode, performing NOP\n") m))))))

(define* perform-r-type (subr cb (int int int rr-funct-code machine) machine)
  (lambda (rs1 rs2 rd funct m)
    (let* ((rf (extract m rf))
           (al (lambda ((op aluop))
                 (machine-of (extract m pc)
                             (store-register rf rd (perform-al op (load-register rf rs1)
                                                               (load-register rf rs2)))
                             (extract m mem) (extract m trap)))))
      (tagcase funct
        (NOP () m)
        (SLL () (al (A-SLL))) (SRL () (al (A-SRL))) (SRA () (al (A-SRA)))
        (ADD () (al (A-ADD))) (ADDU () (al (A-ADDU))) (SUB () (al (A-SUB)))
        (SUBU () (al (A-SUBU))) (AND () (al (A-AND))) (OR () (al (A-OR)))
        (XOR () (al (A-XOR))) (SEQ () (al (A-SEQ))) (SNE () (al (A-SNE)))
        (SLT () (al (A-SLT))) (SGT () (al (A-SGT))) (SLE () (al (A-SLE)))
        (SGE () (al (A-SGE)))
        (else o (begin (print-string "Error : Non R-Type opcode, performing NOP\n") m))))))

;; The register a JR or JALR names, in bits 21 to 25.
(define* jump-register (subr pure (u32) int) (lambda (offset) (u32->int (field offset 21 31))))

(define* perform-trap (subr cb (u32 machine) machine)
  (lambda (offset m)
    (let* ((pc (extract m pc)) (rf (extract m rf)) (mem (extract m mem))
           (trap (extract m trap)) (code (u32->int offset))
           (with-state (lambda ((state tstate))
                         (product (input-fn (extract trap input-fn))
                                  (output-fn (extract trap output-fn))
                                  (state state)))))
      (cond ((= code 3)
             (let ((r ((extract trap input-fn) (extract trap state))))
               (machine-of pc (store-register rf 14 (int->u32 (extract r input))) mem
                           (with-state (extract r state)))))
            ((= code 4)
             (let* ((output (to-intx (load-register rf 14)))
                    (state ((extract trap output-fn) output (extract trap state))))
               (machine-of pc rf mem (with-state state))))
            (else (begin (print-string "Error : Non J-Type opcode, performing NOP\n") m))))))

(define* perform-j-type (subr cb (opcode u32 machine) machine)
  (lambda (opcode offset m)
    (let ((pc (extract m pc)) (rf (extract m rf)) (mem (extract m mem)) (trap (extract m trap)))
      (tagcase opcode
        (J () (machine-of (branch-target pc offset) rf mem trap))
        (JR () (machine-of (load-register rf (jump-register offset)) rf mem trap))
        (JAL () (machine-of (branch-target pc offset) (store-register rf 31 pc) mem trap))
        (JALR () (machine-of (load-register rf (jump-register offset)) (store-register rf 31 pc)
                             mem trap))
        (TRAP () (perform-trap offset m))
        (else o (begin (print-string "Error : Non J-Type opcode, performing NOP\n") m))))))

(define* perform-instr (subr cb (instruction machine) machine)
  (lambda (instr m)
    (tagcase instr
      (ITYPE (op rs1 rd immediate) (perform-i-type op rs1 rd immediate m))
      (RTYPE (op rs1 rs2 rd shamt funct) (perform-r-type rs1 rs2 rd funct m))
      (JTYPE (op offset) (perform-j-type op offset m))
      (ILLEGAL () m))))

;; HALT is TRAP #0.
(define* halt-or-illegal? (subr pure (instruction) bool)
  (lambda (instr)
    (tagcase instr
      (JTYPE (op offset) (tagcase op (TRAP () (u32= offset (int->u32 0))) (else o #f)))
      (ILLEGAL () #t)
      (else o #f))))

(define-type statistics (subr cb () string))
(define-type result (productof (statistics statistics) (state tstate)))

;; The clock cycle: load, decode and perform an instruction, until HALT.
(define* cycle-loop (subr cb (machine) result)
  (lambda (m)
    (let* ((r (c-load-word (extract m mem) (extract m pc)))
           (nmem (extract r mem))
           (instr (decode-instr (extract r word)))
           (npc (u32+ (extract m pc) (int->u32 4))))
      (if (halt-or-illegal? instr)
          (product (statistics (lambda () (c-statistics nmem)))
                   (state (extract (extract m trap) state)))
          (cycle-loop
           (perform-instr instr (machine-of npc (extract m rf) nmem (extract m trap))))))))

(define-type strings (listof string acyclic))

(define* invalid-instruction (subr (maxeff (read @o) (write @o) spin) () u32)
  (lambda ()
    (begin (print-string "Error : Invalid instruction format, returning NOP\n")
           (int->u32 0))))

;; LoadProg: the program's words into memory, from 0x10000 on.
(define* load-prog-aux (subr cb (strings cmemory u32) cmemory)
  (lambda (instrs mem address)
    (if (null? instrs)
        mem
        (let ((instr (tagcase (from-string (car instrs))
                       (SOME (w) w)
                       (NONE () (invalid-instruction))))
              (next (u32+ address (int->u32 4))))
          (load-prog-aux (cdr instrs) (c-store-word mem address instr) next)))))

(define* run-prog (subr cb (strings trap) result)
  (lambda (instructions trap)
    (cycle-loop (machine-of (int->u32 65536) (init-register-file)
                            (load-prog-aux instructions (c-init) (int->u32 65536))
                            trap))))

;; ---- The example programs

(define Simple strings (list "200E002F" "44000004" "44000000" "00000000"))

(define Twos strings
  (list "44000003" "00000000" "3D00FFFF" "3508FFFF" "010E7026" "25CE0001" "44000004"
        "00000000" "44000000" "00000000"))

(define Abs strings
  (list "44000003" "00000000" "01C0402A" "11000002" "00000000" "000E7022" "44000004"
        "00000000" "44000000" "00000000"))

(define Fact strings
  (list "0C000002" "00000000" "44000000" "44000003" "000E2020" "2FBD0020" "AFBF0014"
        "AFBE0010" "27BE0020" "0C000009" "00000000" "8FBE0010" "8FBF0014" "27BD0020"
        "00027020" "44000004" "00001020" "4BE00000" "00000000" "20080001" "0088402C"
        "11000004" "00000000" "20020001" "08000016" "00000000" "2FBD0004" "AFA40000"
        "28840001" "2FBD0020" "AFBF0014" "AFBE0010" "27BE0020" "0FFFFFF1" "00000000"
        "8FBE0010" "8FBF0014" "27BD0020" "8FA40000" "27BD0004" "00004020" "10800005"
        "00000000" "01024020" "28840001" "0BFFFFFB" "00000000" "01001020" "4BE00000"
        "00000000"))

(define GCD strings
  (list "0C000002" "00000000" "44000000" "44000003" "00000000" "000E2020" "0080402A"
        "11000002" "00000000" "00042022" "44000003" "00000000" "000E2820" "00A0402A"
        "11000002" "00000000" "00052822" "2FBD0020" "AFBF0014" "AFBE0010" "27BE0020"
        "0C00000A" "00000000" "8FBE0010" "8FBF0014" "27BD0020" "00027020" "44000004"
        "00000000" "00001020" "4BE00000" "00000000" "14A00004" "00000000" "00801020"
        "08000013" "00000000" "0085402C" "15000006" "00000000" "00804020" "00A02020"
        "01002820" "08000002" "00000000" "00A42822" "2FBD0020" "AFBF0014" "AFBE0010"
        "27BE0020" "0FFFFFED" "00000000" "8FBE0010" "8FBF0014" "27BD0020" "4BE00000"
        "00000000"))

;; ---- structure Main

(define* tstate-of (subr pure (ints ints) tstate)
  (lambda (inputs outputs) (product (inputs inputs) (outputs outputs))))

(define* input-fn (subr (read @i) (tstate) input-state)
  (lambda (state)
    (let ((inputs (extract state inputs)) (outputs (extract state outputs)))
      (if (null? inputs)
          (product (input 0) (state (tstate-of nil outputs)))
          (product (input (car inputs)) (state (tstate-of (cdr inputs) outputs)))))))

(define* output-fn (subr (alloc @i) (int tstate) tstate)
  (lambda (output state)
    (product (inputs (extract state inputs)) (outputs (cons output (extract state outputs))))))

(define-type program (productof (instructions strings) (inputs ints)))

(define* print-outputs (subr cb (ints) unit)
  (lambda (outputs)
    (if (null? outputs)
        #u
        (begin (print-string (concat (list "Output: " (int-to-string (car outputs)) "\n")))
               (print-outputs (cdr outputs))))))

(define* doit-program (subr cb (bool program) unit)
  (lambda (last p)
    (let* ((trap (product (input-fn input-fn) (output-fn output-fn)
                          (state (product (inputs (extract p inputs)) (outputs (the ints nil))))))
           (r (run-prog (extract p instructions) trap)))
      (if last
          (begin (print-outputs (extract (extract r state) outputs))
                 (print-string ((extract r statistics)))
                 (print-string "\n"))
          #u))))

(define* doit-programs (subr cb (bool (listof program @i)) unit)
  (lambda (last ps)
    (if (null? ps) #u (begin (doit-program last (car ps)) (doit-programs last (cdr ps))))))

(define* doit-loop (subr cb (int) unit)
  (lambda (n)
    (if (= n 0)
        #u
        (begin
          (doit-programs (= n 1)
                         (list (product (instructions Simple) (inputs (list)))
                               (product (instructions Twos) (inputs (list 10)))
                               (product (instructions Abs) (inputs (list -10)))
                               (product (instructions Fact) (inputs (list 12)))
                               (product (instructions GCD) (inputs (list 123456789 98765)))))
          (doit-loop (- n 1))))))

;; Main.doit, giving the hash of what it printed.
(define* doit (subr cb (int) int)
  (lambda (size) (begin (doit-loop size) (get out-hash))))

;; The input, where no compiler can fold it: a global, which a later
;; definition may replace.
(define size int 1)

(doit size)
