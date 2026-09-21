;;; The built-in `fx` module's signature -- GENERATED, do not edit.
;;; regenerate with: racket reference/fx91-stdmodule.rkt <out>
;;; source: GiffordHistory fx-lang/fx91 standard.scm, spliced in
;;; create-initial-envs order:
;;;   (effect-module bool-module unit-module refof-module int-module float-module char-module string-module sym-module permutation-module uniqueof-module listof-module vectorof-module sexp-module stream-module)
(moduleof
 (abs (read write init) effect)
 (abs bool type)
 (val a-bool bool)
 (val (equiv? and? or?) (subr (maxeff) ((x bool) (y bool)) bool))
 (val not? (subr (maxeff) ((x bool)) bool))
 (abs unit type)
 (val an-unit unit)
 (abs refof (dfunc type))
 (val (new ref) (poly ((t type)) (subr init ((x t)) (refof t))))
 (val (get ^) (poly ((t type)) (subr read ((x (refof t))) t)))
 (val (set! :=) (poly ((t type)) (subr write ((r (refof t)) (x t)) unit)))
 (abs int type)
 (val an-int int)
 (val (= < > <= >=) (subr (maxeff) ((x int) (y int)) bool))
 (val (+ * - / remainder modulo) (subr (maxeff) ((x int) (y int)) int))
 (val (neg absolute) (subr (maxeff) ((x int)) int))
 (abs float type)
 (val a-float float)
 (val (fl= fl< fl> fl<= fl>=) (subr (maxeff) ((x float) (y float)) bool))
 (val (fl+ fl* fl- fl/) (subr (maxeff) ((x float) (y float)) float))
 (val
  (flneg flabs log exp sqrt sin cos tan asin acos atan)
  (subr (maxeff) ((x float)) float))
 (val (floor ceiling truncate round) (subr (maxeff) ((x float)) int))
 (val int->float (subr (maxeff) ((x int)) float))
 (abs char type)
 (val a-char char)
 (val
  (char=? char<? char>? char<=? char>=?)
  (subr (maxeff) ((x char) (y char)) bool))
 (val
  (char-ci=? char-ci<? char-ci>? char-ci<=? char-ci>=?)
  (subr (maxeff) ((x char) (y char)) bool))
 (val
  (char-alphabetic?
   char-numeric?
   char-whitespace?
   char-lower-case?
   char-upper-case?)
  (subr (maxeff) ((x char)) bool))
 (val (char-upcase char-downcase) (subr (maxeff) ((x char)) char))
 (val char->int (subr (maxeff) ((x char)) int))
 (val int->char (subr (maxeff) ((x int)) char))
 (abs string type)
 (val a-string string)
 (val make-string (subr init ((l int) (c char)) string))
 (val string-length (subr (maxeff) ((s string)) int))
 (val string-ref (subr read ((s string) (i int)) char))
 (val string-set! (subr write ((s string) (i int) (c char)) unit))
 (val string-fill! (subr write ((s string) (c char)) unit))
 (val
  (string=?
   string<?
   string>?
   string<=?
   string>=?
   string-ci=?
   string-ci<?
   string-ci>?
   string-ci<=?
   string-ci>=?)
  (subr read ((s string) (t string)) bool))
 (val list->string (subr (maxeff read init) ((l (listof char))) string))
 (val string->list (subr (maxeff read init) ((s string)) (listof char)))
 (val substring (subr (maxeff read init) ((s string) (f int) (t int)) string))
 (val string-append (subr (maxeff init read) ((s string) (t string)) string))
 (val string-copy (subr (maxeff init read) ((s string)) string))
 (abs sym type)
 (val a-sym sym)
 (val sym->string (subr init ((s sym)) string))
 (val string->sym (subr read ((s string)) sym))
 (val sym=? (subr (maxeff) ((s sym) (t sym)) bool))
 (abs permutation type)
 (val a-permutation permutation)
 (val
  make-permutation
  (subr
   (maxeff)
   ((to (subr (maxeff) ((f int)) int)) (length int))
   permutation))
 (val cshift (subr (maxeff) ((l int) (o int)) permutation))
 (val identity (subr (maxeff) ((l int)) permutation))
 (abs uniqueof (dfunc type))
 (val unique (poly ((t type)) (subr init ((x t)) (uniqueof t))))
 (val value (poly ((t type)) (subr (maxeff) ((x (uniqueof t))) t)))
 (val
  eq?
  (poly
   ((t type))
   (subr (maxeff) ((u1 (uniqueof t)) (u2 (uniqueof t))) bool)))
 (abs listof (dfunc type))
 (val a-listof (poly ((t type)) (listof t)))
 (val null (poly ((t type)) (subr (maxeff) () (listof t))))
 (val null? (poly ((t type)) (subr (maxeff) ((l (listof t))) bool)))
 (val cons (poly ((t type)) (subr init ((a t) (d (listof t))) (listof t))))
 (val car (poly ((t type)) (subr read ((l (listof t))) t)))
 (val cdr (poly ((t type)) (subr read ((l (listof t))) (listof t))))
 (val set-car! (poly ((t type)) (subr write ((l (listof t)) (x t)) unit)))
 (val
  set-cdr!
  (poly ((t type)) (subr write ((l (listof t)) (x (listof t))) unit)))
 (val length (poly ((t type)) (subr read ((l (listof t))) int)))
 (val
  append
  (poly
   ((t type))
   (subr (maxeff read init) ((f (listof t)) (r (listof t))) (listof t))))
 (val
  reverse
  (poly ((t type)) (subr (maxeff read init) ((l (listof t))) (listof t))))
 (val
  list-tail
  (poly
   ((t type))
   (subr (maxeff read init) ((l (listof t)) (m int)) (listof t))))
 (val
  map
  (poly
   ((t type) (u type) (e effect))
   (subr
    (maxeff e init read)
    ((f (subr e ((x t)) u)) (l (listof t)))
    (listof u))))
 (val
  for-each
  (poly
   ((t type) (u type) (e effect))
   (subr (maxeff e init read) ((f (subr e ((x t)) u)) (l (listof t))) unit)))
 (val
  reduce
  (poly
   ((t type) (u type) (e effect))
   (subr
    (maxeff e init read)
    ((f (subr e ((x t) (r u)) u)) (l (listof t)) (s u))
    u)))
 (abs vectorof (dfunc type))
 (val
  make-vector
  (poly ((t type)) (subr init ((length int) (value t)) (vectorof t))))
 (val
  vector-length
  (poly ((t type)) (subr (maxeff) ((vector (vectorof t))) int)))
 (val
  vector-ref
  (poly ((t type)) (subr read ((vector (vectorof t)) (index int)) t)))
 (val
  vector-set!
  (poly
   ((t type))
   (subr write ((vector (vectorof t)) (index int) (new t)) unit)))
 (val
  vector-fill!
  (poly ((t type)) (subr write ((old (vectorof t)) (new t)) unit)))
 (val
  vector->list
  (poly
   ((t type))
   (subr (maxeff init read) ((vector (vectorof t))) (listof t))))
 (val
  list->vector
  (poly
   ((t type))
   (subr (maxeff init read) ((list (listof t))) (vectorof t))))
 (val
  vector-map
  (poly
   ((t type) (u type) (e effect))
   (subr
    (maxeff e init read)
    ((f (subr e ((v t)) u)) (vector (vectorof t)))
    (vectorof u))))
 (val
  vector-map2
  (poly
   ((t1 type) (t2 type) (u type) (e effect))
   (subr
    (maxeff e init read)
    ((f (subr e ((v1 t1) (v2 t2)) u))
     (vector1 (vectorof t1))
     (vector2 (vectorof t2)))
    (vectorof u))))
 (val
  vector-reduce
  (poly
   ((t type) (u type) (e effect))
   (subr
    (maxeff e read)
    ((f (subr e ((x t) (red u)) u)) (vector (vectorof t)) (seed u))
    u)))
 (val
  scan
  (poly
   ((t type) (e effect))
   (subr
    (maxeff e init read)
    ((f (subr e ((x t) (y t)) t)) (vector (vectorof t)))
    (vectorof t))))
 (val
  segmented-scan
  (poly
   ((t type) (e effect))
   (subr
    (maxeff e init read)
    ((f (subr e ((x t) (y t)) t))
     (segments (vectorof bool))
     (vector (vectorof t)))
    (vectorof t))))
 (val
  permute
  (poly
   ((t type))
   (subr
    (maxeff init read)
    ((mapping permutation) (vector (vectorof t)))
    (vectorof t))))
 (val
  compress
  (poly
   ((t type))
   (subr
    (maxeff init read)
    ((selection (vectorof bool)) (vector (vectorof t)))
    (vectorof t))))
 (val
  expand
  (poly
   ((t type))
   (subr
    (maxeff init read)
    ((selection (vectorof bool)) (vector (vectorof t)) (default (vectorof t)))
    (vectorof t))))
 (val
  eoshift
  (poly
   ((t type))
   (subr
    (maxeff init read)
    ((offset int) (vector (vectorof t)) (default (vectorof t)))
    (vectorof t))))
 (abs sexp type)
 (desc
  sexp-rep
  (sumof
   (|1| (productof (|1| unit)))
   (|2| (productof (|2| bool)))
   (|3| (productof (|3| sym)))
   (|4| (productof (|4| int)))
   (|5| (productof (|5| float)))
   (|6| (productof (|6| char)))
   (|7| (productof (|7| string)))
   (|8| (productof (|8| (listof sexp))))
   (|9| (productof (|9| (listof sexp))))))
 (val a-sexp sexp)
 (val
  cons~
  (poly
   ((e1 effect) (e2 effect) (t type) (u type))
   (subr
    (maxeff e1 e2)
    ((x (listof t))
     (s (subr e1 ((x t) (y (listof t))) u))
     (f (subr e2 ((x (listof t))) u)))
    u)))
 (val
  nil~
  (poly
   ((t type) (u type) (e1 effect) (e2 effect))
   (subr
    (maxeff e1 e2)
    ((x (listof t)) (s (subr e1 () u)) (f (subr e2 ((x (listof t))) u)))
    u)))
 (val unit->sexp (subr (maxeff) ((u unit)) sexp))
 (val bool->sexp (subr (maxeff) ((b bool)) sexp))
 (val sym->sexp (subr (maxeff) ((s sym)) sexp))
 (val int->sexp (subr (maxeff) ((i int)) sexp))
 (val float->sexp (subr (maxeff) ((f float)) sexp))
 (val char->sexp (subr (maxeff) ((c char)) sexp))
 (val string->sexp (subr (maxeff) ((s string)) sexp))
 (val list->sexp (subr (maxeff) ((l (listof sexp))) sexp))
 (val vector->sexp (subr (maxeff) ((l (vectorof sexp))) sexp))
 (val
  unit->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp) (s (subr e1 ((x unit)) t)) (f (subr e2 ((x sexp)) t)))
    t)))
 (val
  bool->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp) (s (subr e1 ((x bool)) t)) (f (subr e2 ((x sexp)) t)))
    t)))
 (val
  sym->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp) (s (subr e1 ((x sym)) t)) (f (subr e2 ((x sexp)) t)))
    t)))
 (val
  int->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp) (s (subr e1 ((x int)) t)) (f (subr e2 ((x sexp)) t)))
    t)))
 (val
  float->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp) (s (subr e1 ((x float)) t)) (f (subr e2 ((x sexp)) t)))
    t)))
 (val
  char->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp) (s (subr e1 ((x char)) t)) (f (subr e2 ((x sexp)) t)))
    t)))
 (val
  string->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp) (s (subr e1 ((x string)) t)) (f (subr e2 ((x sexp)) t)))
    t)))
 (val
  list->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp) (s (subr e1 ((x (listof sexp))) t)) (f (subr e2 ((x sexp)) t)))
    t)))
 (val
  vector->sexp~
  (poly
   ((e1 effect) (e2 effect) (t type))
   (subr
    (maxeff e1 e2)
    ((x sexp)
     (s (subr e1 ((x (vectorof sexp))) t))
     (f (subr e2 ((x sexp)) t)))
    t)))
 (val sexp=? (subr read ((s1 sexp) (s2 sexp)) bool))
 (abs stream type)
 (val standard-input stream)
 (val standard-output stream)
 (val error (poly ((t type)) (subr write ((msg string)) t)))
 (val unspecified (poly ((t type)) (subr pure () t)))
 (val open-input-stream (subr (maxeff init write) ((f string)) stream))
 (val open-output-stream (subr (maxeff init write) ((f string)) stream))
 (val stream-char-eof? (subr write ((s stream)) bool))
 (val stream-sexp-eof? (subr write ((s stream)) bool))
 (val stream-write-sexp (subr write ((s stream) (val sexp)) unit))
 (val write-sexp (subr write ((val sexp)) unit))
 (val stream-read-sexp (subr write ((s stream)) sexp))
 (val read-sexp (subr write () sexp))
 (val stream-write-char (subr write ((s stream) (val char)) unit))
 (val write-char (subr write ((val char)) unit))
 (val stream-read-char (subr write ((s stream)) char))
 (val read-char (subr write () char))
 (val close-stream (subr write ((s stream)) unit)))
