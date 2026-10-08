;;; The FX-26 parser's types, in FX-26: the trees it makes, its effects, and
;;; what it was given of the files a program loads. A module file of the
;;; reader's regions and the parser's own, as `parser.fx` is, which loads it
;;; at its own; it holds no state, so any client may load it too, and the
;;; loads are the same types (`TODO.md` §68).

(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))
;; The reader's types, at these regions, and what these use of them.
(define reader-types ((proj (load-module "fx26:eager-reader-types.fx") rs re rm rc)))
(define-type syn (select reader-types syn))

;; What a parse may do: read what was read and build a tree
;; (`tree-builds`), and give up.
(define-effect tree-builds (maxeff (read @globals) (read rs) (alloc rs)))
(define-effect parses (maxeff tree-builds (goto rp)))

(define-type syns-a (listof syn acyclic))
(define-type names (listof symbol acyclic))

;;; ------------------------------------------------------------------ trees
;;; Each node ends with where it starts and ends. A list of none or one
;;; stands for something optional: a parameter's type, a tagcase's `else`.

(define-datatype exp
  (e-var symbol int int)
  (e-int int int int)
  (e-bool bool int int)
  (e-str string int int)
  (e-char char int int)
  (e-float f64 int int)
  (e-sym symbol int int)
  (e-unit int int)
  (e-lambda (listof (productof (1 symbol) (2 syns-a)) acyclic) exp int int)
  (e-app exp (listof exp acyclic) int int)
  (e-plambda syn exp int int)
  (e-proj exp syns-a int int)
  (e-if exp exp exp int int)
  (e-letrec (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp int int)
  (e-let (listof (productof (1 symbol) (2 exp)) acyclic) exp int int)
  (e-begin (listof exp acyclic) int int)
  (e-prompt exp exp exp int int)
  ;; `(letregion name body …)`, `(letrena name body …)` or `(letreap name
  ;; body …)`, or `(letfreeze name body …)`: what it makes besides the
  ;; region (0 nothing, 1 an arena, 2 a reap, 3 nothing, its region's data
  ;; frozen as it ends: `docs/research/places-and-regions.md`),
  ;; the region variable's name, the place a `letfreeze` freezes into
  ;; (`heap` unless given), and the body.
  (e-letregion int symbol symbol exp int int)
  ;; `(rlambda region (param …) body …)`: the region, and the `lambda`.
  (e-rlambda exp exp int int)
  (e-the syn exp int int)
  ;; `(convention C expression)`: the procedure converted to `C`.
  (e-convention syn exp int int)
  ;; A bloblet form, by name, with its field index, or -1.
  (e-bloblet symbol int (listof exp acyclic) int int)
  (e-product (listof (productof (1 symbol) (2 exp)) acyclic) int int)
  (e-extract exp symbol int int)
  (e-sum symbol exp int int)
  ;; Arms: the tag, whether it takes a product apart, the names, the body.
  (e-tagcase exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic)
             (listof (productof (1 symbol) (2 exp)) acyclic) int int)
  ;; `(module item …)` (`docs/research/first-class-modules.md`): each item
  ;; what it is (0 `define-generative`, 1 `define-type`, 2 `define`, 3
  ;; `define-rec`), the names it defines, their types (a `define`'s, none or
  ;; one), and its expressions: the values, or an abstract type's two
  ;; conversions, each `(lambda (x) x)` spanning the item.
  (e-module (listof (productof (1 int) (2 names) (3 syns-a) (4 (listof exp acyclic))) acyclic)
            int int)
  ;; `(with module body …)`: the body, with the module's values in scope.
  (e-with symbol exp int int))

;; A top-level form. A definition's type is a list of none or one; a
;; `define*`'s, of it and the `define*`.
(define-datatype top
  (t-define symbol syns-a exp int int)
  ;; `(define-rec (name type lambda) …)`: a top-level `letrec`.
  (t-define-rec (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) int int)
  (t-define-type syn syn int int)
  (t-define-effect syn syn int int)
  ;; `(define-generative head rep)`: read by the checker alone; its two
  ;; conversions follow it as definitions.
  (t-define-generative syn syn int int)
  (t-exp exp))

;; The trees' lists: of expressions, a `lambda`'s parameters, a `letrec`'s
;; and a `let`'s bindings, a `tagcase`'s arms, and top-level forms.
(define-type exp-list (listof exp acyclic))
(define-type param-list (listof (productof (1 symbol) (2 syns-a)) acyclic))
(define-type letrec-list (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type let-list (listof (productof (1 symbol) (2 exp)) acyclic))
(define-type arm-list (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
(define-type top-list (listof top acyclic))
(define-type mod-item (productof (1 int) (2 names) (3 syns-a) (4 exp-list)))
(define-type mod-items (listof mod-item acyclic))

(define-datatype presult (p-ok (listof top acyclic)) (p-err string int int))

;; What the driver read for each `load-module`, by where the form starts:
;; the file's base (0 if it could not be read or read), its path, why not
;; (`cannot read …`, or where in it reading failed), its forms, and its
;; text.
(define-type loaded-file
  (productof (1 int) (2 int) (3 string) (4 string) (5 syns-a) (6 string)))
(define-type loaded-files (listof loaded-file acyclic))
