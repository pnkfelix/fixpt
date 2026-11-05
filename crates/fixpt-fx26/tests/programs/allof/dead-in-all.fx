;; ! a ab has no tag `c`
;; An arm skipped under every member of an `allof` is the error it would be
;; anywhere: a tag no member's subject has (a misspelt one, say).
(define-type ab (sumof (a int) (b int)))
(define f (allof (subr pure ((sumof (a int))) int) (subr pure (ab) int))
  (lambda (s) (tagcase s (a i i) (b j j) (c k k))))
