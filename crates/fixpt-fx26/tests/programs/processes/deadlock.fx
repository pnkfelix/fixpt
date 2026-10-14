;; ! a deadlock
;; Kayak's fourth test: A, asked, asks B and waits for B's answer; B, asked
;; by A, asks A, which is waiting and receives nothing. Nothing can run, and
;; the program waits on its own question: an error, not a hang.
(define-type msg (sumof (peer (addr msg @s)) (ask (icell int @r))))
;; What a relay does beyond its own mailbox.
(define-effect relays (maxeff (send @s) (alloc @r) (await @r) (init @r) nondet spin))
;; Told its peer, it answers each question by asking the peer.
(define* relay
  (poly ((p place)) (subr (maxeff (receive p) relays) ((inbox msg p)) unit))
  (plambda ((p place))
    (lambda (box)
      (tagcase (receive box)
        (peer other
          (tagcase (receive box)
            (ask reply
              (let ((mine (the (icell int @r) (make-icell))))
                (begin (send other (sum ask mine)) (icell-put! reply (icell-get mine)))))
            (peer x #u)))
        (ask reply #u)))))
(define a (addr msg @s) (spawn (box msg p) ((proj relay p) box)))
(define b (addr msg @s) (spawn (box msg p) ((proj relay p) box)))
(send a (sum peer b))
(send b (sum peer a))
(let ((c (the (icell int @r) (make-icell))))
  (begin (send a (sum ask c)) (icell-get c)))
