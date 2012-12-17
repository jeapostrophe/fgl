#lang typed/racket
(require/typed typed/racket [hash (All (a b) (-> (HashTable a b)))])

(define-type Node Integer)
(define-type (AdjPair b)
  (Pairof b Node))
(define-type (Adj b) (Listof (AdjPair b)))
;; Context = Predecessors x Node x Label x Successors
(define-type (Context a b) (Vector (Adj b) Node a (Adj b)))

(define-type (NodeInfo a b)
  (Vector a (Adj b)))
(define-type (Graph a b)
  (HashTable Node (NodeInfo a b)))

(define: (a b) (g-empty) : (Graph a b) ((inst make-immutable-hash Node (NodeInfo a b)) empty))

;; XXX Inefficient
(define: (a b) (& [ctxt : (Context a b)] [subg : (Graph a b)]) : (Graph a b)
  (match-define (vector p n l s) ctxt)
  (: add-suc-to-node ((AdjPair b) (Graph a b) -> (Graph a b)))
  (define (add-suc-to-node p-adj new)
    (match-define (cons edge-l p) p-adj)
    (: add-suc ((NodeInfo a b) -> (NodeInfo a b)))
    (define (add-suc ni)
      (match-define (vector node-l s) ni)
      (vector node-l (cons (cons edge-l n) s)))
    (hash-update new p add-suc))
  (define ext
    (foldr add-suc-to-node
           subg
           p))
  (hash-set ext n (vector l s)))

(define: (a b) (&any [g : (Graph a b)]) :  (Option (cons (Context a b) (Graph a b)))
  (define pos (hash-iterate-first g))
  (and pos
       (&vt (hash-iterate-key g pos) g)))

(define: (a b) (&vt [top-v : Node] [g : (Graph a b)]) :  (Option (cons (Context a b) (Graph a b)))
  (cond
    [(hash-has-key? g top-v)
     (define ni (hash-ref g top-v))
     (match-define (vector l s) ni)
     (define topless-g (hash-remove g top-v))
     (define-values (p subg)
       (for/fold:
        : (values (Adj b) (Graph a b))
        ([p : (Adj b) empty]
         [subg : (Graph a b) ((inst g-empty a b))])
        ([v : Node (in-hash-keys topless-g)]
         [ni : (NodeInfo a b) (in-hash-values topless-g)])
        (match-define (vector vl vs) ni)
        (define-values (new-p-rev vs-p)
          (partition (λ: ([ap : (AdjPair b)])
                         (equal? top-v (cdr ap)))
                     vs))
        (define new-p
          (map (λ: ([ap : (AdjPair b)])
                   (cons (car ap) v))
               new-p-rev))
        (values (append new-p p)
                (hash-set subg v (vector vl vs-p)))))
     (cons (vector p top-v l s) subg)]
    [else
     #f]))

(module+ test
  (: Figure1 (Graph Symbol String))
  (define Figure1
    ((inst & Symbol String) (vector (list (cons "left" 2) (cons "up" 3)) 1 'a (list (cons "right" 2)))
     ((inst & Symbol String) (vector empty 2 'b (list (cons "down" 3)))
      ((inst & Symbol String) (vector empty 3 'c empty)
       ((inst g-empty Symbol String))))))

  (: Figure1-p (Graph Symbol String))
  (define Figure1-p
    ((inst & Symbol String) (vector (list (cons "down" 2)) 3 'c (list (cons "up" 1)))
     ((inst & Symbol String) (vector (list (cons "right" 1)) 2 'b (list (cons "left" 1)))
      ((inst & Symbol String) (vector empty 1 'a empty)
       ((inst g-empty Symbol String)))))))

;; Lightly derived

(define: (a b) (g-empty? [g : (Graph a b)]) : Boolean
  (match (&any g)
    [#f
     #t]
    [(cons c g)
     #f]))

(define: (a b c) (ufold [f : ((Context a b) c -> c)] [u : c] [g : (Graph a b)]) : c
  (match (&any g)
    [#f
     u]
    [(cons c g)
     (f c (ufold f u g))]))

;; Derived

(define: (a b) (nodes [g : (Graph a b)]) : (Listof Node)
  (: cons-l ((Context a b) (Listof Node) -> (Listof Node)))
  (define (cons-l c l)
    (match-define (vector _ v _ _) c)
    (cons v l))
  (ufold cons-l empty g))

(define: (a b) (new-nodes [i : Exact-Nonnegative-Integer] [g : (Graph a b)]) : (Listof Node)
  (define n (foldr max 0 (nodes g)))
  (build-list n add1))

(define: (a b c d) (gmap [f : ((Context a b) -> (Context c d))] [g : (Graph a b)]) : (Graph c d)
  (: map-f ((Context a b) (Graph c d) -> (Graph c d)))
  (define (map-f c g)
    (& (f c) g))
  ((inst ufold a b (Graph c d)) map-f ((inst g-empty c d)) g))

(define: (a b) (g-reverse [g : (Graph a b)]) : (Graph a b)
  (: swap ((Context a b) -> (Context a b)))
  (define (swap c)
    (match-define (vector p v l s) c)
    (vector s v l p))
  (gmap swap g))

(define: (a b) (undir [g : (Graph a b)]) : (Graph a b)
  (: undir-f ((Context a b) -> (Context a b)))
  (define (undir-f c)
    (match-define (vector p v l s) c)
    (define ps (remove-duplicates (append p s)))
    (vector ps v l ps))
  (gmap undir-f g))

(define: (a b) (suc [c : (Context a b)]) : (Listof Node)
  (match-define (vector _ _ _ s) c)
  ((inst map Node (AdjPair b)) cdr s))

(define: (a b) (gsuc [v : Node] [g : (Graph a b)]) : (Listof Node)
  (match (&vt v g)
    [(cons c sg)
     (suc c)]))

(define: (a b) (deg [v : Node] [g : (Graph a b)]) : Exact-Nonnegative-Integer
  (match (&vt v g)
    [(cons c sg)
     (match-define (vector p _ _ s) c)
     (+ (length p) (length s))]))

(define: (a b) (del [v : Node] [g : (Graph a b)]) : (Graph a b)
  (match (&vt v g)
    [(cons c sg)
     sg]))

(define: (a b) (dfs [vs : (Listof Node)] [g : (Graph a b)]) : (Listof Node)
  (match vs
    [(list)
     empty]
    [(list-rest v vs)
     (match (&vt v g)
       [(cons c g)
        (cons v (dfs (append (suc c) vs) g))]
       [#f
        (dfs vs g)])]))

(module+ test
  (dfs (nodes Figure1) Figure1)
  (dfs (nodes Figure1-p) Figure1-p))

(define-struct: (a) Tree ([e : a] [kids : (Listof (Tree a))])
  #:transparent)

(define: (a b) (df [vs : (Listof Node)] [g : (Graph a b)]) : (Pairof (Listof (Tree Node)) (Graph a b))
  (match vs
    [(list)
     (cons empty g)]
    [(list-rest v vs)
     (match (&vt v g)
       [(cons c g)
        (match-define (cons f g_1) (df (suc c) g))
        (match-define (cons f-p g_2) (df vs g_1))
        (cons (cons (Tree v f) f-p)
              g_2)]
       [#f
        (df vs g)])]))

(define: (a b) (dff [vs : (Listof Node)] [g : (Graph a b)]) : (Listof (Tree Node))
  (car (df vs g)))

(module+ test
  (dff (nodes Figure1) Figure1)
  (dff (nodes Figure1-p) Figure1-p))

;; XXX topsort
;; XXX scc

;; Section 4.2
