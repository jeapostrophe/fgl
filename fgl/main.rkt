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

(define: (a b) (grev [g : (Graph a b)]) : (Graph a b)
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

(define: (a b) (pre [c : (Context a b)]) : (Listof Node)
  (match-define (vector p _ _ _) c)
  ((inst map Node (AdjPair b)) cdr p))

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
     sg]
    [#f
     g]))

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

(define: (a) (postorder [t : (Tree a)]) : (Listof a)
  (match-define (Tree v ts) t)
  (append ((inst append-map a (Tree a)) postorder ts)
          (list v)))

(define: (a b) (df [vs : (Listof Node)] [g : (Graph a b)])
  : (values (Listof (Tree Node)) (Graph a b))
  (match vs
    [(list)
     (values empty g)]
    [(list-rest v vs)
     (match (&vt v g)
       [(cons c g)
        (define-values (f g_1) (df (suc c) g))
        (define-values (f-p g_2) (df vs g_1))
        (values (cons (Tree v f) f-p)
                g_2)]
       [#f
        (df vs g)])]))

(define: (a b) (dff [vs : (Listof Node)] [g : (Graph a b)])
  : (Listof (Tree Node))
  (define-values (fst snd) (df vs g))
  fst)

(module+ test
  (dff (nodes Figure1) Figure1)
  (dff (nodes Figure1-p) Figure1-p))

(define: (a b) (topsort [g : (Graph a b)])
  : (Listof Node)
  (define vs (nodes g))
  (reverse ((inst append-map Node (Tree Node)) postorder (dff vs g))))

(module+ test
  (topsort Figure1)
  (topsort Figure1-p))

(define: (a b) (scc [g : (Graph a b)])
  : (Listof (Tree Node))
  (dff (topsort g) (grev g)))

(module+ test
  (scc Figure1)
  (scc Figure1-p))

(define: (a b) (bfs [vs : (Listof Node)] [g : (Graph a b)])
  : (Listof Node)
  (match vs
    [(list)
     empty]
    [(list-rest v vs)
     (match (&vt v g)
       [(cons c g)
        (cons v (bfs (append vs (suc c)) g))]
       [#f
        (bfs vs g)])]))

(module+ test
  (bfs (nodes Figure1) Figure1)
  (bfs (nodes Figure1-p) Figure1-p))

(define-type Path (Listof Node))
(define-type RTree (Listof Path))

(define: (a b) (bft [v : Node] [g : (Graph a b)])
  : RTree
  (bf (list (list v)) g))

(define: (a b) (bf [ps : RTree] [g : (Graph a b)])
  : RTree
  (match ps
    [(list)
     empty]
    [(list-rest p ps)
     (match p
       [(list-rest v _)
        (match (&vt v g)
          [(cons c g)
           (cons p
                 (bf (append ps
                             (map
                              (λ: ([more : Node])
                                  (cons more p))
                              (suc c)))
                     g))]
          [#f
           (bf ps g)])]
       [_
        (bf ps g)])]))

(module+ test
  (bf ((inst map Path Node) list (nodes Figure1)) Figure1)
  (bf ((inst map Path Node) list (nodes Figure1-p)) Figure1-p))

(define: (a) (first-such-that [p : (a -> Boolean)] [l : (Listof a)]) : a
  (first (filter p l)))

(define: (a b) (esp [s : Node] [t : Node] [g : (Graph a b)]) : Path
  (define (first-is-t vs)
    (match-define (list-rest v _) vs)
    (equal? v t))
  (reverse (first-such-that first-is-t (bft s g))))

(module+ test
  (esp 1 2 Figure1)
  (esp 1 3 Figure1)
  (esp 2 3 Figure1))

(define-type (LNode a) (Pairof Node a))
(define-type (LPath a) (Listof (LNode a)))
(define-type (LRTree a) (Listof (LPath a)))

(define: (a) (getPath [v : Node] [l : (LRTree a)]) : Path
  (define (first-is-v x)
    (match-define (list-rest (cons w _) _) x)
    (equal? w v))
  (reverse ((inst map Node (LNode a)) car (first-such-that first-is-v l))))

;; XXX expand (pg 22)
;; XXX dijkstra (pg 22)
;; XXX spt (pg 22)
;; XXX sp (pg 22)

;; XXX addEdges (pg 23)
;; XXX mst (pg 23)
;; XXX prim (pg 23)
;; XXX mstp (pg 23)
;; XXX joinPaths (pg 23)
;; XXX joinAt (pg 23)

(define: (a b) (indep [g : (Graph a b)])
  : (Listof Node)
  (cond
    [(g-empty? g)
     empty]
    [else
     (define vs 
       (nodes g))
     (define v
       (argmax (λ: ([v : Node]) (deg v g)) vs))     
     (: g-p (Graph a b))
     (match-define (cons c g-p) (&vt v g))
     (define i₁ (indep g-p))
     (: next (Listof Node))
     (define next
       (append (pre c) (suc c)))
     (: next-g (Graph a b))
     (define next-g
       (foldr (inst del a b) g-p next))
     (define i₂ (cons v (indep next-g)))
     (if ((length i₁) . > . (length i₂))
       i₁
       i₂)]))

(module+ test
  (indep Figure1))
