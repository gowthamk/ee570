(define (assert flag msg)
  (if (eq? flag #t) 0
    (panic msg)))

(define (foldl l acc f)
  (if (null? l) acc
    (foldl (rest l) (f (first l) acc) f)))

(define (check-consistency entry word sol)
  (for-each
    (lambda (bind)
      (let* ((old-entry (first bind))
             (old-word (second bind)))
        (when (not (consistent-entries? old-entry entry 
                                        old-word word))
          (fail))))
    sol))

;; Takes (id * entry) list
;; Returns (id * entry * score) list
(define (populate-score identries)
  (map (lambda (identry)
         (let* ((myid (first identry))
                (myentry (second identry))
                (myscore (foldl identries 0 
                          (lambda (identry acc)
                            (cond 
                              ((= myid (first identry)) acc)
                              ((entries-intersect? myentry (second identry))
                                (+ 1 acc))
                              (else acc))))))
           (list myid myentry myscore)))
       identries))

;; Takes (id * entry * score) list
;; returns member of the list with max score.
(define (member-with-max-score pool)
  (if (null? pool) (panic "Empty pool")
    (foldl (rest pool) (first pool)
           (lambda (e beste)
             (if (> (third e) (third beste)) e beste)))))

;; Removes member with id = id from pool.
;; precondition : no duplicate ids in pool
(define (remove-id id pool)
  (cond
    ((null? pool) (panic "id not found!"))
    ((= id (first (first pool))) (rest pool))
    (else (cons (first pool) (remove-id id (rest pool))))))

;; Precondition: 
;;    worklist is list of only entries
;;    worklist not in entries of pool
;; Returns (a,b) where
;; a : list of plain entries.
;;     worklist is prefix of a.
;; b : pool - {a}
(define (bfs worklist pool)
  ;; item is an entry.
  ;; returns members of pool whose
  ;; entries are adjacent (xn with) item
  (define (find-adjacent item pool)
    (foldl pool '() 
           (lambda (other acc) 
              (if (entries-intersect? item (second other))
                    (append acc other)
                    acc))))
  ;; work is an entry not in entries of pool.
  ;; returns (a,b) where
  ;;    a : entries from pool intersecting work.
  ;;    b : pool - {a}
  (define (xn-partition work pool)
    (let* ((idxns (find-adjacent work pool))
           (xnids (map first idxns))
           (xns (map second idxns))
           (non-xn-pool (foldl xnids cur-pool 
                        (lambda (xnid pool)
                          (remove-id xnid pool)))))
       (list xns non-xn-pool)))

  (if (null? worklist) (list worklist pool)
    (let* ((x (foldl worklist (list '() pool) 
                     (lambda (work acc)
                       (let* ((nodesacc (first acc))
                              (poolacc (second acc))
                              (news (xn-partition work poolacc))
                              (new-nodes (first news))
                              (new-pool (second news))
                              (nodes-sofar (append (nodesacc new-nodes))))
                         (list nodes-sofar new-pool)))))
           (all-adjacent (first x))
           (remaining (second x))
           (y (bfs all-adjacent remaining))
           (reachable (first y))
           (unreachable (second y)))
      (list (append worklist reachable) unreachable))))

(define (pre-sort entries)
  ;; should return only entries from pool
  (define (loop pool res)
    (if (null? pool) res
      (let* ((max-identry (member-with-max-score pool))
             (max-id (first max-identry))
             (max-entry (second max-identry))
             (others (remove-id max-id pool))
             (y (bfs (list max-entry) others))
             (sorted-entries (first y))
             (new-pool (second y))
             (new-res (append res sorted-entries)))
        (loop new-pool new-res))))
  (let* ((identries (map-indexed (lambda (entry i)
                                   (list i entry))))
         (pool (populate-scores identries))
         (sorted-entries (loop pool '())))
    sorted-entries))

(define (solve-crossword-puzzle-by-backtracking entries words)
  (define (loop entries sol)
    (if (null? entries) sol
      (let* ((entry (first entries))
             (word (a-member-of words))
             (fill-entry entry word))
        (check-consistency entry word sol)
        (loop (rest entries) (cons (list entry word) sol)))))
  (let* ((sorted-entries (pre-sort entries))
         (x (assert ((= (length entries) (length sorted-entries)),
                     "sorted entries have different length"))))
    (loop (pre-sort entries) '())))
