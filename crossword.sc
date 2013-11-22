(define (assert flag msg)
  (if (eq? flag #t) 0
    (panic msg)))

(define (is_triple t)
  (and 
    (list? t)
    (= 3 (length t))))

(define (foldl l acc f)
  (if (null? l) acc
    (foldl (rest l) (f (first l) acc) f)))

(define (entry-length entry)
  (cond 
    ((across-entry? entry) (across-entry-length entry))
    ((down-entry? entry) (down-entry-length entry))
    (else (panic "Entry is neither down nor across"))))

(define (ensure-fits word entry)
  (when (not (= (string-length word) (entry-length entry)))
    (fail)))

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
(define (populate-scores identries)
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
                    (append acc (list other))
                    acc))))
  ;; work is an entry not in entries of pool.
  ;; returns (a,b) where
  ;;    a : entries from pool intersecting work.
  ;;    b : pool - {a}
  (define (xn-partition work pool)
    (let* ((idxns (find-adjacent work pool))
           (xnids (map first idxns))
           (xns (map second idxns))
           (non-xn-pool (foldl xnids pool 
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
                              (nodes-sofar (append nodesacc new-nodes)))
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
                                   (list i entry))
                                 entries))
         (pool (populate-scores identries))
         (sorted-entries (loop pool '())))
    sorted-entries))

(define (dummy-pre-sort entries) entries)

(define (solve-crossword-puzzle-by-backtracking entries words)
  (define (loop entries sol)
    (if (null? entries) sol
      (let* ((entry (first entries))
             (word (a-member-of words))
             (x (ensure-fits word entry))
             ;;(x (display entry))
             ;;(x (display word))
             (x (fill-entry entry word)))
        (check-consistency entry word sol)
        (loop (rest entries) (cons (list entry word) sol)))))
  (let* ((sorted-entries (pre-sort entries))
         (x (assert (= (length entries) (length sorted-entries))
                     "sorted entries have different length")))
    (loop sorted-entries '())))


;;; CROSSWORD CSP

(define (for-each-pair f l)
  (unless (null? l)
    (let ((x (for-each (lambda (x2) 
            (f (first l) x2)) (rest l))))
      (for-each-pair f (rest l)))))

(define-structure domain-variable
                  domain
                  before-demons
                  after-demons)

(define (create-domain-variable domain)
  (when (null? domain) (fail))
  (make-domain-variable domain '() '()))

(define (attach-before-demon! demon x)
  (local-set-domain-variable-before-demons!
    x (cons demon (domain-variable-before-demons x)))
  (demon))

(define (attach-after-demon! demon x)
  (local-set-domain-variable-after-demons!
    x (cons demon (domain-variable-after-demons x)))
  (demon))

(define (restrict-domain! x domain)
  (when (null? domain) (fail))
  (when (< (length domain)
           (length (domain-variable-domain x)))
    (for-each (lambda (demon) (demon))
              (domain-variable-before-demons x))
    (local-set-domain-variable-domain! x domain)
    (for-each (lambda (demon) (demon))
              (domain-variable-after-demons x))))

(define (assert-unary-constraint-gfc! constraint x)
  (restrict-domain! x (remove-if-not 
                        (lambda (xe) (constraint xe)) 
                        (domain-variable-domain x))))

(define (assert-binary-constraint-gfc! constraint x y)
  (attach-after-demon!
    (lambda ()
      (when (bound? x)
        (restrict-domain! y 
          (remove-if-not (lambda (ye) (constraint (binding x) ye)) 
                         (domain-variable-domain y)))))
    x)
  (attach-after-demon!
    (lambda ()
      (when (bound? y)
        (restrict-domain! x 
          (remove-if-not (lambda (xe) (constraint xe (binding y))) 
                         (domain-variable-domain x)))))
    y))

(define (assert-unary-constraint-ac! constraint x)
  (restrict-domain! x (remove-if-not 
                        (lambda (xe) (constraint xe)) 
                        (domain-variable-domain x))))

(define (assert-binary-constraint-ac! constraint x y)
  (attach-after-demon!
    (lambda ()
      (restrict-domain! y 
        (remove-if-not 
          (lambda (ye) 
            (some (lambda (xe) (constraint xe ye))
                  (domain-variable-domain x))) 
        (domain-variable-domain y))))
    x)
  (attach-after-demon!
    (lambda ()
      (restrict-domain! x
        (remove-if-not 
          (lambda (xe) 
            (some (lambda (ye) (constraint xe ye))
                  (domain-variable-domain y))) 
        (domain-variable-domain x))))
    y))

(define (words-of-length n words)
  (foldl words '()
         (lambda (word acc)
           (if (= n (string-length word))
             (cons word acc)
             acc))))

(define (solve-crossword-puzzle-by-constraints entries words) 
  ;; Add GUI helper as post-demon
  (define (attach-gui-demon var entry) 
    (attach-after-demon! 
      (lambda () (when (bound? var) 
                   (fill-entry entry (binding var)))) 
     var))
  ;; Create domain var for each entry. Domain is set of
  ;; words that fit in entry.
  (define (dvar-for-entry entry)
    (let* ((domain (words-of-length (entry-length entry) words))
           (var (create-domain-variable domain))
           (x (attach-gui-demon var entry)))
      (list entry var)))

  (let* ((evars (map dvar-for-entry entries))
         (x (for-each (lambda (evar)
                        attach-gui-demon (second evar)) 
                      evars))
         ;; the only constraint is that when entries intersect
         ;; then they must be consistently filled.
         (x (for-each-pair 
              (lambda (evar1 evar2) 
                (let* ((e1 (first evar1))
                       (e2 (first evar2))
                       (var1 (second evar1))
                       (var2 (second evar2)))
                  (when (entries-intersect? e1 e2)
                    (assert-constraint! (lambda (w1 w2) 
                        (consistent-entries? e1 e2 w1 w2)) 
                      (list var1 var2))))) 
              evars))
         (vars (map second evars)))
    (csp-solution vars first)))
