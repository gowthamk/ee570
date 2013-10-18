(module p1 racket
  
(define (id x) x)
  
; current-continuation : -> continuation
(define (current-continuation) 
  (call-with-current-continuation 
   (lambda (cc)
     (cc cc))))

; fail-stack : list[continuation]
(define fail-stack '())

; fail : -> ...
(define (fail)
  (if (not (pair? fail-stack)) #f
      (begin
        (let ((back-track-point (car fail-stack)))
          (set! fail-stack (cdr fail-stack))
          (back-track-point back-track-point)))))

; amb : list[a] -> a
(define (amb choices)
  (let ((cc (current-continuation)))
    (cond
      ((null? choices)      (fail))
      ((pair? choices)      (let ((choice (car choices)))
                              (set! choices (cdr choices))
                              (set! fail-stack (cons cc fail-stack))
                              choice)))))

; (assert condition) will cause
; condition to be true, and if there
; is no way to make it true, then
; it signals and error in the program.
(define (assert condition)
  (if (not condition)
      (fail)
      #t))

(define (allprefsufs l) 
  (if (null? l) (list (list '() '()))
      (cons (list '() l)
            (map  (lambda (prefsuf) 
                   (list (cons (first l) (first prefsuf))
                         (second prefsuf)))
                  (allprefsufs (rest l))))))
  
(define (panic str) 
  (display str)
  (raise str))
  
(define (pattern-variable? pattern) (memq pattern '(e e1 e2 e3)))

(define (pattern-list-variable? pattern) (memq pattern '(e... e1... e2... e3...)))

(define (lookup-pattern-variable pattern-variable bindings)
  (cond
    ((null? bindings) #f)
    ((eq? pattern-variable (first (first bindings)))
      (second (first bindings)))
    (else (lookup-pattern-variable
      pattern-variable (rest bindings)))))

(define (unify binds1 binds2)
  (cond
    ((null? binds1) binds2)
    ((null? binds2) binds1)
    ((or (memq #f binds1) (memq #f binds2))
      (list #f))
    (else 
     (let* ((bind (first binds1))
            (patvar (first bind))
            (newval (second bind))
            (binds (unify (rest binds1) binds2)))
        (cond 
          ((memq #f binds) (list #f))
          (else 
           (let* ((oldval (lookup-pattern-variable patvar binds)))
            (if (or (equal? oldval #f) (equal? oldval newval))
                (cons bind binds)
                (list #f)))))))))
  
(define (match pattern expression)
  (cond
    ((pattern-variable? pattern) (list (list pattern expression)))
    ((pattern-list-variable? pattern)
      (panic "Pattern list variable not at end of list"))
    ((and (list? pattern)
      (= (length pattern) 1)
      (pattern-list-variable? (first pattern)))
      (list (list (first pattern) expression)))
    ((and (list? pattern) (not (null? pattern)))
      (if (and (list? expression) (not (null? expression)))
          (if (pattern-list-variable? (first pattern))
              (let* ((prefsuf (amb (allprefsufs expression))))
                (if (eq? prefsuf false) (list #f)
                    (let* ((prefexp (first prefsuf))
                           (sufexp (second prefsuf))
                           (sufmatch (match (rest pattern) sufexp)))
                      (if (assert (not (memq #f sufmatch))) 
                          (cons (list (first pattern) prefexp) sufmatch)
                          (list #f)))))
              (append (match (first pattern) (first expression))
                  (match (rest pattern) (rest expression))))
          (list #f)))
    ((equal? pattern expression) '())
    (else (list #f))))

(define (instantiate pattern bindings)
  (cond ((pattern-variable? pattern)
    (lookup-pattern-variable pattern bindings))
    ((pattern-list-variable? pattern)
      (lookup-pattern-variable pattern bindings))
    ((and (list? pattern) (not (null? pattern)))
      (cons (instantiate (first pattern) bindings)
      (instantiate (rest pattern) bindings)))
    (else pattern)))

(define (applicable? rule expression)
  (not (memq #f (match (first rule) expression))))

(define (first-applicable-rule rules expression)
  (cond ((null? rules) #f)
    ((applicable? (first rules) expression) (first rules))
    (else (first-applicable-rule (rest rules) expression))))

(define (apply-rule rule expression)
  (let* ((binds (match (first rule) expression))
         (newexp (instantiate (third rule) binds)))
    (id newexp)))

(define (apply-rules rules expression)
  (let ((rule (first-applicable-rule rules expression)))
    (if rule
        (let* ((newexp (apply-rule rule expression))
               (newexp1 (rewrite rules newexp)))
          (id newexp1))
        expression)))

(define (rewrite rules expression)
  (if (list? expression)
      (let* ((expr (map (lambda (expression) 
                         (rewrite rules expression))
                       expression))
            (simpexpr (apply-rules rules expr)))
        (id simpexpr))
      (id expression)))

(define *PropCalcRules*
 '(; not #t --> #f
   ;((not #t)
   ; -~->
   ; #f)
   ; not #f --> #t
   ;((not #f)
   ; -~->
   ; #t)
   ; double negation
   ;((not (not e))
   ; -~->
   ; e)
   ; and
   ;(and
   ; -~->
   ; #t)
   ; and p
   ;((and e)
   ; -~->
   ; e)
   ; and #t
   ((and e1... (and e2...) e3...)
    -~->
    (and e1... e2... e3...))
   ))

(define (simplify pcexpr) 
  (rewrite *PropCalcRules* pcexpr))
  
;(define (simulated-plus x y)
; (length
;  (second
;   (first
;    (second
;     (rewrite (initial-state (map (lambda (i) #t) (enumerate x))
;           (map (lambda (i) #t) (enumerate y)))
;        *boilerchip*))))))

)