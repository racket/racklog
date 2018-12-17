#lang racket/base
(require (for-syntax racket/base
                     racket/list
                     syntax/kerncase)
         racket/list
         racket/contract
         racket/stxparam
         "unify.rkt")

;Dorai Sitaram
;1989, revised Feb. 1993, Mar. 1997

(define-syntax %let
  (syntax-rules ()
    ((%let (x ...) . e)
     (let ((x (_)) ...)
       . e))))

(define %= unify)

(define-syntax %or
  (syntax-rules ()
    ((%or g ...)
     (lambda (__fk)
       (let/racklog-sk __sk
         (let/racklog-fk (__fk __fk)
           (__sk ((logic-var-val* g) __fk)))
         ...
         (__fk 'fail))))))

(define-syntax %and
  (syntax-rules ()
    ((%and g ...)
     (lambda (__fk)
       (let* ((__fk ((logic-var-val* g) __fk))
              ...)
         __fk)))))

(define (%apply pred args)
  (lambda (fk)
    (let ([pred-v (if (logic-var? pred)
                      (logic-var-val pred)
                      pred)]
          [args-v (let lv->list ([lv args])
                    (let ([v (if (logic-var? lv) (logic-var-val lv) lv)])
                      (cond
                        [(null? v) v]
                        [(pair? v) (cons (car v) (lv->list (cdr v)))]
                        [else (fk 'fail)])))])
      (if (and (procedure? pred-v) (procedure-arity-includes? pred-v (length args-v)))
          ((apply pred-v args-v) fk)
          (fk 'fail)))))

(define (%andmap pred lst . rest)
  (define lsts (cons lst rest))
  (lambda (fk)
    (let/racklog-sk sk
      ; Base case (all lists empty)
      (let/racklog-fk (fk fk)
        (sk (foldl (lambda (lst fk) ((%= lst '()) fk)) fk lsts)))
      ; Call and recurse
      (let/racklog-fk (fk fk)
        (sk (let ([heads (map (lambda (lst) (_)) lsts)]
                  [tails (map (lambda (lst) (_)) lsts)])
              (let* ([fk (foldl (lambda (lst h t fk) ((%= lst (cons h t)) fk)) fk lsts heads tails)]
                     [fk ((%apply pred heads) fk)])
                ((apply %andmap pred tails) fk)))))
      (fk 'fail))))

(define-syntax-parameter !
  (λ (stx) (raise-syntax-error '! "May only be used syntactically inside %rel or %cut-delimiter expression." stx)))

(define-syntax %cut-delimiter
  (syntax-rules ()
    ((%cut-delimiter g)
     (lambda (__fk)
       (let ((this-! (lambda (__fk2)
                       (lambda (msg)
                         ; Unwind any bindings in the body
                         (unless (equal? __fk2 __fk) (__fk2 __fk))
                         ; Pass on the message, skipping the body
                         (unless (equal? __fk msg) (__fk msg))))))
         (syntax-parameterize 
          ([! (make-rename-transformer #'this-!)])
          ((logic-var-val* g) __fk)))))))

(struct relation (clauses)
  #:property prop:procedure
  (lambda (rel . __fmls)
    (%cut-delimiter
      (lambda (__fk)
        (let/racklog-sk __sk
          (for ([clause (in-list (relation-clauses rel))])
            (let/racklog-fk (fail-clause __fk)
              (__sk ((clause __fmls !) fail-clause))))
          (__fk 'fail))))))

(define-syntax %rel
  (syntax-rules ()
    ((%rel (v ...) ((a ...) subgoal ...) ...)
     (relation
      (list
       (lambda (__fmls rel-cut)
         (syntax-parameterize ([! (make-rename-transformer #'rel-cut)])
           (%let (v ...)
             (%and (%= __fmls (list a ...))
                   subgoal ...))))
       ...)))))

(define %fail
  (lambda (fk) (fk 'fail)))

(define %true
  (lambda (fk) fk))

(define-for-syntax orig-insp (variable-reference->module-declaration-inspector
                              (#%variable-reference)))

(define-syntax (%is stx)
  (syntax-case stx ()
    [(%is v e)
     (with-syntax ([fe (syntax-disarm 
                        (local-expand #'e 'expression empty)
                        orig-insp)])
       (syntax/loc stx
         (lambda (__fk)
           ((%= v (%is/fk fe __fk)) __fk))))]))
(define-syntax (%is/fk stx)
  (kernel-syntax-case stx #f
    [(_ (#%plain-lambda fmls e ...) fk)
     (syntax/loc stx (#%plain-lambda fmls (%is/fk e fk) ...))]
    [(_ (case-lambda [fmls e ...] ...) fk)
     (syntax/loc stx (case-lambda [fmls (%is/fk e fk) ...] ...))]
    [(_ (if e1 e2 e3) fk)
     (syntax/loc stx (if (%is/fk e1 fk)
                         (%is/fk e2 fk) 
                         (%is/fk e3 fk)))]
    [(_ (begin e ...) fk)
     (syntax/loc stx (begin (%is/fk e fk) ...))]
    [(_ (begin0 e ...) fk)
     (syntax/loc stx (begin0 (%is/fk e fk) ...))]
    [(_ (let-values ([(v ...) ve] ...)
          be ...) fk)
     (syntax/loc stx
       (let-values ([(v ...) (%is/fk ve fk)] ...) 
         (%is/fk be fk) ...))]
    [(_ (letrec-values ([(v ...) ve] ...)
          be ...) fk)
     (syntax/loc stx
       (letrec-values ([(v ...) (%is/fk ve fk)] ...) 
         (%is/fk be fk) ...))]
    [(_ (set! i e) fk)
     (syntax/loc stx (set! i (%is/fk e fk)))]
    [(_ (quote d) fk)
     (syntax/loc stx (quote d))]
    [(_ (quote-syntax d) fk)
     (syntax/loc stx (quote-syntax d))]
    [(_ (with-continuation-mark e1 e2 e3) fk)
     (syntax/loc stx (with-continuation-mark
                         (%is/fk e1 fk)
                       (%is/fk e2 fk) 
                       (%is/fk e3 fk)))]
    [(_ (#%plain-app e ...) fk)
     (syntax/loc stx (#%plain-app (%is/fk e fk) ...))]
    [(_ x fk)
     (syntax/loc stx
       (if (and (logic-var? x) (unbound-logic-var? x))
           (fk 'fail) (logic-var-val* x)))]
    
    ))

#;(define-syntax %is/fk
  (syntax-rules (quote)
    ((%is/fk (quote x) fk) (quote x))
    ((%is/fk (x ...) fk)
     ((%is/fk x fk) ...))
    ((%is/fk x fk)
     (if (and (logic-var? x) (unbound-logic-var? x))
         (fk 'fail) (logic-var-val* x)))))

(define ((make-binary-arithmetic-relation f) x y)
  (%and (%is #t (number? x))
        (%is #t (number? y))
        (%is #t (f x y))))

(define %=:= (make-binary-arithmetic-relation =))
(define %> (make-binary-arithmetic-relation >))
(define %>= (make-binary-arithmetic-relation >=))
(define %< (make-binary-arithmetic-relation <))
(define %<= (make-binary-arithmetic-relation <=))
(define %=/= (make-binary-arithmetic-relation (compose not =)))

(define (%constant x)
  (lambda (fk)
    (if (constant? x) fk (fk 'fail))))

(define (%compound x)
  (lambda (fk)
    (if (is-compound? x) fk (fk 'fail))))

(define (%var x)
  (lambda (fk) (if (var? x) fk (fk 'fail))))

(define (%nonvar x)
  (lambda (fk) (if (var? x) (fk 'fail) fk)))

(define ((make-negation p) . args) 
  ;basically inlined cut-fail
  (lambda (fk)
    (if (let/racklog-sk k
          ((apply p args) (make-racklog-fk (lambda (d) (k #f)))))
        (fk 'fail)
        fk)))

(define %/=
  (make-negation %=))

(define (%== x y)
  (lambda (fk) (if (ident? x y) fk (fk 'fail))))

(define (%/== x y)
  (lambda (fk) (if (ident? x y) (fk 'fail) fk)))

(define (%freeze s f)
  (lambda (fk)
    ((%= (freeze s) f) fk)))

(define (%melt f s)
  (lambda (fk)
    ((%= (melt f) s) fk)))

(define (%melt-new f s)
  (lambda (fk)
    ((%= (melt-new f) s) fk)))

(define (%copy s c)
  (lambda (fk)
    ((%= (copy s) c) fk)))

(define (%not g)
  (%if-then-else g %fail %true))

(define %empty-rel
  (relation '()))

(define-syntax %assert!
  (syntax-rules ()
    ((_ rel-name (v ...) ((a ...) subgoal ...) ...)
     (set! rel-name
           (let ((__old-rel rel-name)
                 (__new-addition (%rel (v ...) ((a ...) subgoal ...) ...)))
             (relation (append (relation-clauses __old-rel)
                               (relation-clauses __new-addition))))))))

(define-syntax %assert-after!
  (syntax-rules ()
    ((_ rel-name (v ...) ((a ...) subgoal ...) ...)
     (set! rel-name
           (let ((__old-rel rel-name)
                 (__new-addition (%rel (v ...) ((a ...) subgoal ...) ...)))
             (relation (append (relation-clauses __new-addition)
                               (relation-clauses __old-rel))))))))

(define (set-cons e s)
  (if (member e s) s (cons e s)))

(define-struct goal-with-free-vars (vars subgoal))

(define-syntax %free-vars
  (syntax-rules ()
    ((%free-vars (v ...) g)
     (make-goal-with-free-vars
      (list v ...) 
      g))))

(define ((make-bag-of kons) lv goal bag)
  (let ((fvv '()))
    (when (goal-with-free-vars? goal)
      (set! fvv (goal-with-free-vars-vars goal))
      (set! goal (goal-with-free-vars-subgoal goal)))
    (make-bag-of-aux kons fvv lv goal bag)))

(define (make-bag-of-aux kons fvv lv goal bag)
  (lambda (fk)
    (let/racklog-sk sk
      (let ((lv2 (cons fvv lv)))
        (let* ((acc '())
               (fk-final
                (lambda (d)
                  (sk ((separate-bags fvv bag acc) fk))))
               (fk-retry (goal fk-final)))
          (set! acc (kons (logic-var-val* lv2) acc))
          (fk-retry 'retry))))))

(define (separate-bags fvv bag acc)
  (let ((bags (let loop ((acc acc)
                         (current-fvv #f) (current-bag '())
                         (bags '()))
                (if (null? acc)
                    (cons (cons current-fvv current-bag) bags)
                    (let ((x (car acc)))
                      (let ((x-fvv (car x)) (x-lv (cdr x)))
                        (if (or (not current-fvv) (equal? x-fvv current-fvv))
                            (loop (cdr acc) x-fvv (cons x-lv current-bag) bags)
                            (loop (cdr acc) x-fvv (list x-lv)
                                  (cons (cons current-fvv current-bag) bags)))))))))
    (if (null? bags) (%= bag '())
        (let ((fvv-bag (cons fvv bag)))
          (let loop ((bags bags))
            (if (null? bags) %fail
                (%or (%= fvv-bag (car bags))
                     (loop (cdr bags)))))))))

(define %bag-of (make-bag-of cons))
(define %set-of (make-bag-of set-cons))

(define (%bag-of-1 x g b)
  (%and (%bag-of x g b)
        (%= b (cons (_) (_)))))

(define (%set-of-1 x g s)
  (%and (%set-of x g s)
        (%= s (cons (_) (_)))))

(define *more-fk* (box (λ (d) (error '%more "No active %which"))))

(define-syntax %which
  (syntax-rules ()
    ((%which (v ...) g)
     (with-racklog-prompt
       (%let (v ...)
         (set-box! *more-fk*
                   ((logic-var-val* g)
                    (make-racklog-fk
                     (lambda (d)
                       (set-box! *more-fk* #f)
                       (abort-to-racklog-prompt #f)))))
         (abort-to-racklog-prompt
          (list (cons 'v (logic-var-val* v))
                ...)))))
    [(%which (v ...) g ...)
     (%which (v ...) (%and g ...))]))

(define (%more)
  (with-racklog-prompt
    (if (unbox *more-fk*)
        ((unbox *more-fk*) 'more)
        #f)))

(define-syntax %find-all
  (syntax-rules ()
    [(_ (v ...) g)
     (list* (%which (v ...) g)
            (%more-list))]))

(define (%more-list)
  (define a (%more))
  (if a
      (list* a (%more-list))
      empty))

(define racklog-prompt-tag (make-continuation-prompt-tag 'racklog))
(define (abort-to-racklog-prompt a)
  (abort-current-continuation racklog-prompt-tag (λ () a)))
(define-syntax-rule (with-racklog-prompt e ...)
  (call-with-continuation-prompt (λ () e ...) racklog-prompt-tag))
(define-syntax-rule (let/racklog-cc k e ...)
  (call-with-current-continuation (λ (k) e ...) racklog-prompt-tag))
(define-syntax-rule (let/racklog-sk k e ...)
  (let/racklog-cc k e ...))
(define (make-racklog-fk fk [uk #f])
  (λ (msg)
    (if (procedure? msg)
        (when uk (unless (equal? uk msg) (uk msg))) ; unwind
        (fk 'fail))))
(define-syntax-rule (let/racklog-fk (k uk) e ...)
  (let/racklog-cc fk (let ([k (make-racklog-fk fk uk)]) e ...)))

(define (%member x y)
  (%let (xs z zs)
        (%or
         (%= y (cons x xs))
         (%and (%= y (cons z zs))
               (%member x zs)))))

(define (%if-then-else p q r)
  (%cut-delimiter
   (%or
    (%and p ! q)
    r)))

(define %append
  (%rel (x xs ys zs)
        (('() ys ys))
        (((cons x xs) ys (cons x zs))
         (%append xs ys zs))))

(define %repeat
  (%rel ()
        (())
        (() (%repeat))))

(define fk? ((or/c symbol? procedure?) . -> . any))
(define goal/c 
  (or/c goal-with-free-vars?
        (fk? . -> . fk?)))
(define relation/c
  (->* () () #:rest (listof unifiable?) goal/c))

; XXX Add contracts in theses macro expansions
(provide %and %assert! %assert-after! %cut-delimiter %free-vars %is %let
         %or %rel %which %find-all !)
(provide/contract
 [goal/c contract?]
 [logic-var? (any/c . -> . boolean?)]
 [atom? (any/c . -> . boolean?)]
 [atomic-struct? (any/c . -> . boolean?)]
 [compound-struct? (any/c . -> . boolean?)]
 [compound? (any/c . -> . boolean?)]
 [unifiable? (any/c . -> . boolean?)]
 [answer-value? (any/c . -> . boolean?)]
 [answer? (any/c . -> . boolean?)]
 [%/= (unifiable? unifiable? . -> . goal/c)]
 [%/== (unifiable? unifiable? . -> . goal/c)]
 [%< (unifiable? unifiable? . -> . goal/c)]
 [%<= (unifiable? unifiable? . -> . goal/c)]
 [%= (unifiable? unifiable? . -> . goal/c)]
 [%=/= (unifiable? unifiable? . -> . goal/c)]
 [%=:= (unifiable? unifiable? . -> . goal/c)]
 [%== (unifiable? unifiable? . -> . goal/c)]
 [%> (unifiable? unifiable? . -> . goal/c)]
 [%>= (unifiable? unifiable? . -> . goal/c)]
 [%andmap (unifiable? unifiable? unifiable? ... . -> . goal/c)]
 [%append (unifiable? unifiable? unifiable? . -> . goal/c)]
 [%apply (unifiable? unifiable? . -> . goal/c)]
 [%bag-of (unifiable? goal/c unifiable? . -> . goal/c)]
 [%bag-of-1 (unifiable? goal/c unifiable? . -> . goal/c)]
 [%compound (unifiable? . -> . goal/c)]
 [%constant (unifiable? . -> . goal/c)]
 [%copy (unifiable? unifiable? . -> . goal/c)]
 [%empty-rel relation/c]
 [%fail goal/c]
 [%freeze (unifiable? unifiable? . -> . goal/c)]
 [%if-then-else (goal/c goal/c goal/c . -> . goal/c)]
 [%melt (unifiable? unifiable? . -> . goal/c)]
 [%melt-new (unifiable? unifiable? . -> . goal/c)]
 [%member (unifiable? unifiable? . -> . goal/c)]
 [%nonvar (unifiable? . -> . goal/c)]
 [%not (goal/c . -> . goal/c)]
 [%more (-> answer?)]
 [%repeat (-> goal/c)]
 [use-occurs-check? (parameter/c boolean?)]
 [%set-of (unifiable? goal/c unifiable? . -> . goal/c)]
 [%set-of-1 (unifiable? goal/c unifiable? . -> . goal/c)]
 [%true goal/c]
 [%var (unifiable? . -> . goal/c)]
 [_ (-> logic-var?)]) 
