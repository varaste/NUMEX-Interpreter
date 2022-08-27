#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file

;; definition of structures for NUMEX programs
;; expression types
(struct var     (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num     (int)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool    (b)      #:transparent)  ;; a constant boolean, e.g., (boolean #f)
(struct munit   ()       #:transparent)  ;; unit value -- good for ending a list
(struct apair   (e1 e2)  #:transparent)  ;; a constant pair of two numex expressions
(struct closure (env f)  #:transparent)  ;; a closure is not in "source" programs; it is what functions evaluate to
(struct plus  (e1 e2)  #:transparent)  ;; add two expressions
(struct minus (e1 e2)  #:transparent)  ;; minus two expressions
(struct mult  (e1 e2)  #:transparent)  ;; mult two expressions
(struct div   (e1 e2)  #:transparent)  ;; div two expressions
(struct neg     (e)     #:transparent)  ;; negative of an expression
(struct andalso (e1 e2) #:transparent)  ;; and two expressions
(struct orelse  (e1 e2) #:transparent)  ;; or two expressions
(struct 1st (xs) #:transparent) ;; selecting the first item from an apair
(struct 2nd (xs) #:transparent) ;; selecting the second item from an apair
(struct cnd     (e1 e2 e3)    #:transparent)  ;; condition on e1, resulting in e2 or e3
(struct iseq    (e1 e2)       #:transparent)  ;; checking equallity of params
(struct ifnzero (e1 e2 e3)    #:transparent)  ;; another type of condition
(struct ifleq   (e1 e2 e3 e4) #:transparent)  ;; conditioning on e1 being leq e2
(struct ismunit (e)           #:transparent)  ;; testing if an expression is munit
(struct lam     (nameopt formal body) #:transparent)  ;; a recursive(?) 1-argument function
(struct apply   (funexp actual)       #:transparent)  ;; function application
(struct with    (s e1 e2)             #:transparent)  ;; the masqueraded let function :D
(struct key  (s e) #:transparent) ;; key holds corresponding value of s which is e
(struct record (k r) #:transparent) ;; record holds several keys
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r
(struct letrec (s1 e1 s2 e2 e3) #:transparent) ;; a letrec expression for recursive definitions


;; Problem 1

(define (validate x)
  (cond
      [(var? x) (if (string? (var-string x)) x (error "Var content isn't string!"))]
      [(num? x) (if (integer? (num-int x)) x (error "Num content isn't integer!"))]
      [(bool? x) (if (boolean? (bool-b x)) x (error "Bool content isn't boolean!"))]
      [(munit? x) x]
      [(apair? x) x]
      [(closure? x) x] ;; TODO: is this correct?
      [else (error "Isn't a valid NUMEX expression.")]
  )
)

(define (racketlist->numexlist xs)
  (cond
    [(null? xs) (munit)]
    [(list? xs) (apair (car xs) (racketlist->numexlist (cdr xs)))]
    [(cons? xs) (apair (car xs) (cdr xs))]
    [else (error "Input of racketlist->numexlist must be a list or a cons!")]
  )
)

(define (numexlist->racketlist xs)
  (cond
    [(munit? xs) null]
    [(apair? xs) (cons (apair-e1 xs) (numexlist->racketlist (apair-e2 xs)))]
    [else (error "Input of numexlist->racketlist must be an apair!")]
  )
)

;; Problem 2
;; lookup a variable in an environment
(define (envlookup env str)
  (cond 
    [(null? env) (error "Unbound variable during evaluation" str)]
    [(equal? str (car (car env))) (cdr (car env))]
    [else (envlookup (cdr env) str)]
  )
)

;; checking types
(define (ct xs type_checker)
  (cond
    [(null? xs) xs]
    [(type_checker xs) xs]
    [(list? xs) (if (type_checker (car xs)) (cons (car xs) (ct (cdr xs) type_checker)) (error "Type didn't matched!" xs type_checker))]
    [(cons? xs) (if (type_checker (car xs)) (cons (car xs) (ct (cdr xs) type_checker)) (error "Type didn't matched!" xs type_checker))]
    [else (error "Input type not correct!" xs type_checker)]
  )
)

(define (if_eval_helper e1 e2 e3 env)
  (if (bool-b (ct (eval-under-env e1 env) bool?)) 
        (eval-under-env e2 env) 
        (eval-under-env e3 env)
  )
)

(define (eval-under-env e env)
  (cond 
    ;; expression types
    [(var? e) (envlookup env (var-string (validate e)))]
    [(num? e) (validate e)]
    [(bool? e) (validate e)]
    [(munit? e) e]
    [(apair? e) (apair (eval-under-env (apair-e1 e) env) (eval-under-env (apair-e2 e) env))]
    [(closure? e) (validate e)]




    
    [(plus? e) 
        (num (+
          (num-int (ct (eval-under-env (plus-e1 e) env) num?)) 
          (num-int (ct (eval-under-env (plus-e2 e) env) num?))
        ))]

    [(minus? e) 
        (num (-
          (num-int (ct (eval-under-env (minus-e1 e) env) num?)) 
          (num-int (ct (eval-under-env (minus-e2 e) env) num?))
        ))]

    [(mult? e)
        (num (* 
          (num-int (ct (eval-under-env (mult-e1 e) env) num?)) 
          (num-int (ct (eval-under-env (mult-e2 e) env) num?))
        ))]

    [(div? e) 
        (let ([v (ct (eval-under-env (div-e2 e) env) num?)])
            (if (eq? 0 (num-int v)) (error "Division by zero!")  
              (num (quotient
                  (num-int (ct (eval-under-env (div-e1 e) env) num?)) (num-int v)
              ))
            )
        )]
    
    ;; logical functions
    [(neg? e)
      (let ([v (eval-under-env (neg-e e) env)])
        (cond
          [(bool? v) (bool (not (bool-b (ct v bool?))))]
          [(num? v) (num (- (num-int (ct v num?))))]
          [else (error "Type must be either bool or num!" e)]
        )  
      )]
    
    [(andalso? e)
        (bool (and 
          (bool-b (ct (eval-under-env (andalso-e1 e) env) bool?)) 
          (bool-b (ct (eval-under-env (andalso-e2 e) env) bool?)) 
        ))]
    
    [(orelse? e) 
        (bool (or 
          (bool-b (ct (eval-under-env (orelse-e1 e) env) bool?)) 
          (bool-b (ct (eval-under-env (orelse-e2 e) env) bool?)) 
        ))]

    ;;12
    [(1st? e) (apair-e1 (ct (eval-under-env (1st-xs e) env) apair?))]
    
    [(2nd? e) (apair-e2 (ct (eval-under-env (2nd-xs e) env) apair?))]

    
    ;; tester functions
    [(cnd? e) (if_eval_helper (cnd-e1 e) (cnd-e2 e) (cnd-e3 e) env)]
    
    [(iseq? e) 
        (let ([v1 (eval-under-env (iseq-e1 e) env)]
              [v2 (eval-under-env (iseq-e2 e) env)])
          (cond
            [(apair? v1)
              (if (apair? v2)
                (let ([a11 (eval-under-env (apair-e1 v1) env)] [a12 (eval-under-env (apair-e2 v1) env)]
                      [a21 (eval-under-env (apair-e1 v2) env)] [a22 (eval-under-env (apair-e2 v2) env)])
                  (bool (and
                    (equal? a11 a21)
                    (equal? a12 a22)
                  ))
                )
                (bool #f)
              )]
            [else (bool (equal? v1 v2))]
          )
        )]

    [(ifnzero? e) 
        (let ([v (if (eq? 0 (num-int (ct (eval-under-env (ifnzero-e1 e) env) num?))) (bool #f) (bool #t))]) 
            (if_eval_helper v (ifnzero-e2 e) (ifnzero-e3 e) env)
        )]
    
    [(ifleq? e) 
        (let ([v1 (num-int (ct (eval-under-env (ifleq-e1 e) env) num?))])
            (let ([v (if (<= v1 (num-int (ct (eval-under-env (ifleq-e2 e) env) num?))) (bool #t) (bool #f))]) 
              (if_eval_helper v (ifleq-e3 e) (ifleq-e4 e) env)
            )
        )]

    [(ismunit? e) (bool (munit? (eval-under-env (ismunit-e e) env)))]

    [(key? e)
         (if (string? (key-s e))
             (let ([exp (eval-under-env (key-e e) env)])
               (key (key-s e) exp)
               )
             (error "NUMEX key argument s should be of type racket string")
             )
         ]
    
    ;; functional language specific functions

    [(lam? e) 
        (if (and (or (string? (lam-nameopt e)) (null? (lam-nameopt e))) (string? (lam-formal e)))
             (closure env e)
             (error "NUMEX function name and parameter name must be string")
        )]
    
    [(apply? e)
        (let ([v (eval-under-env (apply-actual e) env)]
              [clsr (ct (eval-under-env (apply-funexp e) env) closure?)])
            (let ([clsr_fun (closure-f clsr)])
              (if (null? (lam-nameopt clsr_fun))
                (eval-under-env (lam-body clsr_fun) (cons (cons (lam-formal clsr_fun) v) (closure-env clsr)))
                (eval-under-env (lam-body clsr_fun) (cons (cons (lam-nameopt clsr_fun) clsr) 
                    (cons (cons (lam-formal clsr_fun) v) (closure-env clsr))))
              )
            )
        )]
    [(with? e) 
        (let ([s (ct (with-s e) string?)] 
              [v (eval-under-env (with-e1 e) env)])
           (eval-under-env (with-e2 e) (append (list (cons s v)) env))
        )]
    
    [(isbool? e) (bool (bool? (eval-under-env (isbool-b e) env)))]


    
    [(record? e)
     (let ( [eK (eval-under-env (record-k e) env)]
            [eR (eval-under-env (record-r e) env)])
       (if (and (key? eK) (or (munit? eR) (record? eR)))
           e
           (error "REC ERROR")))]

    
    [(value? e)
     (let ([eR (eval-under-env (value-r e) env)])
       (if (record? eR)
           (if (eq? (value-s e) (key-s (record-k (value-r e))))
              (eval-under-env (key-e (record-k (value-r e))) env)
              (if (munit? (record-r (value-r e)))
                  (munit)
                  (eval-under-env (value (value-s e) (record-r(value-r e))) env)))
       (error "VAL ERROR" )))]
;;   ::((
    [(letrec? e)
          (eval-under-env (letrec-e3 e)
              (cons (cons (letrec-s1 e) (letrec-e1 e))
              (cons (cons (letrec-s2 e) (letrec-e2 e)) env)))]
        

    
    [else (error (format "bad NUMEX expression: ~v" e))]
  )
)





;; evaluating expressions
(define (eval-exp e) (eval-under-env e null))
        
;; Problem 3

(define (ifmunit e1 e2 e3) (cnd (ismunit e1) e2 e3))

(define (with* bs e) 
  (cond
    [(null? bs) e]
    [else (with (caar bs) (cdar bs) (with* (cdr bs) e))]
  )
)


(define (ifneq e1 e2 e3 e4)
  (cnd (iseq e1 e2) e4 e3)
 )

;; Problem 4

(struct isbool (b) #:transparent)


(define (fun x)x )
 

(define numex-filter 
  (lam null "mapper" 
    (lam "map" "xs" 
      (cnd (ismunit (var "xs")) 
        (munit)
        (with "result" (apply (var "mapper") (1st (var "xs"))) 
          (ifnzero (var "result")
            (apair (var "result") (apply (var "map") (2nd (var "xs"))))
            (apply (var "map") (2nd (var "xs")))
          )
        )
      )
    )
  )
)

(define numex-all-gt
  (with "filter" numex-filter
    (lam null "i"
      (lam null "list"
        (apply 
          (apply (var "filter") (lam null "number"
            (ifleq (var "number") (var "i")
              (num 0)
              (var "number") ;; what if number was 0?
            )
          ))
          (var "list")
        )
      )
    )
  )
)

