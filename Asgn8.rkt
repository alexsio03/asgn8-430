#lang typed/racket

(require typed/rackunit)

;; ExprC struct definitions
(define-type ExprC (U numC idC strC ifC blamC appC recC))
(struct numC ([n : Real]) #:transparent)
(struct idC ([s : Symbol]) #:transparent)
(struct strC ([str : String]) #:transparent)
(struct ifC ([check : ExprC] [true : ExprC] [false : ExprC]) #:transparent)
(struct blamC ([params : (Listof idC)] [paramT : (Listof Type)] [body : ExprC]) #:transparent)
(struct appC ([func : ExprC] [args : (Listof ExprC)]) #:transparent)
(struct recC ([func : ExprC] [func-params : (Listof idC)] [func-paramT : (Listof Type)]
                             [fname : idC] [retT : Type] [body : ExprC]) #:transparent)

;; Value struct definitions
(define-type Value (U numV closV strV boolV primopV))
(struct numV ([n : Real]) #:transparent)
(struct boolV ([b : Boolean]) #:transparent)
(struct strV ([str : String]) #:transparent)
(struct closV ([params : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primopV ([op : Symbol] [arity : Real] [env : Env]) #:transparent)

;; Type definitions
(define-type Type (U numT strT boolT funT))
(struct numT () #:transparent)
(struct strT () #:transparent)
(struct boolT () #:transparent)
(struct funT ([args : (Listof Type)] [ret : Type]) #:transparent)

;; Binding/Env definitions
(struct Binding ([key : Symbol] [val : (Boxof Value)]) #:transparent)
(define-type Env (Listof Binding))

;; Type Binding/Type Env definitions
(struct TBinding ([key : Symbol] [type : Type]) #:transparent)
(define-type TEnv (Listof TBinding))

; The top type environment
(define (create-base-tenv) : TEnv
  (list
   (TBinding 'true (boolT))
   (TBinding 'false (boolT))
   (TBinding '+ (funT (list (numT) (numT)) (numT)))
   (TBinding '* (funT (list (numT) (numT)) (numT)))
   (TBinding '- (funT (list (numT) (numT)) (numT)))
   (TBinding '/ (funT (list (numT) (numT)) (numT)))
   (TBinding '<= (funT (list (numT) (numT)) (boolT)))
   (TBinding 'num-eq? (funT (list (numT) (numT)) (boolT)))
   (TBinding 'str-eq? (funT (list (strT) (strT)) (boolT)))
   (TBinding 'substring (funT (list (strT) (numT) (numT)) (strT)))))

; The top environment with primop bindings
(define vbox (inst box Value))
(define (create-top-env) : Env
  (list
   (Binding 'true (vbox (boolV true)))
   (Binding 'false (vbox (boolV false)))
   (Binding '+ (vbox (primopV '+ 2 '())))
   (Binding '* (vbox (primopV '* 2 '())))
   (Binding '- (vbox (primopV '- 2 '())))
   (Binding '/ (vbox (primopV '/ 2 '())))
   (Binding '<= (vbox (primopV '<= 2 '())))
   (Binding 'num-eq? (vbox (primopV 'num-eq? 2 '())))
   (Binding 'str-eq? (vbox (primopV 'str-eq? 2 '())))
   (Binding 'substring (vbox (primopV 'substring 3 '())))))

(define top-env (create-top-env))
(define base-tenv (create-base-tenv))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; interpreters and helper functions

; Purpose: The main interpreter of the PAIG language which takes in an ExprC type and an
; environment with bindings, and interprets the ExprC into a Value
(define (interp (e : ExprC) (env : Env)) : Value
  (match e
    [(numC n) (numV n)]
    [(strC str) (strV str)]
    [(idC s) (lookup s env)]
    [(ifC c t f)
     (match (interp c env)
       [(boolV b)
        (match b
          [#t (interp t env)]
          [#f (interp f env)])])]
    [(blamC params param-types b) (closV ((inst map Symbol idC) idC-s params) b env)]
    [(appC f vals)
     (match (interp f env)
       [(closV params body e) (interp body (append (bind params
                                            ((inst map (Boxof Value) ExprC)
                                             (λ (x) (vbox (interp x env))) vals)) e))]
       [(primopV op ar e)
        (match (equal? ar (length vals))
          [#t
           (match ar
             [3 (match op
             ['substring (strV (substr (interp (first vals) env) (interp (second vals) env)
                                       (interp (third vals) env)))])]
             [2 (eval (primopV op ar env)
                      (interp (first vals) env) (interp (second vals) env))])])])]
    [(recC f fp fpT fn rT body)
     (define bogus (vbox (numV 0)))
     (define ext-env (append env (bind (list (idC-s fn)) (list bogus))))
     (define clo (interp f ext-env))
     (set-box! bogus clo)
     (interp body ext-env)]))

; Purpose: Takes in a string, a start index, and an end index, and returns
; the string from index start to index end.
(define (substr (str : Value) (start : Value) (end : Value)) : String
    (match (and (strV? str) (numV? start) (numV? end))
       [#t (cond
       [(and (natural? (numV-n start)) (natural? (numV-n end)))
        (substring (strV-str str) (numV-n start) (numV-n end))]
       [else (error 'substring "(PAIG) indexes must be natural numbers")])]))

; Purpose: A helper function used to evalueate primitive operators, which takes in a primopV as well
; as two arguments, and interprets the whole expression into a Value based on the primop's identifier
(define (eval (prim : primopV) (arg1 : Value) (arg2 : Value)) : Value
  (match (and (numV? arg1) (numV? arg2))
    [#t
     (match (primopV-op prim)
       ['+ (numV (+ (numV-n arg1) (numV-n arg2)))]
       ['* (numV (* (numV-n arg1) (numV-n arg2)))]
       ['- (numV (- (numV-n arg1) (numV-n arg2)))]
       ['/
        (match arg2
          [(numV 0) (error 'eval "(PAIG) Cannot divide by zero")]
          [other (numV (/ (numV-n arg1) (numV-n arg2)))])]
       ['<= (boolV (<= (numV-n arg1) (numV-n arg2)))]
       ['num-eq? (boolV (equal? (numV-n arg1) (numV-n arg2)))])]
    [#f (match (and (strV? arg1) (strV? arg2))
                    [#t (match (primopV-op prim)
                          ['str-eq? (boolV (equal? (strV-str arg1) (strV-str arg2)))])])]))

; Purpose: A helper function which takes a list of parameters and values, and returns a list of
; Binding types with each parameter at index i bound to each value at index i of either list
(define (bind (params : (Listof Symbol)) (vals : (Listof (Boxof Value)))) : (Listof Binding) 
  (match params
       ['() '()]
       [(cons f r) (cons (Binding f (first vals)) (bind r (rest vals)))]))

; Purpose: A helper function which takes a list of parameters and types, and returns a list of
; TBinding types with each parameter at index i bound to each type at index i of either list
(define (tbind (vars : (Listof idC)) (types : (Listof Type))) : (Listof TBinding)
  (match vars
       ['() '()]
       [(cons f r) (cons (TBinding (idC-s f) (first types)) (tbind r (rest types)))]))

; Purpose: A helper function which takes in a symbol and an environment and searches the environment.
; If the symbol is found, it returns the value bound to that symbol in the environment, else it errors
(define (lookup [var : Symbol] [env : Env]) : Value
  (match env
    [other (cond
             [(symbol=? var (Binding-key (first env)))
              (unbox (Binding-val (first env)))]
             [else (lookup var (rest env))])]))

; Purpose: A helper function which takes in a symbol and the base-tenvironment and searches the env. If
; the symbol is found, it returns its type. Errors otherwise.
(define (tlookup [var : Symbol] [env : TEnv]) : Type
  (match env
    ['() (error 'tlookup "(PAIG) unbound identifier: ~e" var)]
    [other (cond
             [(symbol=? var (TBinding-key (first env)))
              (TBinding-type (first env))]
             [else (tlookup var (rest env))])]))

; Purpose: The top-interp function which takes in an s-expression and returns the evaluated and serialized
; program in a String
(define (top-interp [s : Sexp]) : String
  (define expr (parse s))
  (type-check expr base-tenv)
  (serialize (interp expr top-env)))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; type checker and helper functions

; Purpose: The type checker takes in an expression and the top-level type environment
; and returns each type declared matches each type given, errors otherwise
(define (type-check (e : ExprC) (env : TEnv)) : Type
  (match e
    [(numC n) (numT)]
    [(strC s) (strT)]
    [(idC s) (tlookup s env)]
    [(ifC c t f)
     (match (equal? (type-check f env) (type-check t env))
       [#t (match (type-check c env)
             [(boolT) (type-check t env)]
             [other (error 'type-check "(PAIG) Condition is not a boolean")])]
       [#f (error 'type-check "(PAIG) Types not matching~n
                    ~e != ~e" (type-check f env) (type-check t env))])]
    [(appC func args)
     (match (type-check func env)
       [(funT argsT retT)
        (match (equal? (length args) (length argsT))
          [#t (match (check-arg-types args argsT env)
                [#t retT])]
          [#f (error 'type-check "(PAIG) Invalid number of arguments")])]
       [other (error 'type-check "(PAIG) not a function: ~e" func)])]
    [(blamC p pT b) (funT pT (type-check b (append env (tbind p pT))))]
    [(recC func fp fpT fname retT b)
     (match func
       [(blamC p pT body)
        (match (equal? (type-check body
           (append env (tbind p pT) (tbind (list fname) (list (funT fpT retT))))) retT)
          [#t (type-check b (append env (tbind (list fname) (list (funT fpT retT)))))]
          [#f (error 'type-check "(PAIG) Given return type and body return type do not match")])])]))

; Purpose: A helper function for the type checker that makes sure the arguments passed in
; match the types given in a function declaration
(define (check-arg-types (args : (Listof ExprC)) (argsT : (Listof Type)) (env : TEnv)) : Boolean
  (match args
    ['() #t]
    [(cons f r)
     (match (equal? (type-check f env) (first argsT))
       [#t (check-arg-types r (rest argsT) env)]
       [#f (error 'check-arg-types "(PAIG) Type mismatch~n
       ~e != ~e" (type-check f env) (first argsT))])]))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; parser and helper functions

; Purpose: Takes in an s-expression and parses it into an ExprC type
(define (parse (s : Sexp)) : ExprC
  (match s
    [(? real? n) (numC n)]
    [(? symbol? s) (check-sym s)]
    [(? string? str) (strC str)]
    [(list c '? t 'else: f) (ifC (parse c) (parse t) (parse f))];ifC
    [(list 'blam (list p ...) b) (blamC (check-dupes ((inst map idC Sexp) parse-params p))
                                        ((inst map Type Sexp) parse-param-types p) (parse b))];blamC
    [(list 'with subs ... ': func) 
     (appC (blamC (check-dupes ((inst map idC Any) get-var subs))
                  ((inst map Type Any) get-var-type subs) (parse func))
           ((inst map ExprC Any) get-val subs))]
    [(list 'rec [list blam 'as (? symbol? id) 'returning ty] ': body)
     (match (parse blam)
       [(blamC p pT r) (recC (parse blam) p pT (check-sym id) (parse-type ty) (parse body))]
       [other (error 'parse "(PAIG) Recursive function must be blam")])]
    [(list func1 func2 ...) (appC (parse func1) ((inst map ExprC Sexp) parse func2))]));appC

; Purpose: A parsing function that determines the type of a variable based on the
; keyword passed in the s-expression
(define (parse-type (s : Any)) : Type
  (match s
    ['num (numT)]
    ['str (strT)]
    ['bool (boolT)]
    [(list x ... '-> r) (funT ((inst map Type Any) parse-type x) (parse-type r))]
    [other (error 'parse-type "(PAIG) Types can only be num, str, or bool, not: ~e" s)]))

; Purpose: A helper function for the parser which takes in a list of idC's and makes sure
; each idC only appears once. Errors if there is a duplicate, returns the list of not.
(define (check-dupes (lst : (Listof idC))) : (Listof idC)
  (match lst
    ['() '()]
    [(cons f r)
     (match (member f r)
       [#f (cons f (check-dupes r))]
       [else (error 'check-dupes "(PAIG) Duplicate identifier: ~v" (idC-s f))])]))

; Purpose: A helper function for the parser which takes in a symbol and makes sure it is
; not a restricted symbol. Errors on failure, return's an idC with given symbol on success.
(define (check-sym (s : Symbol)) : idC
  (match s
       [(or '? 'with 'as 'blam 'else: 'rec 'returning '->) (error 'parse "(PAIG) invalid identifier: ~e" s)]
       [other (idC other)]))

; Purpose: A helper function for the parser which takes in a [val as var] from a 'with'
; statement, and returns the var as an idC
(define (get-var (s : Any)) : idC
  (match s
    [(list val 'as (? symbol? var) ': t) (check-sym var)]
    [other (error 'get-var "(PAIG) invalid form of blam: ~e" s)]))

; Purpose: A helper function for the parser which takes in a variable from a 'with'
; statement and returns the type
(define (get-var-type (s : Any)) : Type
  (match s
    [(list val 'as (? symbol? var) ': t) (parse-type t)]))

; Purpose: A helper function for the parser which takes in a [val as var] from a 'with'
; statement, and returns a parsed version of the val
(define (get-val (s : Any)) : ExprC
  (match s
    [(list val 'as (? symbol? var) ': t) (parse (cast val Sexp))]))

; Purpose: A helper function for the parser which takes in an s-expression from the 'blam'
; and ensures all parameters passed were symbols
(define (parse-params (s : Sexp)) : idC
  (match s
    [(list (? symbol? s) ': t) (check-sym s)]
    [other (error 'parse-params "(PAIG) Parameters must be symbols, given: ~v" s)]))

(define (parse-param-types (s : Sexp)) : Type
  (match s
    [(list s ': t) (parse-type t)]))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; serialize

; Purpose: The serialize function which takes in a Value and returns the serialized version of that
; value as a String
(define (serialize (v : Value)) : String
  (match v
    [(numV n) (format "~v" n)]
    [(boolV b)
     (match b
       [#t "true"]
       [#f "false"])]
    [(strV str) (format "~v" str)]
    [(closV prms b e) "#<procedure>"]
    [(primopV op ar e) "#<primop>"]))

;-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
; tests

(check-equal? (type-check (parse '{rec [{blam {[n : num]} {{<= n 0} ? 0 else: {+ n {square-helper {- n 2}}}}}
     as square-helper returning num]
 :
 {with [{blam {[n : num]} {square-helper {- {* 2 n} 1}}}
        as square : {num -> num}]
       :
       {square 13}}}) base-tenv) (numT))

(check-equal? (top-interp '{rec [{blam {[n : num]} {{<= n 0} ? 0 else: {+ n {square-helper {- n 2}}}}}
     as square-helper returning num]
 :
 {with [{blam {[n : num]} {square-helper {- {* 2 n} 1}}}
        as square : {num -> num}]
       :
       {square 12}}}) "144")

(check-equal? (top-interp '{rec [{blam {[n : num]} {{<= n 0} ? 0 else: {+ n {addup {- n 1}}}}}
                                 as addup returning num] : {addup 10}}) "55")

(check-equal? (top-interp '{{<= 5 10} ? "less" else: "more"}) "\"less\"")

; substring tests
(check-equal? (top-interp '{substring "hello world" 6 11}) "\"world\"")
(check-exn (regexp (regexp-quote "check-arg-types: (PAIG) Type mismatch\n\n       (strT) != (numT)"))
           (lambda () (top-interp '{substring "hello world" "wrong" 11})))
(check-exn (regexp (regexp-quote "substring: (PAIG) indexes must be natural numbers"))
           (lambda () (top-interp '{substring "hello world" 2.5 11})))

(check-exn (regexp (regexp-quote "type-check: (PAIG) Types not matching

                    (strT) != (numT)"))
           (lambda () (top-interp '{{<= 5 10} ? 10 else: "more"})))

(check-exn (regexp (regexp-quote "type-check: (PAIG) not a function: (numC 3)"))
           (lambda () (top-interp '{3 4 5})))

(check-exn (regexp (regexp-quote "type-check: (PAIG) Invalid number of arguments"))
           (lambda () (top-interp '{+ 3 4 5})))

(check-exn (regexp (regexp-quote "eval: (PAIG) Cannot divide by zero"))
           (lambda () (top-interp '{/ 3 0})))

(check-exn (regexp (regexp-quote "tlookup: (PAIG) unbound identifier: 'y"))
           (lambda () (top-interp '{{blam {[x : num]} {+ x y}} 2})))

(check-exn (regexp (regexp-quote "check-dupes: (PAIG) Duplicate identifier: 'x"))
           (lambda () (parse '(blam ([x : num] [x : num]) 3))))

(check-exn (regexp (regexp-quote "parse: (PAIG) Recursive function must be blam"))
           (lambda () (top-interp '{rec [{+ 1 2} as f returning num] : f})))

(check-exn (regexp (regexp-quote "parse-type: (PAIG) Types can only be num, str, or bool, not: 'number"))
           (lambda () (parse '{blam {[x : number]} {* x 2}})))

(check-exn (regexp (regexp-quote "parse: (PAIG) invalid identifier: '?"))
           (lambda () (parse '{blam {[? : number]} {* ? 2}})))

(check-exn (regexp (regexp-quote "type-check: (PAIG) Condition is not a boolean"))
           (lambda () (type-check (parse '(4 ? "abc" else: "def")) base-tenv)))

(check-exn (regexp (regexp-quote
                    "parse-params: (PAIG) Parameters must be symbols, given: '(\"var\" : num)"))
           (lambda () (parse '{blam {["var" : num]} {* "var" 2}})))

(check-exn (regexp (regexp-quote
                    "get-var: (PAIG) invalid form of blam: '((blam () 3) as z)"))
           (lambda () (top-interp '(with ((blam () 3) as z) (9 as z) : (z)))))

(check-exn (regexp (regexp-quote
                    "type-check: (PAIG) Given return type and body return type do not match"))
           (lambda () (type-check (parse '(rec ((blam ((c : num)) "abc") as a returning num) : 13)) base-tenv)))

(check-equal? (top-interp '{blam {[x : num]} {* x 2}}) "#<procedure>")
(check-equal? (parse '{blam {[x : bool]} {* x 2}})
              (blamC (list (idC 'x)) (list (boolT)) (appC (idC '*) (list (idC 'x) (numC 2)))))
(check-equal? (type-check (parse '{{<= 5 10} ? "good" else: "bad"}) base-tenv) (strT))
(check-equal? (type-check (parse '{rec [{blam {[x : num]} {* x 2}} as f returning num] :
          {with [{blam {[n : num]} {f n}} as call : {num -> num}] :
                {call 10}}}) base-tenv) (numT))
(check-equal? (parse '{with [{blam {[x : num]} {* x 2}} as f : num] : {f 7}}) (appC
 (blamC (list (idC 'f)) (list (numT)) (appC (idC 'f) (list (numC 7))))
 (list (blamC (list (idC 'x)) (list (numT)) (appC (idC '*) (list (idC 'x) (numC 2)))))))
(check-equal? (type-check (parse '{with [{blam {[x : num]} {* x 2}} as f : {num -> num}] : {f 7}}) base-tenv) (numT))
(check-equal? (type-check (parse '{with [{blam {[x : num]} {blam {[y : num]} {+ x y}}} as f : {num -> {num -> num}}]
                                        : {{f 3} 7}}) base-tenv) (numT))
(check-equal? (type-check (parse '{{blam {[x : num] [y : num]} {* x y}} 5 3}) base-tenv) (numT))
(check-equal? (type-check (parse '{<= 10 50}) base-tenv) (boolT))
(check-equal? (top-interp '{{blam {[x : num] [y : num]} {* x y}} 5 3}) "15")
(check-equal? (top-interp '{{blam {[x : num] [y : num]} {/ x y}} 10 2}) "5")
(check-equal? (top-interp '{{blam {[x : num] [y : num]} {- x y}} 2 2}) "0")
(check-equal? (top-interp '{{blam {[x : num] [y : num]} {num-eq? x y}} 2 2}) "true")
(check-equal? (top-interp '{{blam {[x : str] [y : str]} {str-eq? x y}} "one" "two"}) "false")
(check-equal? (serialize (primopV '+ 2 '())) "#<primop>")