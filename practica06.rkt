#|
Compiladores 2022-1  Practica 06
Tabla de simbolos.
Alumnos:
- Acosta Meza Alam
  No.cuenta : 315124569
- Arroyo Rivera Juan José
  No.cuenta: 416053223
- Sierra Casiano Vladimir
  No.cuenta: 316020361
|#


#lang nanopass


;; Predicados para los terminales
(define (variable? x) (and (symbol? x) (not (primitive? x)) (not (constant? x))) )

(define (primitive? x) (memq x '(+ - * / length car cdr)))

(define (constant? x) (or (integer? x) (char? x) (boolean? x)))

;; Definimos el sistema de tipos
(define (type? x) (or (b-type? x) (c-type? x)))

(define (b-type? x) (memq x '(Bool Char Int List Lambda)))

(define (c-type? x)
    (if (list? x)
        (let* ( [f (car x)] [s (cadr x)] [t (caddr x)])
            (or (and (equal? f 'List) (equal? s 'of) (type? t))
                (and (type? f) (equal? s '->) (type? t))))
        #f))

(define (arit? x) (memq x '(+ - * /)))

(define (lst? x) (memq x '(length car cdr)))


;; Definimos el lenguaje
(require nanopass/base)
(define-language L10
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (type (t)))
   (Expr (e body)
         x
         (const t c)
         (begin e* ... e)
         (primapp pr e* ...)
         (if e0 e1 e2 )
         (lambda ([x t]) body)
         (let ([x t e]) body)
         (letrec ([x t e]) body)
         (letfun ([x t e]) body)
         (list e* ...)
         (e0 e1 )))

;; Parser de l10
(define-parser parse-L10 L10)

;; EJERCICIO 1 =====================

;;Primero definimos un nuevo lenguaje L11 para que las lambda sean multiparametricas
(define-language L11
    (extends L10)
    (Expr (e body)
          (- (lambda ([x t]) body))
          (+ (lambda ([x* t*] ...) body))))

;; Definimos su parser
(define-parser parse-L11 L11)

;; Definimos un pass auxiliar para identificar lambdas
(define-pass lambda? : (L10 Expr) (e) -> * (bool)
    (Expr : Expr (e) -> * (bool)
        [(lambda ([,x ,t]) ,body) #t]
        [else #f])
    (Expr e))

;; Funcion auxiliar que devuelve el body de una expresion lambda
(define (get-body-lambda expr)
    (nanopass-case (L10 Expr) expr
        [(lambda ([,x ,t]) ,body) (get-body-lambda body)]
        [else expr]))

;; Funcion auxiliar para obtener la lista de asignaciones que se hacen en una expression lambda dada
(define (get-assigments-lambda expr acum)
    (nanopass-case (L10 Expr) expr
        [(lambda ([,x ,t]) ,body)  (append (list (list x t)) (get-assigments-lambda body acum)) ]
        [else acum]))

(define (uncurry-aux expr)
    (nanopass-case (L10 Expr) expr
        [(lambda ([,x ,t]) ,body)
            (parse-L11 `(lambda ,(get-assigments-lambda expr '()) ,(unparse-L11 (uncurry-aux (get-body-lambda expr)))))]
        [(let ([,x ,t ,[e]]) ,[body])
            (with-output-language (L11 Expr) `(let ([,x ,t ,e]) ,body))]
        [(letrec ([,x ,t ,[e]]) ,[body])
            (with-output-language (L11 Expr) `(letrec ([,x ,t ,e]) ,body))]
        [(letfun ([,x ,t ,[e]]) ,[body])
            (with-output-language (L11 Expr) `(letfun ([,x ,t ,e]) ,body))]
        [(begin ,[e*] ... ,[e])
            (with-output-language (L11 Expr) `(begin ,e* ... ,e))]
        [(primapp ,pr ,[e*] ...)
            (with-output-language (L11 Expr) `(primapp ,pr ,e* ...))]
        [(if ,[e0] ,[e1] ,[e2])
            (with-output-language (L11 Expr) `(if ,e0 ,e1 ,e2))]
        [(const ,t ,c)
            (with-output-language (L11 Expr) `(const ,t ,c))]
        [(list ,[e*] ...)
            (with-output-language (L11 Expr) `(list ,e* ...))]
        [(,[e0] ,[e1])
            (with-output-language (L11 Expr) `(,e0 ,e1))]
        [else (parse-L11 (unparse-L10 expr))] ))

(define-pass uncurry : L10 (ir) -> L11 ()
    (Expr : Expr (ir) -> Expr ())
        (uncurry-aux ir))

;;Ejemplos Ejercicio 1
(printf "\nEjemplos Ejercicio 1:\n")
(printf "\nInput: (uncurry (parse-L10 '(lambda ([x Int]) (lambda ([y Int]) (lambda ([z Int]) (primapp + x y z))))))" )
(printf "\nOutput:")
(uncurry (parse-L10  '(lambda ([x Int]) (lambda ([y Int]) (lambda ([z Int]) (primapp + x y z))))))

(printf "\nInput: (uncurry (parse-L10 '(lambda ([x Int]) (lambda ([y Int]) (letfun ([foo (Int → Int → Int) (lambda ([z Int]) (lambda ([w Int])
(primapp + x y z w)))]) ((foo (const Int 4)) (const Int 2)))))))" )
(printf "\nOutput:")
(uncurry (parse-L10 '(lambda ([x Int]) (lambda ([y Int]) (letfun ([foo (Int -> Int -> Int) (lambda ([z Int]) (lambda ([w Int])
(primapp + x y z w)))]) ((foo (const Int 4)) (const Int 2)))))))

;; EJERCICIO 2 ========================================

(define (symbol-table-var-aux expr table)
    (nanopass-case (L11 Expr) expr
        [(let ([,x ,t ,[e] ]) ,body)
            (begin (hash-set! table x (cons t e))
                    (symbol-table-var-aux body table))]
        [(letrec ([,x ,t ,e]) ,body)
            (begin (hash-set! (symbol-table-var-aux body table) x (cons t e))
                    (symbol-table-var-aux body table))]
        [(letfun ([,x ,t ,e]) ,body)
            (begin (hash-set! table x (cons t e))
                    (symbol-table-var-aux body table))]
        [(,e0 ,e1)
            (begin
                (define h1 table)
                (set! h1 (symbol-table-var-aux e1 h1))
                (define h2 h1)
                (set! h2 (symbol-table-var-aux e1 h2))
                h2)]
        [(primapp ,pr ,[e*] ...)
            (let f ([e* e*]) (if (null? e*) table (symbol-table-var-aux (first e*) (f (rest e*)))))]
        [(begin ,e* ... ,e)
            (begin (map (lambda (e) (symbol-table-var-aux e table)) e*))]
        [(if ,e0 ,e1 ,e2)
            (begin
                (symbol-table-var-aux e0 table)
                (symbol-table-var-aux e1 table)
                (symbol-table-var-aux e2 table))]
        [(lambda ([,x* ,t*] ...) ,body) (symbol-table-var-aux body table)]
        [(list ,e* ... ,e)
            (begin (map (lambda (e) (symbol-table-var-aux e table)) e*) (symbol-table-var-aux e table))]
        [else table] ))

;; Funcion que genera la tabla de simbolos de una expresión
(define (symbol-table-var expr)
    (nanopass-case (L11 Expr) expr
                    [else (symbol-table-var-aux expr (make-hash))]))

;;Ejemplos Ejercicio 2
(printf "\nEjemplos Ejercicio 2:\n")
(printf "\nInput: (symbol-table-var (parse-L11 '(letrec ([x Int (const Int 5)]) (letrec ([y Int (const Int 4)]) (primapp + x y (const Int 2))))))" )
(printf "\nOutput:")
(symbol-table-var (parse-L11 '(letrec ([x Int (const Int 5)]) (letrec ([y Int (const Int 4)]) (primapp + x y (const Int 2))))))

(printf "\nInput: (symbol-table-var (parse-L11 '(if (const Bool #t) (const Int 3) (letfun (foo (Int → Int → Int) (lambda ([x Int]
[y Int]) (primapp + x y))]) ((foo (const Int 1)) (const Int 2))))))" )
(printf "\nOutput:")
(symbol-table-var (parse-L11 '(if (const Bool #t) (const Int 3) (letfun ([foo (Int -> Int -> Int) (lambda ([x Int] [y Int]) (primapp + x y))]) ((foo (const Int 1)) (const Int 2))))))

;; EJERCICIO 3 =====================

(define-language L12
  (extends L11)
  (Expr (e body)
        (- (let ([x t e]) body)
           (letrec ([x t e]) body)
           (letfun ([x t e]) body))
        (+ (let x body)
           (letrec x body)
           (letfun x body))))

;; Parser L12
(define-parser parse-L12 L12)

;; Función que elimina el valor asociado a cada identificador y su tipo
(define-pass assigment : L11 (ir) -> L12 (hash)
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,e]) ,[body]) `(let ,x ,body)]
        [(letrec ([,x ,t ,e]) ,[body]) `(letrec ,x ,body)]
        [(letrec ([,x ,t ,e]) ,[body]) `(letfun ,x ,body)])
  (values (Expr ir) (symbol-table-var ir)))

;;Ejemplos Ejercicio 3
(printf "\nEjemplos Ejercicio 3:\n")
(printf "\nInput: (assigment (parse-L11 '(letrec ([foo (Int -> Int) (lambda ([x Int]) x)]) (foo (const Int 5)))))" )
(printf "\nOutput:")
(assigment (parse-L11 '(letrec ([foo (Int -> Int) (lambda ([x Int]) x)]) (foo (const Int 5)))))

(printf "\nInput: (assigment (parse-L11 '(let ([x Int (primapp * (const Int 40) (const Int 20))]) (primapp cdr x))))" )
(printf "\nOutput:")
(assigment (parse-L11 '(let ([x Int (primapp * (const Int 40) (const Int 20))]) (primapp cdr x))))





;; ==== EJERCICIO 4 ================================


;; Definimos el lenguaje
(define-language L13
    (extends L12)
    (Expr (e body)
        (- (list e* ...))
        (+ (array c t [e* ...]))))

(define-parser parse-L13 L13)


;; Funcion que dada una lista toma el primer elemento y aplica sobre ese elemento el algoritmo J
(define (J-aux x)
    (nanopass-case (L12 Expr) x
        [(list ,e* ... ,e) (J e '())] ))


;; Pass que pasa las listas a arreglos
(define-pass list-to-array : L12 (ir) -> L13 ()
 (Expr : Expr (ir) -> Expr()
    [ (list ,[e*] ...)
        (let ([t (J-aux ir)])
        `(array ,(length e*)  ,t  [,e* ...] )) ] ))








;; ================== Algoritmo auxiliar. Algoritmo J ===============================



;; PRIMERO DEFINIREMOS UNAS FUNCIONES AUXILIARES



;; Definimos la funcion unify
(define (unify t1 t2)
    (if (and (type? t1) (type? t2))
        (cond
            [(equal? t1 t2) #t]
            [(and (equal? 'List t1) (list? t2))  (equal? (car t2) 'List) ]
            [(and (equal? 'List t2) (list? t1))  (equal? (car t1) 'List) ]
            [(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)))]
            [else #f])
        (error "Se esperaban 2 tipos")))

;; Unas funciones auxiliares para realizar la busqueda de variables en el ambiente
(define (find-type x env)
    (cond
        [(empty? env) (error "Error, variable no esta en el ambiente")]
        [(eq? (caar env) x) (cadar env)] ;; caso cuando el ambiente tiene la forma '( (x t) ... ) , devolvemos t
        [else (find-type x (cdr env))] ))  ;; llamada recursiva sobre el resto del ambiente si no coincide


;; Funcion que dada una variable x, un tipo t y un ambiente env devuelve un nuevo ambiente
;; resultado de agregar la tupla (x,t) al ambiente
(define (add-var-to-env x t env)
    (list (list x t) env))

;; Funcion que verifica que dada una lista de tipos args, estos tipos sean los correctos para la operacion pr
(define (check-args-types pr args )
    (case pr
        [(+ - * /) (andmap (lambda (x) (equal? x 'Int)) args) ]  ;; Estas primitivas son sobre enteros
        [(car cdr length) (andmap (lambda (x) (and (list? x) (equal? (car x) 'List))) args) ] ))  ;; Estas operaciones van sobre listas




;; AHORA IMPLEMENTAMOS LA FUNCION J
(define (J e env)
    (nanopass-case (L12 Expr) e
        [,x  (find-type x env)]         ;; para variables buscamos directamente en el ambiente
        [(const ,t ,c ) t]              ;; para constantes tenemos el tipo especificado en el const
        [(begin ,e* ... ,e) (J e env)]   ;; Retornamos el tipo de la ultima exprexion
        [(primapp ,pr ,e* ...)
            (if (check-args-types pr  (map (lambda (x) (J x env)) e*) )
                (case pr
                    [(+ - * / length) 'Int]
                    [(car) (caddr (car  (map (lambda (x) (J x env)) e*)))]
                    [(cdr) (car  (map (lambda (x) (J x env)) e*) )])
                (error 'J "Los tipos de ~a no son compatbles para la operacion ~a" e* pr))]

        ;; Para el if verificamos que el tipo de e0 sea Bool, y los tipos de e1 y e2 sean los mismos
        [(if ,e0 ,e1 ,e2)
            (if (and (equal?  (J e0 env) 'Bool)  (unify (J e1 env) (J e2 env)))
                (J e1 env)
                (error 'J "El tipo de ~a debe ser Bool. Y el tipo de ~a debe ser igual al de ~a " e0 e1 e2) )]

        ;; Para las lambdas el tipo es t -> type_of_body
        [(lambda ([,x ,t]) ,body)  (list t '->  (J body (add-var-to-env x t env)))]

        ;; para expresiones let devolvemos el tipo del body agregando (x t) al ambiente
        [(let ,x ,body)
                (J body env)]

        ;; para expresiones letrec devolvemos el tipo del body agregando (x t) al ambiente
        [(letrec ,x ,body)
                (J body env)]

        ;; Para expresiones letrec devolvemos el tipo del body agregando (x t) al ambiente
        [(letfun ,x,body)
                (J body env)]

        [(list ,e* ...)
            ;; si es la lista vacia devoldemos List
            (if (empty? e*)
                'List
                ;; Calculamos los tipos de los elementos
                (let* ([types (map (lambda (x) (J x env)) e*) ]
                        [t1 (car types)])
                    ;; Si todos los mismos son los mismos deovlvemos List of T1
                    (if (andmap (lambda (x) (unify x t1)) types)
                        (list 'List 'of t1)
                        (error 'J "Los elementos de la lista ~a no son del mismo tipo." e*)))  )]

        [(,e0 ,e1)
            (let ([t0 (J e0 env)] [t1 (J e1 env)])
                (if (and (list? t0) (equal? (cadr t0) '->) (unify (car t0) t1))  ;; verificamos que el tipo de e0 sea T1->T2 y el de e1 sea T1
                    (caddr t0)                                                   ;; Al aplicar la funcion se devuelve T2
                    (error 'J "El tipo de ~a no es compatible con el de ~a  para realizar la aplicacion de funcion." e0 e1) )  )]
        [else (error 'J "La expresion no corresponde al lenguaje")] ))


