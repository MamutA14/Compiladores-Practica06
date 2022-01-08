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

(define fun-count 0)

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

