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
         pr
         c    
         t
         (const t c)
         (begin e* ... e)
         (primapp pr e* ...)
         (if e0 e1 e2 )
         (lambda ([x t] ...) body* ... body)
         (let ([x t e]) body* ... body)
         (letrec ([x t e]) body* ... body)
         (letfun ([x t e]) body* ... body)
         (list e* ...)
         (e0 e1 )))