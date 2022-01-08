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