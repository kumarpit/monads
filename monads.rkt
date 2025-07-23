#lang racket
(require rackunit)

;; Notes and explorations from "Monads in Dynamically-Typed Languages"
;; https://eighty-twenty.org/2015/01/25/monads-in-dynamically-typed-languages

;; The goal is to implement "return-type polymorphism" on monads, similar to
;; monads in Haskell (where return/fail work across monad implementations)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Monomorphic definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lists

(define (list::fail)      (list))
(define (list::return x)  (list x))
(define (list::>>= xs f) (append-map f xs))

(define-syntax list::do
  (syntax-rules (<-)
    [(_ mexp) mexp]
    [(_ #:guard exp rest ...) (if exp (list::do rest ...) (list::fail))]
    [(_ var <- mexp rest ...) (list::>>= mexp (λ (var)   (list::do rest ...)))]
    [(_ mexp rest ...)        (list::>>= mexp (λ (_)
                                                (list::do rest ...)))]))

(check-equal? (list::do i <- '(1 2 3 4 5)
                        #:guard (odd? i)
                        (list::return (* i 2)))
              (list 2 6 10))

;; Streams
(require racket/stream)

(define (stream::fail) empty-stream)
(define (stream::return . args)
  (cond
    [(empty? args) empty-stream]
    [else (stream-cons (first args)
                       (apply stream::return (rest args)))]))
(define (stream::>>= s f)
  (stream-flatten (stream-map f s)))

;; (Streamof (Streamof A)) -> (Streamof A)
(define (stream-flatten sn)
  (cond
    [(stream-empty? sn) empty-stream]
    [else (let walk ((items (stream-first sn)))
            (cond
              [(stream-empty? items) (stream-flatten (stream-rest sn))]
              [else (stream-cons
                     (stream-first items)
                     (walk (stream-rest items)))]))]))

(check-equal? (stream->list (stream-flatten (stream (stream 1 2))))
              (list 1 2))
(check-equal? (stream->list (stream-flatten (stream
                                             (stream 1 2)
                                             (stream 3 4))))
              (list 1 2 3 4))

(define-syntax stream::do
  (syntax-rules (<-)
    [(_ mexp) mexp]
    [(_ #:guard exp rest ...) (if exp (stream::do rest ...) (stream::fail))]
    [(_ var <- mexp rest ...) (stream::>>= mexp (λ (var)
                                                  (stream::do rest ...)))]
    [(_ mexp rest ...)        (stream::>>= mexp (λ (_)
                                                  (stream::do rest ...)))]))

(check-equal? (stream->list (stream::do i <- (stream 1 2 3 4 5)
                                        #:guard (odd? i)
                                        (stream::return i (* i 2))))
              (list 1 2 3 6 5 10))


;; Towards polymorphism
(require racket/generic)

;; Haskell uses dictionary passing to implement dynamic dispatch-like behaviour
;; for the monadic combinators (it is not really dynamic - types are determined
;; at compile time) -- this is easy for something a like a bind (>>=) in which
;; the monadic type is passed as an argument, but for returns/fails we do not
;; know which monad to use. Haskell uses the type system to determine which
;; dictionary instance to use but we would need do infer it at runtime.

(struct MonadClass
  (failer    ;; -> (M a)
   returner  ;; a -> (M a)
   binder    ;; (M a) (a -> (M b)) -> (M b)
   coercer)) ;; N (M a) -> (N a)
;; interp. Monad type class representation

(define-generics monad
  (monad->monad-class monad)
  #:defaults ([null? (define (monad->monad-class m) MonadClass::List)]
              [pair? (define (monad->monad-class m) MonadClass::List)]))
;; interp. Generic method on all MonadClass type classes to determine their
;;         monad type

;; All (A B) MonadClass::<A> MonadClass::<B> -> MonadClass::<A>
;; Doesn't try to coerce the monad instance m to N
;; Effect: Signals an error if there is a mismatch between type of m and N
(define (not-coercable N m)
  (if (eq? (monad->monad-class m) N)
      m
      (error 'coerce)))

;; >>=, fail, and return may be used in a context where the final, concrete
;; monad type is not yet known. For these cases, we introduce neutral,
;; "quasi-monad" type clasess.

;; Read QuasiMonads as "almost" monads -- they are just intermediate
;; representation until the concrete monad type can be determined.

;; Note: I prepend quasi-monad constructors with ~ to distinguish them and
;;       regular monad constructors (eg. list).

(struct ~Return (value)
  #:methods gen:monad [(define (monad->monad-class m)
                         MonadClass::QuasiMonad::Return)])

(struct ~Fail ()
  #:methods gen:monad [(define (monad->monad-class m)
                         MonadClass::QuasiMonad::Fail)])

(struct ~Bind (ma a->mb)
  #:methods gen:monad [(define (monad->monad-class m)
                         MonadClass::QuasiMonad::Bind)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; QuasiMonad instances
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define MonadClass::QuasiMonad::Return
  (MonadClass
   (λ () (error 'fail))
   (λ (x) (~Return x))
   (λ (m f) (f (~Return-value m)))
   (λ (N m) ((MonadClass-returner N) (~Return-value m)))))
;; interp. This is identical to the Identity monad and serves as a temporary
;;         monadic wrapper for the value

(define MonadClass::QuasiMonad::Fail
  (MonadClass
   'invalid ; User code can never be "in" a failure monad. Don't need to
   'invalid ; provide implementations because these are "quasi" monads
   (λ (ma a->mb) (~Bind (ma a->mb)))
   (λ (N m) ((MonadClass-failer N)))))
;; interp. Used when `fail` is called in a context where the concrete monad type
;;         is not yet known

(define MonadClass::QuasiMonad::Bind
  (MonadClass
   'invalid ; Again, user code can never be "in" a bind monad.
   'invalid
   (λ (ma a->mb) (~Bind (ma a->mb)))
   (λ (N m) (>>= (coerce N (~Bind-ma m))
                 (~Bind-a->mb m)))))
;; interp. Used when `>>=` is called in a context where the concrete monad type
;;         is not yet known

;; Monad interface with ad-hoc polymorphism

(define (return x)
  (~Return x))

(define (fail)
  (~Fail))

(define (>>= ma a->mb)
  (define binder (MonadClass-binder (monad->monad-class ma)))
  (binder ma a->mb))

(define (coerce N ma)
  (define coercer (MonadClass-coercer (monad->monad-class ma)))
  (coercer N ma))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Monad Type Class instances
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define MonadClass::List
  (MonadClass
   (λ () '())
   (λ (x) (list x))
   (λ (xs f) (append-map (λ (x) (coerce MonadClass::List (f x))) xs))
   not-coercable))
