#lang racket/base
(require racklog)

(define (moment<? a b) #f)

(define (any->moment x)
  x)

(define (%earlist moment moments)
  (%and (%not (%= moments '()))
        (%is moment (sort moments (lambda (a b) (moment<? a b))
                          #:key (lambda (x) (any->moment x))))))
