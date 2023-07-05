#lang info

(define collection "racklog")

(define scribblings
  '(("racklog.scrbl" (multi-page) ("Logic programming"))))
(define deps '("base"
               "datalog"))
(define build-deps '("eli-tester"
                     "rackunit-lib"
                     "racket-doc"
                     "scribble-lib"))

(define pkg-desc "The implementation of the Racklog (embedded Prolog) language")

(define pkg-authors '(jay))

(define license
  '(Apache-2.0 OR MIT))
