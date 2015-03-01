#lang racket/base
(require "lang.rkt")
;; Since `compile-program` generates syntax that already
;; includes binding, avoid exporting anything from the
;; language position of the module produced by "reader.rkt".
