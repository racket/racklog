#lang racket/base
(require racklog
         tests/eli-tester)

(module+ test
  (test
   (%which (x) %true)
   => '((x . _))
   
   (%which (x) (%or (%not (%= x 1)) %true))
   => '((x . _))

   (%which (x) (%or (%if-then-else (%= x 1) %fail %true) %true))
   => '((x . _))

   (%which (x) (%or (%cut-delimiter (%or (%and (%= x 1) ! %fail) %true)) %true))
   => '((x . _))

   (%which (x) (%or (%cut-delimiter (%or (%and ! (%= x 1) %fail) %true)) %true))
   => '((x . _))))
