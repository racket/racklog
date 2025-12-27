#lang racket/base
(require racklog
         tests/eli-tester)

;; test that %find-all behaves like %which with zero/one/multiple goals
(module+ test
  (test
   (%which (x))
   => '((x . _))

   (%find-all (x))
   => '(((x . _)))

   (%which (x)
           (%member x '(a b c)))
   => '((x . a))

   (%find-all (x)
              (%member x '(a b c)))
   => '(((x . a))
        ((x . b))
        ((x . c)))

   (%which (x)
           (%member x '(a b c))
           (%/= x 'b))
   => '((x . a))

   (%find-all (x)
              (%member x '(a b c))
              (%/= x 'b))
   => '(((x . a))
        ((x . c)))

   (%which (x)
           (%member x '(a b c))
           (%/= x 'b)
           (%/= x 'a))
   => '((x . c))

   (%find-all (x)
              (%member x '(a b c))
              (%/= x 'b)
              (%/= x 'a))
   => '(((x . c)))

   (%which (x) %fail)
   => #false

   (%find-all (x) %fail)
   => '(#false)

   (%which (x) %true %fail)
   => #false

   (%find-all (x) %true %fail)
   => '(#false)))
