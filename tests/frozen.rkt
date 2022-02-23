#lang racket/base

(require racklog rackunit)

;; some basic tests that freeze/melt behave appropriately

(test-equal? "%freeze/%melt can manipulate logic vars directly"
             (%which (X Y)
               (%let (*X)
                 (%and
                   (%freeze (list X) (list *X))
                   (%melt (list *X) (list Y))
                   (%= Y 4))))
            '((X . 4)
              (Y . 4)))

(test-equal? "%freeze/%melt-new copies the logic variables involved"
             (%which (X Y X2 Y2)
               (%let (*X *Y)
                 (%and
                   (%freeze (list X Y) (list *X *Y))
                   (%melt-new (list *X *Y) (list X2 Y2))
                   (%= Y2 4)
                   (%= X2 8))))
            '((X . _)
              (Y . _)
              (X2 . 8)
              (Y2 . 4)))

(test-equal? "%freeze/%melt support variables as subterms (not protected by a logic var) of the frozen RHS"
             (%which (X Y X2 Y2)
               (%let (F)
                 (%and
                   (%freeze (list X Y) F)
                   (%melt F (list X2 Y2))
                   (%= X2 8)
                   (%= Y2 4))))
             '((X . 8)
               (Y . 4)
               (X2 . 8)
               (Y2 . 4)))

(test-equal? "%freeze/%melt-new support variables as subterms (not protected by a logic var) of the frozen RHS and refresh the free vars"
             (%which (X Y X2 Y2)
               (%let (F)
                 (%and
                   (%freeze (list X Y) F)
                   (%melt-new F (list X2 Y2))
                   (%= X2 8)
                   (%= Y2 4))))
             '((X . _)
               (Y . _)
               (X2 . 8)
               (Y2 . 4)))

(test-equal? "%freeze/%melt respect the equivalences among the free variables that appear free"
             (%which (X Y A B C D)
               (%let (F)
                 (%and
                   (%freeze (list X Y Y X) F)
                   (%melt F (list A B C D))
                   (%= A 2)
                   (%= B 4))))
             '((X . 2)
               (Y . 4)
               (A . 2)
               (B . 4)
               (C . 4)
               (D . 2)))

(test-equal? "%freeze/%melt-new respect the equivalences among the free variables that appear free"
             (%which (X Y A B C D)
               (%let (F)
                 (%and
                   (%freeze (list X Y Y X) F)
                   (%melt-new F (list A B C D))
                   (%= A 2)
                   (%= B 4))))
             '((X . _)
               (Y . _)
               (A . 2)
               (B . 4)
               (C . 4)
               (D . 2)))
