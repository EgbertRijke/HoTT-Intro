# Introduction to Homotopy Type Theory
This repository contains a book for a first introduction course to Homotopy Type Theory, accompanied by an Agda formalization of all the results and exercises.

The [course][1] was taught by Egbert Rijke at Carnegie Mellon University during the spring semester of 2018, and was aimed at advanced undergraduate students and graduate students from the Mathematics, Philosophy, and Computer Science departments.

## Topics

The course consisted of 27 one-hour lectures, in which we covered most of the following topics:

I. Martin-Lof's dependent type theory

  1. Dependent type theory
  2. Dependent function types
  3. The type of natural numbers
  4. More inductive types
  5. Identity types
  6. Type theoretic universes

II. Basic homotopy type theory

  7. Equivalences
  8. Contractible types and maps
  9. The fundamental theorem of identity types
  10. The hierarchy of homotopical complexity
  11. Elementary number theory
  
III. Univalent mathematics
  
  12. Function extensionality
  13. The univalence axiom
  14. Groups in univalent mathematics
  15. The circle
  16. The fundamental cover of the circle
  
IV. Homotopu pullbacks and pushouts

  17. Homotopy pullbacks
  18. Homotopy pushouts
  19. Cubical diagrams
  20. Universality and descent for pushouts
  21. Identity types of pushouts
  
V. The homotopy image of a map

  22. Sequential colimits
  23. The homotopy image of a map
  24. Type theoretic replacement
  25. Classifying types of groups
  26. Set quotients
  27. Truncations
  
VI. Synthetic homotopy theory

  28. Homotopy groups of types
  29. The long exact sequence of homotopy groups
  30. Connected types
  31. Wedges and smash products
  32. The Blakers-Massey Theorem

## Book
The course notes that I took are evolving into an introductory textbook for students who want to learn homotopy type theory fo the first time. They are currently subject to frequent change. For the version of the notes that I used during the course, see the original [course website][1].

* To compile the book, run `pdflatex hott-intro.tex`. It should run well with TeXLive 2017 or later.
* To generate the bibliography, run `biber hott-intro.bcf`.
* To generate the index, run `makeindex hott-intro.idx`.

All of this is automated when you run `latexmk -pdf hott-intro.tex`.

## Agda formalization
The Agda formalization can be found in the Agda folder. Except for the first lecture, which explains the rules for dependent type theory, the files of the formalization correspond 1-to-1 with the Lectures in the course notes, and the formalization follows the course material as closely as possible. A formalization of all the exercises is included, since many of them are essential in the development of the theory.


[1]: http://www.andrew.cmu.edu/user/erijke/hott/
