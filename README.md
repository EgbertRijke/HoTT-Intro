# Introduction to Homotopy Type Theory
This repository contains a book for a first introduction course to Homotopy Type Theory, accompanied by an Agda formalization of all the results and exercises.

The [course][1] was taught by Egbert Rijke at Carnegie Mellon University during the spring semester of 2018, and was aimed at advanced undergraduate students and graduate students from the Mathematics, Philosophy, and Computer Science departments.

## Topics

The course consisted of 27 one-hour lectures, in which we covered most of the following topics:

1. Dependent type theory
2. Dependent function types and the natural numbers
3. Inductive types
4. Universes and type-valued relations
5. Identity types
6. Equivalences
7. Contractible types and maps
8. The fundamental theorem of identity types
9. The hierarchy of homotopical complexity
10. Elementary number theory
11. Function extensionality
12. The univalence axiom
13. The circle
14. The fundamental cover of the circle
15. Homotopy pullbacks
16. Homotopy pushouts
17. Cubical diagrams
18. Universality and descent for pushouts
19. Identity types of pushouts
20. Sequential colimits
21. The homotopy image of a map
22. Type theoretic replacement
23. Classifying types of groups
24. Set quotients
25. Truncations
26. Homotopy groups of types
27. The long exact sequence of homotopy groups
28. Connected types
29. Wedges and smash products
30. The Blakers-Massey Theorem

## Book
The course notes that I took are evolving into an introductory textbook for students who want to learn homotopy type theory fo the first time. They are currently subject to frequent change. For the version of the notes that I used during the course, see the original [course website][1].

* To compile the book, run `pdflatex hott-intro.tex`. It should run well with TeXLive 2017 or later.
* To generate the bibliography, run `biber hott-intro.bcf`.
* To generate the index, run `makeindex hott-intro.idx`.

All of this is automated when you run `latexmk -pdf hott-intro.tex`.

## Agda formalization
The Agda formalization can be found in the Agda folder. Except for the first lecture, which explains the rules for dependent type theory, the files of the formalization correspond 1-to-1 with the Lectures in the course notes, and the formalization follows the course material as closely as possible. A formalization of all the exercises is included, since many of them are essential in the development of the theory.


[1]: http://www.andrew.cmu.edu/user/erijke/hott/
