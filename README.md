# Introduction to Homotopy Type Theory
This repository contains the material for a first introduction course to Homotopy Type Theory, accompanied by an Agda formalization of all the results and exercises.

The [course][1] was taught by Egbert Rijke at Carnegie Mellon University during the spring semester of 2018, and was aimed at advanced undergraduate students and graduate students from the Mathematics, Philosophy, and Computer Science departments.

## Topics

The course consisted of 27 one-hour lectures, in which we covered the following topics:

1. Dependent type theory
2. Dependent function types and the natural numbers
3. Inductive types
4. Identity types
5. Equivalences
6. Contractible types and maps
7. The fundamental theorem of identity types
8. The hierarchy of homotopical complexity
9. Function extensionality
10. The univalence axiom
11. The circle
12. Homotopy pullbacks
13. Homotopy pushouts
14. Cubical diagrams
15. Universality and descent for pushouts
16. Sequential colimits
17. The homotopy image of a map
18. Set quotients
19. Homotopy groups of types
20. The Hopf fibration

## Course notes
The course notes can be found in the Notes folder. They are currently subject to change. For the version that I used in my course, see the original [course website][1].

* To compile the course notes, run `pdflatex hott_intro.tex`. It should run well with TeXLive 2017 or later.
* To generate the bibliography, run `biber hott_intro.bcf`.
* To generate the index, run `makeindex hott_intro.idx`.

## Agda formalization
The Agda formalization can be found in the Agda folder. Except for the first lecture, which explains the rules for dependent type theory, the files of the formalization correspond 1-to-1 with the Lectures in the course notes, and the formalization follows the course material as closely as possible. A formalization of all the exercises is included, since many of them are essential in the development of the theory.

The formalization project of this course was initiated by Greg Langmead. The original repository can be found here:

https://github.com/glangmead/hott_cmu80818


[1]: http://www.andrew.cmu.edu/user/erijke/hott/
