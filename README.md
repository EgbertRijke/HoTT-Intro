# Introduction to Homotopy Type Theory
This repository contains a book for a first introduction course to Homotopy Type Theory, accompanied by an Agda formalization of all the results and exercises.

The [course][1] was taught by Egbert Rijke at Carnegie Mellon University during the spring semester of 2018, and was aimed at advanced undergraduate students and graduate students from the Mathematics, Philosophy, and Computer Science departments.

## Topics

The course consisted of 27 one-hour lectures, in which we covered most of the following topics:

1. Martin-Lof's dependent type theory
    * Dependent type theory
    * Dependent function types
    * The type of natural numbers
    * More inductive types
    * Identity types
    * Type theoretic universes
2. Basic concepts of homotopy type theory
    * Equivalences
    * Contractible types and maps
    * The fundamental theorem of identity types
    * The hierarchy of homotopical complexity
    * Elementary number theory
3. Univalent mathematics
    * Function extensionality
    * The univalence axiom
    * Groups in univalent mathematics
    * The circle
    * The fundamental cover of the circle
4. Homotopy pullbacks and pushouts
    * Homotopy pullbacks
    * Homotopy pushouts
    * Cubical diagrams
    * Universality and descent for pushouts
    * Identity types of pushouts
5. The homotopy image of a map
    * Sequential colimits
    * The homotopy image of a map
    * Type theoretic replacement
    * Classifying types of groups
    * Set quotients
    * Truncations
6. Synthetic homotopy theory
    * Homotopy groups of types
    * The long exact sequence of homotopy groups
    * Connected types
    * Wedges and smash products
    * The Blakers-Massey Theorem

## Book
The course notes that I took are evolving into an introductory textbook for students who want to learn homotopy type theory fo the first time. They are currently subject to frequent change. For the version of the notes that I used during the course, see the original [course website][1].

* To compile the book, run `pdflatex hott-intro.tex`. It should run well with TeXLive 2017 or later.
* To generate the bibliography, run `biber hott-intro.bcf`.
* To generate the index, run `makeindex hott-intro.idx`.

All of this is automated when you run `latexmk -pdf hott-intro.tex`.

## Agda formalization
The Agda formalization can be found in the Agda folder. Except for the first lecture, which explains the rules for dependent type theory, the files of the formalization correspond 1-to-1 with the Lectures in the course notes, and the formalization follows the course material as closely as possible. A formalization of all the exercises is included, since many of them are essential in the development of the theory.


[1]: http://www.andrew.cmu.edu/user/erijke/hott/
