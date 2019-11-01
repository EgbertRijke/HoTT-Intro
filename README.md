# Introduction to Homotopy Type Theory
This repository contains a book for a first introduction course to Homotopy Type Theory, accompanied by formalization projects in several proof assistats, closely following the material in the book.

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
    
## The Formalization Rosetta Stone
This repositories contains formalizations of the first half of the course in several proof assistants: currently Agda and Coq. These formalization project are designed to follow the course notes as closely as possible, and they include solutions to the exercises. From the dual point of view, the course notes form an extensive documentation of the formalization projects, and it is my hope that people will find it helpful to have such a documentation with the formalization.

Formalization projects of this course in more proof assistants that support homotopy type theory might be added in the future.

## Book
The course notes that I took are evolving into an introductory textbook for students who want to learn homotopy type theory for the first time. They are currently subject to frequent change, so my recommendation would be to have a look at the 2018 course notes or the 2019 summer school notes instead. Those can be found in the `pdfs` folder of this repository. 

To compile the notes, run `latexmk -pdf hott-intro.tex`.


[1]: http://www.andrew.cmu.edu/user/erijke/hott/
