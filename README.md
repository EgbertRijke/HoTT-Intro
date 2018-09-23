# HoTT-Intro
This repository contains the material for a first introduction course to Homotopy Type Theory, accompanied by an Agda formalization of all the results and exercises.

The [course][1] was taught by Egbert Rijke at Carnegie Mellon University during the spring semester of 2018, and was aimed at advanced undergraduate students and graduate students from the Mathematics, Philosophy, and Computer Science departments.

## Course notes
The course notes can be found in the Notes folder. 

* To compile the course notes, run `pdflatex hott_intro.tex`. It should run well with TeXLive 2017 or later.
* To generate the bibliography, run `biber hott_intro.bcf`.
* To generate the index, run `makeindex hott_intro.idx`.

## Agda formalization
The Agda formalization can be found in the Agda folder. Except for the first lecture, which explains the rules for dependent type theory, the files of the formalization correspond 1-to-1 with the Lectures in the course notes, and the formalization follows the course material as closely as possible. A formalization of all the exercises is included, since many of them are essential in the development of the theory.

[1]: http://www.andrew.cmu.edu/user/erijke/hott/
