Formalizing Linear Algebra Algorithms using Dependently Typed Functional Programming
====================================================================================

![Presentation Type Checks](https://github.com/ryanorendorff/lc-2020-linear-algebra-agda/workflows/presentation-typechecks/badge.svg)

Abstract
--------

Linear algebra is the backbone of many critical algorithms such as self driving
cars and machine learning. Modern tooling makes it easy to program with linear
algebra, but the resulting code is prone to bugs from index mismatches and
improperly defined matrices.

In this talk, we will formalize basic linear algebra operations by representing
a matrix as a function from one vector space to another. This ""matrix-free""
construction will enable us to prove basic properties about linear algebra;
from this base, we will show a framework for formulating optimization problems
that is correct by construction, meaning that it will be impossible to
represent improperly formed matrices. We will compare the Agda framework to
similar frameworks written in Python and in dependently typed Haskell.
