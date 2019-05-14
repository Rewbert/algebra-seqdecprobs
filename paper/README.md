## Layout

**paper.lagda** is the top level file for the paper. In the document body the file imports its sections from the **sections/** folder.

The idea was that the contents of sections should mirror the table of contents of the report somehow (with reservation for the ordering, of course).

+ **sections/**
  + **background/**
    + background.lagda
    + dynamicsystem.lagda
    + seqdecprob.lagda
    + seqdecproc.lagda
  + **combinators/**
    + combinators.lagda
    + coproduct.lagda
    + interleave.lagda
    + product.lagda
    + swapcoproduct.lagda
  + **examples/**
    + examples.lagda
  + **policies/**
    + policy.lagda
 and so on.

----------------

Perhaps retarget to TyDe'19:

  https://icfp19.sigplan.org/home/tyde-2019#Call-for-Papers

Deadline 2019-05-19
Page limit: 12 pages

----------------

1. Intro

+ TODO early example (of using combinators even before def. them)
  (teaser on the first page)
_×SDP_ : SDProc → SDProc → SDProc
_+SDP_ : SDProc → SDProc → SDProc

test = a + b * c

2. Background

2.1 DynSys (S, step)    + trajectory
2.2 SDProc (S, C, step), Policy,
2.3 SDProb (S, C, step, reward),

3. Examples

  (expand and explain the teaser on the first page)

[If too much, put some code in appendix.]

3.a SDProc example
  1d-state, 1d-control, 1d-step, 1d-system (TODO name?)
3.b Policy example + test runs
3.c SDProb example
  (Reviewer qustions, why not include SDProc as subfield?)

4. [Core message] Combinators for SDProc
4.1 Product
TODO continue
