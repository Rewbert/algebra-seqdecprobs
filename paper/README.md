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