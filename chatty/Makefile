.PHONY: default

NAME    := paper
LHS2TEX := lhs2TeX
LATEXMK := latexmk

default : $(NAME).pdf

%.tex : %.lagda %.format
#	$(LHS2TEX) --poly $< > $@

	$(LHS2TEX) --agda $< > $@

%.pdf : %.tex %.bib
	$(LATEXMK) -pdf $<

paper.tex :: code/Monoid.lhs code/Functor.lhs sections/examples/examples.lhs sections/background/dynamicsystem.lhs sections/background/seqdecproc.lhs sections/background/seqdecprob.lhs sections/background/background.lhs sections/combinators/combinators.lhs sections/combinators/product.lhs sections/combinators/coproduct.lhs sections/combinators/interleave.lhs sections/combinators/swapcoproduct.lhs

clean:
	latexmk -C $(NAME).tex
