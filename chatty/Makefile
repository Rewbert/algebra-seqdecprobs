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

paper.tex :: sections/background/dynamicsystem.lagda sections/background/seqdecproc.lagda sections/background/seqdecprob.lagda sections/background/background.lagda sections/combinators/combinators.lagda sections/combinators/product.lagda sections/combinators/coproduct.lagda sections/combinators/interleave.lagda sections/combinators/swapcoproduct.lagda sections/examples/examples.lagda

clean:
	latexmk -C $(NAME).tex
