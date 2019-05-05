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

paper.tex :: sections/core/dynamicsystem.lagda sections/core/seqdecproc.lagda sections/core/seqdecprob.lagda sections/background.lagda sections/combinators.lagda sections/examples.lagda sections/policycombinators.lagda

clean:
	latexmk -C $(NAME).tex
