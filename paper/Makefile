.PHONY: default

NAME    := paper
NAME2   := paper2
LHS2TEX := lhs2TeX
LATEXMK := latexmk

default : $(NAME).pdf $(NAME2).pdf

%.tex : %.lagda paper.format
	$(LHS2TEX) --agda $< > $@

%.pdf : %.tex paper.bib
	$(LATEXMK) -pdf $<

paper.tex :: abstract.txt sections/core/dynamicsystem.lagda sections/core/seqdecproc.lagda sections/core/seqdecprob.lagda sections/core/seqdecproctime.lagda sections/background.lagda sections/introduction.lagda sections/combinators.lagda sections/examples.lagda sections/policycombinators.lagda sections/2dexamples.lagda sections/combinatorstime.lagda sections/conclusions.lagda sections/appendix.lagda sections/extabstract.lagda sections/core/traj.lagda

paper2.tex :: abstract.txt sections/core/dynamicsystem.lagda sections/core/seqdecproc.lagda sections/core/seqdecprob.lagda sections/core/seqdecproctime.lagda sections/background.lagda sections/introduction.lagda sections/combinators.lagda sections/examples.lagda sections/policycombinators.lagda sections/2dexamples.lagda sections/combinatorstime.lagda sections/conclusions.lagda sections/appendix.lagda sections/extabstract.lagda sections/core/traj.lagda
clean:
	latexmk -C $(NAME).tex
