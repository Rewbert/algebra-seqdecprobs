.PHONY: default

NAME    := AlgSDP

LHS2TEX := lhs2TeX
LATEXMK := latexmk

default : $(NAME).pdf

%.tex : %.lagda ../paper/paper.format
	$(LHS2TEX) --agda $< > $@

%.pdf : %.tex
	$(LATEXMK) -pdf $<

clean:
	latexmk -C $(NAME).tex
