
destdir=$(HOME)/public_html

pdflatex=pdflatex -halt-on-error

bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }'
#	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
#	  -- 'delete.field = { doi }'

bibliography=short.bib

stdlib=$(HOME)/agda/std-lib/src

gentex=latex/SubDiagError.tex latex/agda.sty
files=Makefile types17.tex $(gentex) macros.tex easychair.cls

# default : $(gentex) types17.pdf

pack : types17.zip

types17.zip : types17.tex auto-types17.bib $(files) types17.bbl
	zip $@ $^

latex/%.tex : %.lagda
	agda-2.5.3 --latex -i$(stdlib) -i. $<

# types17
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
# note: -shell-escape essential for minted syntax highlighting
types17_aux : types17.tex $(files)
	$(pdflatex) types17.tex;
	touch $@;

# then, run bibtex
types17.bbl : types17_aux auto-types17.bib
	-bibtex types17;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
types17.pdf : types17.bbl
	$(pdflatex) types17.tex;
	$(pdflatex) types17.tex;

# auto-types17.bib is only defined if bibtool is present
# and $(bibliography) exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-types17.bib : types17_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x types17.aux -i $(bibliography) >> $@;
endif
endif

# Templates
##################################################################

%.pdf : %.tex
	$(pdflatex) $<
	bibtex $*
	$(pdflatex) $<
	$(pdflatex) $<

# EOF
