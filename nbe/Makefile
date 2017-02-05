# Makefile for Sized HOAS
# Author : Andreas Abel
# Created: 2008-05-09, 2010-03-29, 2010-11-23
# Source : project/normCC/implicit/Makefile

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
#	  -- 'delete.field = { doi }' \
catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=medium.bib

stdlib=$(HOME)/agda/std-lib/src

files=nbe-sized.tex macros.tex

.PHONY : all debugMake html

.PRECIOUS : %.dvi %.ps %.gz %.pdf %.tex


default : nbe-sized.pdf

pack : nbe-sized.zip

nbe-sized.zip : nbe-sized.pdf $(files) jfp1.cls harpoons.sty nbe-sized.bbl jfp.bst auto-nbe-sized.bib
	zip $@ $^

ship : jfp16-agda.tgz html
	cp -pr html/* $(destdir)/jfp16/
	cp -p $<  $(destdir)/jfp16/

jfp16-agda.tgz : $(agdafiles)
	tar czf $@ $^

html : html/Everything.html

html/Everything.html : $(agdafiles)
	agda --html $<


# nbe-sized
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
nbe-sized_aux : nbe-sized.tex $(files)
	$(pdflatex) nbe-sized.tex;
	touch $@;

# then, run bibtex
nbe-sized.bbl : nbe-sized_aux auto-nbe-sized.bib
	-bibtex nbe-sized;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
nbe-sized.pdf : nbe-sized.bbl
	$(pdflatex) nbe-sized.tex;
	$(pdflatex) nbe-sized.tex;

# auto-nbe-sized.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-nbe-sized.bib : nbe-sized_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x nbe-sized.aux -i $(bibliography) >> $@;
endif
endif



# Templates (reverted back to simple templates)


talk% : talk%.pdf
	cp -p $? $(destdir)/;
	touch $@;

talk%.pdf : talk%.tex
	pdflatex $<;


%.tex : %.lhs
	lhs2TeX --poly -i lhs2TeX.fmt $< > $@
# /usr/local/share/lhs2tex-1.13/

% :  %.pdf # %.dvi %.ps.gz # %.tar.gz
	cp -p $? $(destdir)/;
	touch $@;

%.dvi : %.tex
	$(latex) $<;
	-bibtex $*;
	$(latex) $<;
	$(latex) $<;

%.pdf : %.dvi
	pdflatex $*.tex;

%.ps  : %.dvi
	dvips -o $@ $<;

%.gz : %
	cat $< | gzip > $@

## does not work since $ is evaluated before %
#%.tar : %.cfg $(shell cat %.cfg)
#	echo $?


#EOF
