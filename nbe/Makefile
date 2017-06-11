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
bibliography=all.bib

stdlib=$(HOME)/agda/std-lib/src

files=icfp17.tex acmart.cls Makefile macros.tex latex/SubDiag.tex latex/SubDiagError.tex figjudge.tex figeq.tex figty.tex figcheck.tex sec-sr.tex sec-asub.tex sec-tycheck.tex

.PHONY : all debugMake html

.PRECIOUS : %.dvi %.ps %.gz %.pdf %.tex


default : icfp17-long.pdf # icfp17.pdf

add : additional-material.tgz

additional-material.tgz : README-additional-material.txt icfp17-long.pdf Sit-0.2017.2.26.tar.gz
	tar czhf $@ $^

pack : icfp17.zip

icfp17.zip : icfp17.pdf $(files) jfp1.cls harpoons.sty icfp17.bbl jfp.bst auto-icfp17.bib
	zip $@ $^

ship : jfp16-agda.tgz html
	cp -pr html/* $(destdir)/jfp16/
	cp -p $<  $(destdir)/jfp16/

jfp16-agda.tgz : $(agdafiles)
	tar czf $@ $^

html : html/Everything.html

html/Everything.html : $(agdafiles)
	agda --html $<

latex/%.tex : %.lagda
	agda --latex $<

talkTYPES17.pdf : talkTYPES17.tex macros.tex latex/MonusDiagError.tex latex/MonusDiag.tex
	pdflatex $<

# icfp17
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
icfp17_aux : icfp17.tex $(files)
	$(pdflatex) icfp17.tex;
	touch $@;

# then, run bibtex
icfp17.bbl : icfp17_aux auto-icfp17.bib
	-bibtex icfp17;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
icfp17.pdf : icfp17.bbl
	$(pdflatex) icfp17.tex;
	$(pdflatex) icfp17.tex;

# auto-icfp17.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-icfp17.bib : icfp17_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x icfp17.aux -i $(bibliography) >> $@;
endif
endif

# icfp17-long
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
icfp17-long_aux : icfp17-long.tex $(files)
	$(pdflatex) icfp17-long.tex;
	touch $@;

# then, run bibtex
icfp17-long.bbl : icfp17-long_aux auto-icfp17-long.bib
	-bibtex icfp17-long;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
icfp17-long.pdf : icfp17-long.bbl
	$(pdflatex) icfp17-long.tex;
	$(pdflatex) icfp17-long.tex;

# auto-icfp17-long.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-icfp17-long.bib : icfp17-long_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x icfp17-long.aux -i $(bibliography) >> $@;
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
