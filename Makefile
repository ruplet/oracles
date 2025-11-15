all: driver.pdf

FLAGS = -interaction=nonstopmode -halt-on-error
CHAPTERS = $(wildcard chapters/*.tex)

.PHONY: all clean

clean:
	find chapters -type f -name '*.aux' -print -delete
	rm -f driver.bcf driver.log driver.out driver.run.xml driver.toc \
	      driver.bbl driver.blg driver.synctex.gz

driver.pdf: driver.tex $(CHAPTERS)
	$(MAKE) clean
	pdflatex $(FLAGS) driver.tex
	biber driver
	pdflatex $(FLAGS) driver.tex
	pdflatex $(FLAGS) driver.tex
