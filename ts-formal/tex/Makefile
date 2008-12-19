all: model.pdf model-multi.pdf

MULTI=true

model-multi.pdf: model.tex ts.sty
	pdflatex -jobname=model-multi '\newcommand{\multiargs}{true}\input{model.tex}'
	pdflatex -jobname=model-multi '\newcommand{\multiargs}{true}\input{model.tex}'

MULTI=false

model.pdf: model.tex ts.sty
	pdflatex '\newcommand{\multiargs}{$(MULTI)}\input{model.tex}'
	pdflatex '\newcommand{\multiargs}{$(MULTI)}\input{model.tex}'

clean:
	rm -f model.pdf
