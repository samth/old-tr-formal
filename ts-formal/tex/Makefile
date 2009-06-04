all: model.pdf model-multi.pdf model-simple.pdf

MF=\def\multiargs{false}
MT=\def\multiargs{true}
PF=\def\paths{false}
PT=\def\paths{true}


model-multi.pdf: model.tex ts.sty
	pdflatex -jobname=model-multi '$(MT)$(PT)\input{model.tex}'
	pdflatex -jobname=model-multi '$(MT)$(PT)\input{model.tex}'

model-simple.pdf: model.tex ts.sty
	pdflatex -jobname=model-simple '$(MF)$(PF)\input{model.tex}'
	pdflatex -jobname=model-simple '$(MF)$(PF)\input{model.tex}'


model.pdf: model.tex ts.sty
	pdflatex '$(MF)$(PT)\input{model.tex}'
	pdflatex '$(MF)$(PT)\input{model.tex}'

clean:
	rm -f model.pdf model-multi.pdf
	rm -f *.aux *.log

one: model.tex ts.sty
	pdflatex '\newcommand{\multiargs}{$(MULTI)}\input{model.tex}'
