all: model.pdf  #model-multi.pdf

MF=\def\multiargs{false}
MT=\def\multiargs{true}
PF=\def\paths{false}
PT=\def\paths{true}
LF=\def\dologic{false}
LT=\def\dologic{true}

model-simple.pdf: model.tex ts.sty
	pdflatex -jobname=model-simple '$(MF)$(PF)$(LT)\input{model.tex}'
	pdflatex -jobname=model-simple '$(MF)$(PF)$(LT)\input{model.tex}'

model.pdf: model.tex ts.sty
	pdflatex '$(MF)$(PT)$(LT)\input{model.tex}'
	pdflatex '$(MF)$(PT)$(LT)\input{model.tex}'


model-multi.pdf: model.tex ts.sty
	pdflatex -jobname=model-multi '$(MT)$(PT)$(LT)\input{model.tex}'
	pdflatex -jobname=model-multi '$(MT)$(PT)$(LT)\input{model.tex}'

clean:
	rm -f model.pdf model-multi.pdf
	rm -f *.aux *.log

one: model.tex ts.sty
	pdflatex '\newcommand{\multiargs}{$(MULTI)}\input{model.tex}'
