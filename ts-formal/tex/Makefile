all: model.pdf model-multi.pdf model-simple.pdf model-logic.pdf model-everything.pdf

MF=\def\multiargs{false}
MT=\def\multiargs{true}
PF=\def\paths{false}
PT=\def\paths{true}
LF=\def\dologic{false}
LT=\def\dologic{true}


model-multi.pdf: model.tex ts.sty
	pdflatex -jobname=model-multi '$(LF)$(MT)$(PT)\input{model.tex}'
	pdflatex -jobname=model-multi '$(LF)$(MT)$(PT)\input{model.tex}'

model-simple.pdf: model.tex ts.sty
	pdflatex -jobname=model-simple '$(LF)$(MF)$(PF)\input{model.tex}'
	pdflatex -jobname=model-simple '$(LF)$(MF)$(PF)\input{model.tex}'


model.pdf: model.tex ts.sty
	pdflatex '$(MF)$(PT)$(LF)\input{model.tex}'
	pdflatex '$(MF)$(PT)$(LF)\input{model.tex}'

model-logic.pdf: model.tex ts.sty
	pdflatex -jobname=model-logic '$(MF)$(PF)$(LT)\input{model.tex}'
	pdflatex -jobname=model-logic '$(MF)$(PF)$(LT)\input{model.tex}'

model-everything.pdf: model.tex ts.sty
	pdflatex -jobname=model-everything '$(MT)$(PT)$(LT)\input{model.tex}'
	pdflatex -jobname=model-everything '$(MT)$(PT)$(LT)\input{model.tex}'

clean:
	rm -f model.pdf model-multi.pdf
	rm -f *.aux *.log

one: model.tex ts.sty
	pdflatex '\newcommand{\multiargs}{$(MULTI)}\input{model.tex}'
