# TODO: the compilation is always happening
# TODO: the compliation is done one file at a time

MODULES=lexer parser pprint ast
SOURCE=$(addsuffix .ss,$(MODULES))
COMPILED=$(addsuffix .zo,$(MODULES))

all: $(COMPILED)

clean:
	rm -f compiled/*.zo

$(COMPILED): %.zo: %.ss
	mzc --auto-dir -z $?
