all: src/binary.glob src/ast_instructions.glob src/association_list.glob src/encode.v
	coqc src/encode.v


%.glob: %.v
	coqc -I ./src $<

clean:
	rm src/*.glob src/*.vo
