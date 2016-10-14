all: examples

examples: constraint info_reg ir parsing_elf simplification taint_reg

constraint:
	$(CXX) -g3 -ggdb3 -std=c++0x -ltriton -o constraint.bin constraint.cpp

info_reg:
	$(CXX) -g3 -ggdb3 -std=c++0x -ltriton -o info_reg.bin info_reg.cpp

ir:
	$(CXX) -g3 -ggdb3 -std=c++0x -ltriton -o ir.bin ir.cpp

parsing_elf:
	$(CXX) -g3 -ggdb3 -std=c++0x -ltriton -o parsing_elf.bin parsing_elf.cpp

simplification:
	$(CXX) -g3 -ggdb3 -std=c++0x -ltriton -o simplification.bin simplification.cpp

taint_reg:
	$(CXX) -g3 -ggdb3 -std=c++0x -ltriton -o taint_reg.bin taint_reg.cpp

clean:
	rm *.bin

re: clean all

.PHONY: examples constraint info_reg ir parsing_elf simplification taint_reg
