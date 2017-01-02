all: examples

examples: constraint info_reg ir parsing_elf parsing_pe simplification taint_reg

constraint:
	$(CXX) -g3 -ggdb3 -std=c++0x -o constraint.bin constraint.cpp -ltriton

info_reg:
	$(CXX) -g3 -ggdb3 -std=c++0x -o info_reg.bin info_reg.cpp -ltriton

ir:
	$(CXX) -g3 -ggdb3 -std=c++0x -o ir.bin ir.cpp -ltriton

parsing_elf:
	$(CXX) -g3 -ggdb3 -std=c++0x -o parsing_elf.bin parsing_elf.cpp -ltriton

parsing_pe:
	$(CXX) -g3 -ggdb3 -std=c++0x -o parsing_pe.bin parsing_pe.cpp -ltriton

simplification:
	$(CXX) -g3 -ggdb3 -std=c++0x -o simplification.bin simplification.cpp -ltriton

taint_reg:
	$(CXX) -g3 -ggdb3 -std=c++0x -o taint_reg.bin taint_reg.cpp -ltriton

clean:
	rm *.bin

re: clean all

.PHONY: examples constraint info_reg ir parsing_elf parsing_pe simplification taint_reg
