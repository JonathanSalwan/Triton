all: examples

examples:
	$(CXX) -g3 -ggdb3 -std=c++0x -o taint_reg.bin taint_reg.cpp -ltriton
	$(CXX) -g3 -ggdb3 -std=c++0x -o info_reg.bin info_reg.cpp -ltriton
	$(CXX) -g3 -ggdb3 -std=c++0x -o ir.bin ir.cpp -ltriton
	$(CXX) -g3 -ggdb3 -std=c++0x -o simplification.bin simplification.cpp -ltriton
	$(CXX) -g3 -ggdb3 -std=c++0x -o constraint.bin constraint.cpp -ltriton
	$(CXX) -g3 -ggdb3 -std=c++0x -o parsing_elf.bin parsing_elf.cpp -ltriton

clean:
	rm *.bin

re: clean all

.PHONY: examples
