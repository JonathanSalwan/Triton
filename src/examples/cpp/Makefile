##
## Copyright (C) - Triton
##
## This program is under the terms of the LGPLv3 License.
##

all: examples

examples:
	g++ -g3 -ggdb3 -std=c++11 -o taint_reg.bin taint_reg.cpp -ltriton
	g++ -g3 -ggdb3 -std=c++11 -o info_reg.bin info_reg.cpp -ltriton
	g++ -g3 -ggdb3 -std=c++11 -o ir.bin ir.cpp -ltriton
	g++ -g3 -ggdb3 -std=c++11 -o simplification.bin simplification.cpp -ltriton
	g++ -g3 -ggdb3 -std=c++11 -o constraint.bin constraint.cpp -ltriton

clean:
	rm *.bin

re: clean all

.PHONY: examples
