all: examples

examples: constraint info_reg ir simplification taint_reg

constraint:
	$(CXX) $(CXXFLAGS) -g3 -ggdb3 -std=c++0x -o constraint.bin constraint.cpp -ltriton

info_reg:
	$(CXX) $(CXXFLAGS) -g3 -ggdb3 -std=c++0x -o info_reg.bin info_reg.cpp -ltriton

ir:
	$(CXX) $(CXXFLAGS) -g3 -ggdb3 -std=c++0x -o ir.bin ir.cpp -ltriton

simplification:
	$(CXX) $(CXXFLAGS) -g3 -ggdb3 -std=c++0x -o simplification.bin simplification.cpp -ltriton

taint_reg:
	$(CXX) $(CXXFLAGS) -g3 -ggdb3 -std=c++0x -o taint_reg.bin taint_reg.cpp -ltriton

clean:
	rm *.bin

re: clean all

.PHONY: examples constraint info_reg ir simplification taint_reg
