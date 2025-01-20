There is no assembler and only enough interpreter to run the Ackermann example from the 1960 Newell IPL-V manual.

```code
% clang++ -std=c++20 -pedantic -o test test.cpp ipl_v.cpp
% ./test                                                 
509
PROGRAM RAN TO COMPLETION
number of tests 6, failures 0
% 
```
