#include "ipl_v.h"

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <chrono>
#include <ctime>
#include <cassert>
#include <vector>
#include <memory>
#include <map>
#include <algorithm>
#include <deque>
#include <cctype>
#include <thread>
#include <array>
#include <cstdint>
#include <functional>



namespace ipl_v_cpp {




struct cell {
    uint8_t     p;
    uint8_t     q;
    uint32_t    symb;
    address     link;
};



std::string interpreter_io::getline() { return {}; }
void interpreter_io::print(const std::string &) {}


using address = uint32_t;

constexpr address nil = 0;

/*  The listing at the end of https://bitsavers.org/pdf/rand/ipl/Baker_IPL-704.pdf
    suggests that in the IBM 7090 implementation of IPL-V the instruction fields were
    distributed in the 36-bit machine word in this way:

        35                17               0
        |                 |                |
        qqqSSSSSSSSSSSSSSSpppLLLLLLLLLLLLLLL

        ppp             = P (3-bits)
        qqq             = Q (3-bits)
        SSSSSSSSSSSSSSS = SYMB (15-bits)
        LLLLLLLLLLLLLLL = LINK (15-bits)

    How likely is it that any IPL-V code expects a particular word layout?
*/




class interpreter::implementation {
public:
    implementation(interpreter_io & io);
    ~implementation() {}
    unsigned assemble(const std::string & input);
    void execute(address program_start);


private:
    interpreter_io & io_;

    std::vector<cell> space;

    address alloc_cell();
    void free_cell(address addr);
    void push_down(address addr);
    void pop_up(address addr);
    bool is_primitive(address addr);
    void execute_primitive(address primitive);

    // IPL-V system cells

    address h0 = nil;   // communication cell (stack)
    address h1 = nil;   // current instruction address (stack)
    address h2 = 0;     // list of available space
    uint_least64_t h3 = 0;     // tally of interpretation cycles
    address h5 = 5;     // test cell

    address w0 = 10;    // working cell 0 (stack)
    address w24 = 20;   // print line
    address w25 = 21;   // current print column



    std::unordered_map<uint16_t, void (implementation::*)()> primitive_functions_;


    static constexpr address primitives_begin = 32000;
    static constexpr address primitives_end = 32202;
    static constexpr address h5_negative = primitives_begin + 3;
    static constexpr address h5_positive = primitives_begin + 4;

    using primitive_function = std::function<void(implementation &)>;
    std::unordered_map<uint16_t, primitive_function> primitive_functions;

    void j0_no_operation();
    void j7_halt_proceed_on_go_test();
    void j3_set_h5_negative();
    void j4_set_h5_positive();
    void j7_halt_proceed_on_go();
    void j8_restore_h0();
    void j111_h0_1_minus_h0_2();
    void j117_test_if_h0_0();
    void j125_tally_1_in_h0_0();
    void j152_print_symbol_h0();
    void j154_clear_print_line();
    std::string tbd_1w24;
    void j155_print_line();
    void j157_enter_data_term();
    void primitive_not_pmplemented();
};






interpreter::implementation::implementation(interpreter_io & io)
: io_(io)
{
    space.resize(32768);
    constexpr address available_space_end = 32000;
    for (address a = 0; a < available_space_end; ++a)
        space[a].link = a + 1;
    space[available_space_end - 1].link = nil;
    h2 = 2500;

    for (address a = primitives_begin; a != primitives_end; ++a) {
        primitive_functions_[a] = &implementation::primitive_not_pmplemented;
        space[a] = {0, 5, a, 0};
    }

    primitive_functions_[primitives_begin +   0] = &implementation::j0_no_operation;
    primitive_functions_[primitives_begin +   3] = &implementation::j3_set_h5_negative;
    primitive_functions_[primitives_begin +   4] = &implementation::j4_set_h5_positive;
    primitive_functions_[primitives_begin +   7] = &implementation::j7_halt_proceed_on_go;
    primitive_functions_[primitives_begin +   8] = &implementation::j8_restore_h0;
    primitive_functions_[primitives_begin + 111] = &implementation::j111_h0_1_minus_h0_2;
    primitive_functions_[primitives_begin + 117] = &implementation::j117_test_if_h0_0;
    primitive_functions_[primitives_begin + 125] = &implementation::j125_tally_1_in_h0_0;
    primitive_functions_[primitives_begin + 152] = &implementation::j152_print_symbol_h0;
    primitive_functions_[primitives_begin + 154] = &implementation::j154_clear_print_line;
    primitive_functions_[primitives_begin + 155] = &implementation::j155_print_line;
    primitive_functions_[primitives_begin + 157] = &implementation::j157_enter_data_term;


    space[w24] = {0, 0, 900, 0};
    space[w25] = {0, 0, 1, 0};

}



address interpreter::implementation::alloc_cell()
{
    if (h2 == nil)
        throw ipl_v_exception("SPACE EXHAUSTED.");
    address c = h2;
    h2 = space[h2].link;
    return c;
}

void interpreter::implementation::free_cell(address addr)
{
    space[addr].link = h2;
    h2 = addr;
}

void interpreter::implementation::push_down(address addr)
{
    address new_cell = alloc_cell();
    space[new_cell].p = space[addr].p;
    space[new_cell].q = space[addr].q;
    space[new_cell].symb = space[addr].symb;
    space[new_cell].link = space[addr].link;
    space[addr].link = new_cell;
}

void interpreter::implementation::pop_up(address addr)
{
    address next_cell = space[addr].link;
    if (next_cell == nil)
        throw ipl_v_exception("NOTHING TO POP UP.");
    space[addr].p = space[next_cell].p;
    space[addr].q = space[next_cell].q;
    space[addr].symb = space[next_cell].symb;
    space[addr].link = space[next_cell].link;
    free_cell(next_cell);
}

// return true iff addr is a primitive function
bool interpreter::implementation::is_primitive(address addr)
{
    return space[addr].q == 5;
}

void interpreter::implementation::execute_primitive(address primitive)
{
    auto primfunc = primitive_functions_.find(primitive);
    if (primfunc != primitive_functions_.end())
        (this->*primfunc->second)();
    else
        throw ipl_v_exception("EXECTUE PRIMITIVE FAILED TO FIND PRIMITIVE.");
}




// "J0 NO OPERATION.
//  Proceed to the next instruction."
void interpreter::implementation::j0_no_operation()
{
}

// "J1 EXECUTE (0).
//  The process, (0), is removed from H0, H0 is restored (this positions the process's
//  inputs correctly), and the process is executed (as if its name occurred in the stead of J1)."

// "J2 TEST IF (0) = (1).
//  (The identity test is on the SYMB part only; P and Q are ignored.)"

// "J3 SET H5-.
//  The symbol in H5 is replaced by the symbol J3."
void interpreter::implementation::j3_set_h5_negative()
{
    space[h5].symb = h5_negative;
}

// "J4 SET H5+.
//  The symbol in H5 is replaced by the symbol J4."
void interpreter::implementation::j4_set_h5_positive()
{
    space[h5].symb = h5_positive;
}

// "J5 REVERSE H5.
//  If H5 is +, it is set-; if H5 is - it is set +.

// "J6 REVERSE (0) and (1).
//  Permutes the symbol in H0 with the first symbol down in the H0 push down list.

// "J7 HALT, PROCEED ON GO.
//  The computer stops; if started again, it interprets the next
//  instruction in sequence."
void interpreter::implementation::j7_halt_proceed_on_go()
{
    std::cout << "HALTED AT ADDRESS "
              << space[h1].symb
              << ".\nTO RESUME EXECUTION, TYPE: GO\n"
                 "TO TERMINATE THE PROGRAM, TYPE: X\n";
    std::string s;
    std::getline(std::cin, s);
}

// "J8 RESTORE H0.
//  (Identical to 30H0, but can be executed as LINK.)"
void interpreter::implementation::j8_restore_h0()
{
    pop_up(h0);
}

// "J9 ERASE CELL (0).
//  The cell whose name is (0) is returned to tne available space list, without
//  regard to the contents of the cell."




// "J111 (1) - (2) TO (0).
//  The number (0) is set equal to the algebraic difference between numbers
//  (1) and (2). The output (0) is the input (0)."
void interpreter::implementation::j111_h0_1_minus_h0_2()
{
    address h0_0 = space[h0].symb;
    if (h0_0 == nil)
        throw ipl_v_exception("J111: (0) IS NIL");
    address h0_1 = space[space[h0].link].symb;
    if (h0_0 == nil)
        throw ipl_v_exception("J111: (1) IS NIL");
    address h0_2 = space[space[space[h0].link].link].symb;
    if (h0_2 == nil)
        throw ipl_v_exception("J111: (1) IS NIL");


    auto [p, q, symb, link] = space[h0_0];

    if (q == 0) {

    }
    else {
        switch (p) {
        case 0:
            // decimal integer
            // sign bit -- TBD
            // ints are spread over both symb and link fields -- TBD
            space[h0_0].link = space[h0_1].link - space[h0_2].link;
            pop_up(h0);
            pop_up(h0);
            space[h0].symb = h0_0;
            break;
        case 1:
            // floating point
            break;
        case 2:
            // alphanumeric
            break;
        case 3:
            // octal
            break;
        default:
            throw ipl_v_exception("J111: UNKNOWN DATA TYPE");
        }
    }
}

// "J117 TEST IF (0) = 0."
void interpreter::implementation::j117_test_if_h0_0()
{
    address addr = space[h0].symb;
    if (addr == nil)
        throw ipl_v_exception("J117: (0) IS NIL");
    auto [p, q, symb, link] = space[addr];

    if (q == 0) {

    }
    else {
        switch (p) {
        case 0:
            // decimal integer
            if (link == 0)
                space[h5].symb = h5_positive;
            else
                space[h5].symb = h5_negative;
            pop_up(h0);
            break;
        case 1:
            // floating point
            break;
        case 2:
            // alphanumeric
            break;
        case 3:
            // octal
            break;
        default:
            throw ipl_v_exception("J117: UNKNOWN DATA TYPE");
        }
    }
}

// "J125 TALLY 1 IN (0).
//  An integer 1 is added to the number (0). The type of the result is the
//  same as the type of (0). It is left as the output (0)."
void interpreter::implementation::j125_tally_1_in_h0_0()
{
    address addr = space[h0].symb;
    if (addr == nil)
        throw ipl_v_exception("J125: (0) IS NIL");
    auto [p, q, symb, link] = space[addr];

    if (q == 0) {

    }
    else {
        switch (p) {
        case 0:
            // decimal integer
            space[addr].link++;
            break;
        case 1:
            // floating point
            break;
        case 2:
            // alphanumeric
            break;
        case 3:
            // octal
            break;
        default:
            throw ipl_v_exception("J125: UNKNOWN DATA TYPE");
        }
    }
}


// "J152 PRINT SYMBOL (0).
//  The symbol (0) is printed. The format is the same as J15O, where
//  (0) is placed at SYMB, and if it names a data term, this is printed
//  to the right. Locals are handled as in J151."
void interpreter::implementation::j152_print_symbol_h0()
{
    address addr = space[h0].symb;
    if (addr == nil)
        throw ipl_v_exception("J152: (0) IS NIL");
    auto [p, q, symb, link] = space[addr];

    if (q == 0) {

    }
    else {
        switch (p) {
        case 0:
            // decimal integer
            // should print symbol name, don't yet have a sympol table -- TBD
            io_.print(std::to_string(space[addr].link) + "\n");
            break;
        case 1:
            // floating point
            break;
        case 2:
            // alphanumeric
            break;
        case 3:
            // octal
            break;
        default:
            throw ipl_v_exception("J152: UNKNOWN DATA TYPE");
        }
    }
}



// J154 CLEAR PRINT LINE.
// Print line 1W24 is cleared and the current entry column, 1W25, is set equal
// to the left margin, 1W21.
void interpreter::implementation::j154_clear_print_line()
{
    io_.print("j154_clear_print_line()\n");
}



// J155 PRINT LINE.
// Line 1W24 is printed, according to spacing control 1W22. The print line is not cleared.
void interpreter::implementation::j155_print_line()
{
    io_.print(tbd_1w24);
    io_.print("\n");
}



// J157 ENTER DATA TERM (0) LEFT-JUSTIFIED.
// Data term (0) is entered in the current print line with its leftmost character
// in print position 1W25, 1W25 is advanced, and H5 is set + . If (0) exceeds the
// remaining space, no entry is made and H5 is set - .
void interpreter::implementation::j157_enter_data_term()
{
    address addr = space[h0].symb;
    if (addr == nil)
        throw ipl_v_exception("J157: (0) IS NIL");
    auto [p, q, symb, link] = space[addr];

    int sign = 1; //TBD

    if (q == 0) {

    }
    else {
        switch (p) {
        case 0:
            // decimal integer
            break;
        case 1:
            // floating point
            break;
        case 2:
            // alphanumeric
            tbd_1w24 += "<TBD>";
            break;
        case 3:
            // octal
            break;
        default:
            throw ipl_v_exception("J157: UNKNOWN DATA TYPE");
        }
    }

    pop_up(h0);
}




void interpreter::implementation::primitive_not_pmplemented()
{
    address p = space[space[h1].symb].symb - primitives_begin;
    std::string msg{"PRIMITIVE J"};
    msg += std::to_string(p);
    msg +=  " NOT IMPLEMENTED.";
    throw ipl_v_exception(msg.c_str());
}





void interpreter::implementation::execute(address program_start)
{
    // (see page 42 of RM3739.pdf)
    h1 = 99;
    //space[h1] = {0, 0, nil, nil};
    //push_down(h1);
    space[h1] = {0, 0, program_start, 0};


    auto descend = [&](address symbol) {
        // "Preserve H1: Put S into H1 (H1 now contains the name of the
        //  cell holding the first instruction of the subprogram list);
        //  go to INTERPRET Q."
        push_down(h1);
        space[h1].symb = symbol;
    };

    auto ascend = [&](address & link) {
        // "Restore H1 (returning to H1 the name of the cell holding the
        //  current instruction, one level up); restore auxiliary region
        //  if required; go to ADVANCE."
        // [note that ADVANCE is done externally to this function]
        if (space[h1].link == nil)
            return false; // there is nothing to restore; already at top
        pop_up(h1);
        link = space[space[h1].symb].link;
        return true;
    };

    auto advance = [&](address & link) {
        // "Interpret LINK:
        //  - LINK == 0: Termination; go to ASCEND.
        //  - LINK != 0: LINK is the name of the cell containing the next
        //    instruction; put LINK in H1; go to INTERPRET Q."
        while (link == nil && ascend(link))
            ;
        if (link == nil)
            return false; // there is nothing to advance to; at end of program
        space[h1].symb = link;
        return true;
    };



    for (;;) {
        if (space[h1].symb == nil)
            throw ipl_v_exception("EXECUTE: CURRENT INSTRUCTION ADDRESS = NIL");
        ++h3;
        auto [p, q, symb, link] = space[space[h1].symb];
        // std::cout << std::setw(6) << space[h1].symb;
        // std::cout << (space[h5].symb == h5_negative ? " - " : " + ");
        // std::cout << (int)p << (int)q << " " << std::setw(6) << symb << " " << std::setw(6) << link << '\n';
        // // if (link > 0 && link < 100)
        //     break;
        // if (symb == 803)
        //     std::cout << "          ipl ackermann " << space[901].link << " " << space[902].link << "\n";


        // *** INTERPRET Q ***

        address s = symb;
        if (q == 0) {
            // "S = the symbol in the instruction itself--i.e., SYMB."
        }
        else if (q == 1) {
            // "S = the symbol in the cell named in the instruction--i.e., in SYMB."
            s = space[symb].symb;
        }
        else if (q == 2) {
            // "S = the symbol the cell named the cell named in the cell
            //  whose name is in in the instruction--i.e., in in SYMB."
            s = space[space[symb].symb].symb;
        }
        else if (q == 3) {
            // "Trace this program list (otherwise equivalent to Q = 0)." -- TBD
            // s is symb
        }
        else if (q == 4) {
            // "Continue tracing (otherwise equivalent to Q = 0)." -- TBD
            // s is symb
        }
        else if (q == 5) {
            // "SYMB is the address of a primitive--i..e., of a machine language
            //  subroutine."
            execute_primitive(symb);
            if (!(ascend(link) && advance(link)))
                break;
            continue;
        }
        else if (q == 6) {
            // "Routine is in fast-auxiliary storage."
            throw ipl_v_exception("Q = 6 IS NOT IMPLEMENTED.");
        }
        else {
            // "Routine is in slow-auxiliary storage.""
            throw ipl_v_exception("Q = 7 IS NOT IMPLEMENTED.");
        }



        // *** INTERPRET P ***

        if (p == 0) {
            // "EXECUTE S. S is assumed to name a routine or a primitive.
            //  The process it specifies is carried out."

            if (is_primitive(s)) {
                // s is a built-in primitive: execute it directly
                execute_primitive(s);
                // continue to ADVANCE
            }
            else {
                // s is a user-defined routine: descend then return to INTERPRET Q
                descend(s);
                continue;
            }
        }
        else if (p == 1) {
            // "INPUT S. The Communication Cell H0 is preserved; then a copy of S is put in H0."
            // (i.e. push down H0, then copy the symbol S (a symbol is a name, which is an address)
            // into the SYMB part of H0)

            push_down(h0);
            space[h0].symb = s;
        }
        else if (p == 2) {
            // "OUTPUT TO S. A copy of the symbol in H0 (hereafter abbreviated as (0))
            //  is put in cell S; then H0 is restored."

            space[s].symb = space[h0].symb;
            pop_up(h0);
        }
        else if (p == 3) {
            // "RESTORE S. The symbol most recently placed in the push down list of cell S
            //  is moved into S; the current symbol in S is lost."

            pop_up(s);
        }
        else if (p == 4) {
            // "PRESERVE S. A copy of the symbol in cell S is placed in the push down list of S;
            //  the symbol remains in S."

            push_down(s);
        }
        else if (p == 5) {
            // "REPLACE (0) BY S. A copy of S is put in H0; the current (0) is lost.
            //  (This is analogous to the normal "load accumulator.")"

            space[h0].symb = s;
        }
        else if (p == 6) {
            // "COPY (0) IN S. A copy of (0) is put in cell S; the current symbol in S is lost
            //  and (0) is unaffected. (This is analogous to the normal "store accumulator.")""

            space[s].symb = space[h0].symb;
        }
        else if (p == 7) {
            // "BRANCH TO S IF H5-. The symbol in H5 is always either + or -. If H5 is +, then
            //  LINK names the cell containing the next instruction to be performed. (This is
            //  the normal sequence.) If H5 is -, then S names the cell containing the next
            //  instruction to be performed."

            if (space[h5].symb == h5_negative)
                link = s;
        }



        // *** ADVANCE ***

        if (!advance(link))
            break;
    }

    io_.print("PROGRAM RAN TO COMPLETION\n");
}


unsigned interpreter::implementation::assemble(const std::string & input)
{
    unsigned error_count = 0;

    // right now this function assembles ackermann(3,6) whatever you give it for input -- TBD

    space[800] = {0, 3,   803,     801};    //  E0    03  A0            EXECUTE A0 TO COMPUTE A(M,N)
    space[801] = {1, 0,   902,     802};    //        10  N0            INPUT N0 = RESULT
    space[802] = {0, 0, 32152,       0};    //        00  J152   0      PRINT RESULT, QUIT.

    space[803] = {1, 4,   901,     804};    //  A0    14  M0            INPUT M
    space[804] = {0, 0, 32117,     805};    //        00  J117          IS M = 0
    space[805] = {1, 0,   902,     806};    //        10  N0            INPUT M (DELAY BRANCHING)
    space[806] = {7, 0,   808,     807};    //        70  9-1           BRANCH IF M NOT = 0
    space[807] = {0, 0, 32125,   32008};    //        00  J125   J8     M=0. N+1 TO N. EXIT WITH J8=30H0
    space[808] = {0, 0, 32117,     809};    //  9-1   00  J117          IS N = 0
    space[809] = {7, 0,   812,     810};    //        70  9-2           BRANCH IF N NOT = 0
    space[810] = {1, 0,   902,     811};    //        10  N0            M NOT = 0, N = 0. INPUT N
    space[811] = {0, 0, 32125,     817};    //        00  J125   9-3    SET N = 1 (STILL LEFT IN H0)
    space[812] = {1, 0,   900,     813};    //  9-2   10  K1            M,N,NOT=0.INPUT K1 FOR SUBTRACTION
    space[813] = {1, 0,   902,     814};    //        10  N0            INPUT N
    space[814] = {1, 0,   902,     815};    //        10  N0            INPUT N
    space[815] = {0, 0, 32111,     816};    //        00  J111          N-1 TO N (STILL LEFT IN H0)
    space[816] = {0, 0,   803,     817};    //        00  A0            COMPUTE A(M,N-1).  N HAS VALUE
    space[817] = {5, 0,   900,     818};    //  9-3   50  K1            COMMON TO M NOT 0. K1 REPLACES N
    space[818] = {1, 0,   901,     819};    //        10  M0            INPUT M
    space[819] = {1, 0,   901,     820};    //        10  M0            INPUT M
    space[820] = {0, 0, 32111,     821};    //        00  J111          M-1 TO M (STILL LEFT IN H0)
    space[821] = {0, 0,   803,     822};    //        00  A0            COMPUTE A(M-1,1) OR A(M-1,A(M,N-1))
    space[822] = {0, 0, 32125,   32008};    //        00  J125   J8     M+1 TO M. EXIT WITH J8=30H0

    space[900] = {0, 1,     0,       1};    //  K1    01             1  CONSTANT 1
    space[901] = {0, 1,     0,       3};    //  M0    01             3  VALUE OF M 
    space[902] = {0, 1,     0,       6};    //  N0    01             6  VALUE OF N 

/*
    TYPE  NAME  SIGN  PQ SYMB  LINK  COMMENTS

    - All fields except comment must be present. Comment is optional.
    - Any field may be populated with whitespace

    TYPE
        1 = Comment.
        5 = 
*/


    return error_count;
}


/////////////////////////////////////////////////////////////////////////////

interpreter::interpreter(interpreter_io & io)
    : impl_(std::make_unique<implementation>(io))
{
}

interpreter::~interpreter()
{
}

unsigned interpreter::assemble(const std::string & input)
{
    return impl_->assemble(input);
}

void interpreter::execute(address program_start)
{
    impl_->execute(program_start);
}


}// namespace ipl_v_cpp
