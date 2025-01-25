#include "ipl_v.h"


#include <iostream>



namespace micro_test_library {

/*  Define test functions with DEF_TEST_FUNC(function_name).
    Use TEST_EQUAL(value, expected_value) to test expected outcomes.
    Execute all test functions with RUN_TESTS(). */


// (used in test_equal() when called by test functions in this particular module)
template <typename T, size_t N>
std::ostream & operator<<(std::ostream & os, const std::array<T, N> & arr)
{
    os << '(';
    for (auto a : arr)
        os << a << ' ';
    os << ')';
    return os;
}

// (used in test_equal() when called by test functions in this particular module)
template <typename T>
std::ostream & operator<<(std::ostream & os, const std::vector<T> & vec)
{
    os << '(';
    for (auto v : vec)
        os << v << ' ';
    os << ')';
    return os;
}


unsigned test_count;      // total number of tests executed
unsigned fault_count;     // total number of tests that fail
std::vector<void (*)()> test_routines; // list of all test routines


// write a message to std::cout if !(value == expected_value)
template<typename A, typename B>
void test_equal(const A & value, const B & expected_value,
    const char * filename, const size_t line_num, const char * function_name)
{
    ++test_count;
    if (!(value == expected_value)) {
        ++fault_count;
        // e.g. love.cpp(2021) : in proposal() expected 'Yes!', but got 'no lol'
        std::cout
            << filename << '(' << line_num
            << ") : in " << function_name
            << "() expected '" << expected_value
            << "', but got '" << value
            << "'\n";
    }
}


// register a test function; return an arbitrary value
size_t add_test(void (*f)())
{
    test_routines.push_back(f);
    return test_routines.size();
}


// run all registered tests
void run_tests()
{
    for (auto & t : test_routines)
        t();
    if (fault_count)
        std::cout << fault_count << " total failures\n";
}


// write a message to std::cout if !(value == expected_value)
#define TEST_EQUAL(value, expected_value)                   \
{                                                           \
    micro_test_library::test_equal(value, expected_value,   \
        __FILE__, __LINE__, __FUNCTION__);                  \
}


// To allow test code to be placed nearby code being tested, test functions
// may be defined with this macro. All such functions may then be called
// with one call to RUN_TESTS(). Each test function must have a unique name.
#define DEF_TEST_FUNC(test_func)                                         \
void micro_test_##test_func();                                                        \
size_t micro_test_extern_##test_func = micro_test_library::add_test(micro_test_##test_func); \
void micro_test_##test_func()


// execute all the DEF_TEST_FUNC defined functions
#define RUN_TESTS() micro_test_library::run_tests()

} //namespace micro_test_library






class interpreter_io_console : public ipl_v_cpp::interpreter_io {
public:
    interpreter_io_console() {}
    virtual ~interpreter_io_console() {}

    std::string getline() override
    {
        std::string buf;
        std::getline(std::cin, buf);
        return buf;
    }

    void print(const std::string & msg) override { std::cout << msg; }
};


class interpreter_io_test_stream : public ipl_v_cpp::interpreter_io {
public:
    interpreter_io_test_stream(
        const std::vector<std::string> & expected_output,
        bool show_test_output = false)
    : expected_output_(expected_output), show_test_output_(show_test_output) {}

    virtual ~interpreter_io_test_stream()
    {
        // Were all expected messages printed?
        TEST_EQUAL(index_, expected_output_.size());
    }

    std::string getline() override
    {
        return "";
    }

    void print(const std::string & msg) override
    {
        if (show_test_output_)
            std::cout << msg;

        TEST_EQUAL(index_ < expected_output_.size(), true);
        if (index_ < expected_output_.size()) {
            TEST_EQUAL(msg, expected_output_[index_]);
            ++index_;
        }
    }

private:
    std::vector<std::string> expected_output_;
    unsigned index_ = 0;
    bool show_test_output_;
};



DEF_TEST_FUNC(ackermann)
{
    interpreter_io_test_stream io {{
        "509\n",                          // should be "N                509\n" -- TBD
        "PROGRAM RAN TO COMPLETION\n"
    }, true};

    ipl_v_cpp::interpreter ipl_v(io);


    /*  The Ackermann example program from page 42 of

        INFORMATION PROCESSING LANGUAGE V MANUAL
        Section I. The Elements of IPL Programming
        A. Newell, et al, May 16, 1960

        [The original example had A(1,1), changed here
         to A(3,6) to work the interpreter a litte harder.]
    */

    // NB: change interpreter::assemble(), not this input -- TBD
    TEST_EQUAL(ipl_v.assemble(
        //  NAME  PQ  SYMB  LINK    COMMENT
        "                           ACKERMANN-S FUNCTION IN IPL-V       \n"
        "                           GIVEN M AND N, COMPUTE A(M,N)       \n"
        "                           A(0,N) = N+1                        \n"
        "                           A(M,0) = A(M-1,1)                   \n"
        "                           A(M,N) = A(M-1,A(M,N-1))            \n"
        "                           TRACE ALL ROUTINES                  \n"
        "                           PRINT RESULT                        \n"
        "                                                               \n"
        "   E0    03  A0            EXECUTE A0 TO COMPUTE A(M,N)        \n"
        "         10  N0            INPUT N0 = RESULT                   \n"
        "         00  J152   0      PRINT RESULT, QUIT.                 \n"
        "                                                               \n"
        "   A0    14  M0            INPUT M                             \n"
        "         00  J117          IS M = 0                            \n"
        "         10  N0            INPUT M (DELAY BRANCHING)           \n"
        "         70  9-1           BRANCH IF M NOT = 0                 \n"
        "         00  J125   J8     M=0. N+1 TO N. EXIT WITH J8=30H0    \n"
        "   9-1   00  J117          IS N = 0                            \n"
        "         70  9-2           BRANCH IF N NOT = 0                 \n"
        "         10  N0            M NOT = 0, N = 0. INPUT N           \n"
        "         00  J125   9-3    SET N = 1 (STILL LEFT IN H0)        \n"
        "   9-2   10  K1            M,N,NOT=0.INPUT K1 FOR SUBTRACTION  \n"
        "         10  N0            INPUT N                             \n"
        "         10  N0            INPUT N                             \n"
        "         00  J111          N-1 TO N (STILL LEFT IN H0)         \n"
        "         00  A0            COMPUTE A(M,N-1).  N HAS VALUE      \n"
        "   9-3   50  K1            COMMON TO M NOT 0. K1 REPLACES N    \n"
        "         10  M0            INPUT M                             \n"
        "         10  M0            INPUT M                             \n"
        "         00  J111          M-1 TO M (STILL LEFT IN H0)         \n"
        "         00  A0            COMPUTE A(M-1,1) OR A(M-1,A(M,N-1)) \n"
        "         00  J125   J8     M+1 TO M. EXIT WITH J8=30H0         \n"
        "                                                               \n"
        "   K1    01             1  CONSTANT 1                          \n"
        "   M0    01             3  VALUE OF M                          \n"
        "   N0    01             6  VALUE OF N                          \n"
    ), 0); // no errors in assembly expected

    // run it (number is address of program start)
    ipl_v.execute(800);
}




int main()
{
    try {
        RUN_TESTS();

        std::cout
            << "number of tests " << micro_test_library::test_count
            << ", failures " << micro_test_library::fault_count << "\n";
    }
    catch (const ipl_v_cpp::ipl_v_exception & e) {
        std::cerr << "exception: " << e.what() << std::endl;
        return EXIT_FAILURE;
    }
}
