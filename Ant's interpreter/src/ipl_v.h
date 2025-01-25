#ifndef IPL_V_CPP_H_INCLUDED
#define IPL_V_CPP_H_INCLUDED


#include <memory>
#include <string>


namespace ipl_v_cpp {

struct ipl_v_exception : public std::runtime_error {
    ipl_v_exception(const char * msg) : std::runtime_error(msg) {}
};



// The interpreter will communicate with the world through this interface.
class interpreter_io {
public:
    interpreter_io() = default;
    virtual ~interpreter_io() = default;

    // get the next line of text from the world
    virtual std::string getline() = 0;

    // output an ASCII string
    virtual void print(const std::string &) = 0;

    virtual void trace_location(int) {}
};


using address = uint32_t;


class interpreter {
public:
    interpreter(interpreter_io & io);
    ~interpreter();

    unsigned assemble(const std::string & input);

    void execute(address program_start);

private:
    class implementation;
    std::unique_ptr<implementation> impl_;
};


}// namespace ipl_v_cpp


#endif
