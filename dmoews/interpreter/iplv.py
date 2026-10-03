# Python 3

#
# Interpreter for IPL-V (partial)
#
# Driver program.
#

# David Moews, July 2026.  Released into the public domain, CC0.

import sys

from machine import Machine
from assembler import Assembler
from iplparser import Parser
from remove_ws import remove_ws
import util

def usage(filename):
    print('''Usage: python3 %s [-h] [--help]
               [--[no-]remove-ws] [--[no-]extra-syntax] [ filename ]
               [ [--[no-]remove-ws] [--[no-]extra-syntax] filename ... ]
''' % filename, file = sys.stderr)
    print('''Run the IPL-V interpreter on the source code given in the standard input
or source file or files.  A filename of '-' is interpreted as the standard
input.  Some options are per source code filename and should be given before
the corresponding filename; they may persist from filename to filename.''',
file = sys.stderr)
    print('''
Options:
  -h, --help         show this help message and exit.
  --remove-ws        remove W temporaries (per-filename.)
  --no-remove-ws     don't remove W temporaries (per-filename.)
  --extra-syntax     syntactical extensions (per-filename.)
  --no-extra-syntax  no syntactical extensions (per-filename.)

If enabled, the syntactical extensions to standard IPL-V are:

* Lines beginning with # are comments and ignored.
* Lines beginning with % are treated as if they began with
  42 blanks instead of %.
''', file = sys.stderr)

def main():

    fn = sys.argv[0]
    do_rm_ws = do_syntax = False
    fns = []

    for s in sys.argv[1 : ]:
        match s:
            case '--help' | '-h':
                usage(fn)
                exit()

            case '--remove-ws':
                do_rm_ws = True

            case '--extra-syntax':
                do_syntax = True

            case '--no-remove-ws':
                do_rm_ws = False

            case '--no-extra-syntax':
                do_syntax = False

            case '-':
                fns.append((do_rm_ws, do_syntax, None))

            case _:
                if s[ : 1] == '-':
                    print("Invalid option '%s'." % s, file = sys.stderr)
                    print(file = sys.stderr)
                    usage(fn)
                    exit(1)

                fns.append((do_rm_ws, do_syntax, s))

    if fns == []:
        fns.append((do_rm_ws, do_syntax, None))

    machine = Machine.new_machine()

    all_lines = []

    for do_rm_ws, do_syntax, fn in fns:
        lines = util.get_unparsed_lines(fn)
        if do_syntax:
            lines = util.remove_extensions(lines)
        lines = Parser.parser(lines)
        if do_rm_ws:
            lines = remove_ws(lines)
        all_lines.extend(lines)

    start_symb = Assembler.read(machine, all_lines)
    start_addr = machine.symbols.get(start_symb, None)

    if start_addr is not None:
        machine.memory[machine.h1].symb = start_addr
        print('**Start at', start_symb, '=', str(start_addr) + '.',
              file = sys.stderr)
    else:
        util.complain(util.ERROR, None, -1,
                      'Undefined starting address' +
                      (' ' + start_symb if start_symb is not None else ''))
        exit()

    while machine.cycle():
        pass

if __name__ == '__main__':
    main()
