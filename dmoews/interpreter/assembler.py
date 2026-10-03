# Python 3

import sys

from iplparser import Parser
from machine import Word
from util import complain, WARNING, ERROR

#
# Assemble IPL-V program into memory.
#
# David Moews, July 2026.  Released into the public domain, CC0.
#

#
# The assembler has the following deviations from the standard:
#  (see [MAN1964], part 2, section 18):
#
# * Cards not of types 0 (or blank), 1, or 5 are ignored.
#
# * The only cards of type 5 used should have blank NAME and LINK;
#   PQ should equal 00 or 01; SYMB should be blank or a regional symbol.
#
# * Assembly does not necessarily terminate when a card type 5
#   with a start symbol is found but will go on if possible.
#   The program will eventually start at the last start symbol read in.
#
# * Regional symbols are not allocated in blocks but are allocated as used.
#
# * Octal and floating-point data terms have not been implemented.
#

class Assembler:

    # Return start symbol.

    def read(machine, lines):

        st = None

        nameless_counter = 0
        local_table_table = {}

        def use_name():
            nonlocal nameless_counter

            if non_local_name is None:
                v = nameless_counter
                nameless_counter += 1
                return 'NONE-' + str(v)
            else:
                return non_local_name

        chunk = []
        non_local_name = None

        for l in lines:

            # Comment, ignore
            if l.tp == '1':
                continue

            if l.tp not in [' ', '0']:
                if chunk != []:
                    n = use_name()
                    local_table_table[n] = \
                        Assembler.read_chunk(n, machine, chunk)
                chunk = []
                non_local_name = None

                if not (l.tp == '5' and l.name == '' and l.link == ''
                                    and l.p in [0, -1] and l.q in [-1, 0, 1]):
                    # Card type not implemented
                    complain(WARNING, l.filename, l.line_no,
                             'Unimplemented type %s card' % l.tp)
                else:
                    if l.symb != '':
                        if not Parser.is_regional(l.symb):
                            complain(ERROR, l.filename, l.line_no,
                       'Non-regional symbol %s as start address' % symb)
                        else:
                            if st is not None:
                                complain(WARNING, l.filename, l.line_no,
                               'Changing start from %s to %s' % (st, l.symb))
                            st = l.symb
            else:
                if not Parser.is_local(l.name):
                    if chunk != []:
                        n = use_name()
                        local_table_table[n] = \
                            Assembler.read_chunk(n, machine, chunk)
                    chunk = []
                    non_local_name = l.name

                chunk.append(l)

        if chunk != []:
            n = use_name()
            local_table_table[n] = \
                Assembler.read_chunk(n, machine, chunk)

        for k in machine.symbols.keys():
            if k not in machine.is_defined:
                complain(ERROR, lines[-1].filename, lines[-1].line_no,
                         'Undefined symbol %s' % k)

        # Add local names to global table
        # Use Shrager's convention of prepending section name
        for name, local_table in local_table_table.items():
            for n, v in local_table.items():
                fn = name + '-' + n
                assert v not in machine.anti_symbols
                machine.anti_symbols[v] = fn
                assert fn not in machine.symbols
                machine.symbols[fn] = v

        return st

    # Returns local symbol table
    def read_chunk(section_name, machine, chunk):

        def get_address(filename, line_no, is_defining, name):
            if Parser.is_local(name):
                if is_defining and name in local_is_defined:
                    complain(ERROR, filename, line_no,
                             'Redefinition of local name %s' % name)
                if name not in local_table:
                    local_table[name] = len(machine.memory)
                    machine.memory.append(Word.new_word())
                if is_defining:
                    local_is_defined.add(name)
                return local_table[name]
            else:
                if is_defining and name in machine.is_defined:
                    if Parser.is_internal(name):
                         complain(ERROR, filename, line_no,
                             'Redefinition of internal name %s' % name)
                    else:
                        assert Parser.is_regional(name)
                        complain(WARNING, filename, line_no,
                             'Redefinition of regional name %s' % name)
                if name not in machine.symbols:
                    machine.symbols[name] = len(machine.memory)
                    machine.anti_symbols[len(machine.memory)] = name
                    machine.memory.append(Word.new_word())
                if is_defining:
                    machine.is_defined.add(name)
                return machine.symbols[name]

        assert chunk != []

        if section_name[ : 4] == 'NONE':
            complain(WARNING, chunk[0].filename, chunk[0].line_no,
                     'Assembling unreachable nameless section')

        local_table = {}
        local_is_defined = set()

        if chunk[0].name != '':
            next_address = get_address(chunk[0].filename, chunk[0].line_no,
                                       True, chunk[0].name)
        else:
            next_address = len(machine.memory)
            machine.memory.append(Word.new_word())

        for i, l in enumerate(chunk):

            pq = (0 if l.p == -1 else l.p) * 8 + (0 if l.q == -1 else l.q)

            addr = next_address

            if i != len(chunk) - 1:
                if chunk[i + 1].name != '':
                    next_address = get_address(chunk[i + 1].filename,
                                               chunk[i + 1].line_no,
                                               True, chunk[i + 1].name)
                else:
                    next_address = len(machine.memory)
                    machine.memory.append(Word.new_word())
            else:
                next_address = 0

            if l.data is not None:
                assert l.symb == '' and l.link == ''
                machine.memory[addr] = Word(pq, None, None, l.data)
            else:
                if l.symb != '':
                   symb_addr = get_address(l.filename, l.line_no, False, l.symb)
                else:
                    if i == len(chunk) - 1:
                        complain(WARNING, l.filename, l.line_no,
                                 'Zeroed blank symbol at section end')
                    symb_addr = next_address

                if l.link != '':
                   link_addr = get_address(l.filename, l.line_no, False, l.link)
                else:
                    if i == len(chunk) - 1:
                        complain(WARNING, l.filename, l.line_no,
                                 'Zeroed blank link at section end')
                    link_addr = next_address

                if l.is_this_data:
                    pq &= 0o70
                    if Parser.is_internal(l.symb):
                        pq |= 0o04
                    elif Parser.is_local(l.symb):
                        pq |= 0o02
                    else:
                        assert Parser.is_regional(l.symb)
                        pass

                machine.memory[addr] = Word.w(pq, symb_addr, link_addr)

        for k in local_table.keys():
            if k not in local_is_defined:
                complain(WARNING, chunk[-1].filename, chunk[-1].line_no,
                         'Undefined local symbol %s' % k)

        return local_table
