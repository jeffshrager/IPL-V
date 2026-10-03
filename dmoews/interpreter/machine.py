# Python 3

#
# Interpreter for IPL-V (partial)
#
# Machine class with basic interpretative loop
# and primitives used to implement the J-functions.
#

# David Moews, July 2026.  Released into the public domain, CC0.

from __future__ import annotations
from collections import deque
from dataclasses import dataclass

import sys

from iplparser import Parser

type Address = int

# Enters characters of string T into S at offset OFS.
# May pad S with blanks.
def enter_string(s, t, ofs):
    assert ofs >= 0
    if ofs > len(s):
        s += ' ' * (ofs - len(s))
    return s[ : ofs] + t + s[ofs + len(t) : ]

@dataclass
class Word:
    pq: int                       # 0 to 63
    symb: None | Address          # None only for data terms
    link: None | Address          # None only for data terms
    data: None | type.EllipsisType | int | float | str
                                  # not None only for data terms
                                  # ... is used for data terms of unknown type

    def copy(self):
        return Word(self.pq, self.symb, self.link, self.data)

    def w(pq, s, l):    # Normal (non-DT) cell
        return Word(pq, s, l, None)

    def new_word():
        return Word(4, 0, 0, None)

# For the basic IPL-V interpretive loop see:
# [MAN1964], section 3.10, p. 159 ff.

@dataclass
class Machine:
    memory: list[Word]
    level: int
    anti_symbols: dict[int, str]
    symbols: dict[str, int]
    is_defined: set[str]

    h0: int = 10 # SP
    h1: int = 11 # PC
    h2: int = 12 # Free cell list
    h3: int = 13 # Cycle counter
    h5: int = 14 # Test cell (+/-)

    j3: int = 15    # Reserve 2 cells for J3 routine
    j4: int = 17    # Reserve 2 cells for J4 routine

    h_minus: int = j3
    h_plus: int = j4

    initial_size: int = 19

    ll_routines: frozenset[int] = \
        frozenset([1, 2, 7, 9, 17, 18, 60, 62, 72, 74,
                   90, 110, 111, 112, 113, 114, 117, 118, 119,
                   120, 121, 128, 131, 132, 133, 134, 135, 136,
                   150, 151, 152, 153, 154, 155, 156, 157, 158,
                   159, 160, 161, 180])

    # External symbols 0-9 are always defined and absolute
    # ([MAN1964], section 18.5, p. 226)
    def initial_symbols():
        return ( { 'H0': Machine.h0,
                   'H1': Machine.h1,
                   'H2': Machine.h2,
                   'H3': Machine.h3,
                   'H5': Machine.h5,
                   'J3': Machine.j3,
                   'J4': Machine.j4 }
                 | { str(x) : x for x in range(10) }
                 | { '@' + str(x) : -x for x in Machine.ll_routines } )

    def prettyprint(self, addr):
        return self.anti_symbols.get(addr, str(addr))

    # Return regional name or printed form of absolute address;
    # absolute address form begins with space
    def pp_no_local(self, addr):
        s = self.anti_symbols.get(addr, str(addr))
        return s if Parser.is_regional(s) else ' ' + str(addr)

    def pq(self, x):
        return self.memory[x].pq

    def symb(self, x):
        return self.memory[x].symb

    def link(self, x):
        return self.memory[x].link

    def data(self, x):
        return self.memory[x].data

    # Is it a data term?

    def is_dt(self, addr):
        if self.data(addr) is None:
            assert self.symb(addr) is not None
            assert self.link(addr) is not None
            return False
        else:
            assert self.symb(addr) is None
            assert self.link(addr) is None
            return True

    # Subtypes of data terms

    def is_integer_dt(self, addr):
        return self.is_dt(addr) and type(self.data(addr)) is type(0)

    def is_float_dt(self, addr):
        return self.is_dt(addr) and type(self.data(addr)) is type(0.0)

    def is_numeric_dt(self, addr):
        return self.is_integer_dt(addr) or self.is_float_dt(addr)

    def is_string_dt(self, addr):
        return self.is_dt(addr) and type(self.data(addr)) is type('')

    def start_at(self, addr):
        self.memory[self.h1].symb = addr

    # Return a cell to the available space list.
    # See section 9.1, p. 180 of [MAN1964]
    # for the exact definition of these operations.
    def add_free(self, v):
        self.memory[v] = self.memory[self.h2].copy()
        self.memory[self.h2].link = v

    # Get a new cell from the available space list.
    # See section 9.1, p. 180 of [MAN1964]
    # for the exact definition of these operations.
    def new_cell(self):
        rv = self.memory[Machine.h2].link
        if rv == 0:
            rv = len(self.memory)
            self.memory.append(Word.new_word())
        else:
            self.memory[Machine.h2].link = self.link(rv)
            self.memory[rv] = Word.new_word()
        return rv

    # Preserve.  See section 9.1, p. 180 of [MAN1964]
    # for the exact definition of these operations.
    def preserve(self, address, pq, v):
        n = self.new_cell()
        self.memory[n] = self.memory[address].copy()
        self.memory[address].pq = pq
        self.memory[address].symb = v
        self.memory[address].link = n

    # Restore.  See section 9.1, p. 180 of [MAN1964]
    # for the exact definition of these operations.
    def restore(self, address):
        pq = self.pq(address)
        v = self.symb(address)
        if self.link(address) == 0:
            # Popping an empty stack.
            print('**Warning: Popping an empty stack', file = sys.stderr)
            self.memory[address].pq = 4
            self.memory[address].symb = 0
        else:
            n = self.memory[address].link
            self.memory[address] = self.memory[n].copy()
            self.add_free(n)
        return pq, v

    def new_machine():
        #
        # It's a violation of the type system to put None in memory,
        # but it hopefully will catch invalid dereferencing attempts.
        #
        m = Machine([None] * 10 +
                    [Word.new_word()
                        for _ in range(Machine.initial_size - 10)],
                    1,
                    {v : k for k, v in Machine.initial_symbols().items()},
                    Machine.initial_symbols(),
                    set(Machine.initial_symbols().keys()))

        # J3 routine
        m.memory[Machine.j3    ] = Word.w(0o10, Machine.j3, Machine.j3 + 1)
        m.memory[Machine.j3 + 1] = Word.w(0o20, Machine.h5, 0)

        # J4 routine
        m.memory[Machine.j4    ] = Word.w(0o10, Machine.j4, Machine.j4 + 1)
        m.memory[Machine.j4 + 1] = Word.w(0o20, Machine.h5, 0)

        # Start cycle counter at 0
        m.memory[Machine.h3]     = Word(0o01, None, None, 0)

        return m

    def start_trace(self):
        pass # NIY

    def continue_trace(self):
        pass # NIY

    def advance(self, next_insn):
        while next_insn == 0:
            if self.link(self.h1) == 0:
                return False
            self.restore(self.h1)
            insn = self.symb(self.h1)
            next_insn = self.link(insn)
            self.level -= 1
            # Returning does not seem to cause another H3 increment,
            # contrary to what you might suspect from the manual
            # ([MAN1964], section 3.15 and 3.16, pp. 164-165)
        self.memory[Machine.h1].symb = next_insn
        self.memory[Machine.h3].data += 1
        return True

    def erase_list_structure(self, v):
        if v == 0:
            return
        to_do = [v]
        done = set([0, v])
        while len(to_do) != 0:
            s = to_do.pop()
            t = self.link(s)
            if t is None:
                # Data term
                assert self.symb(s) is None
                assert self.data(s) is not None
            else:
                assert self.data(s) is None
                if t not in done:
                    to_do.append(t)
                    done.add(t)
                t = self.symb(s)
                if self.pq(s) & 7 == 2 and t not in done:
                    to_do.append(t)
                    done.add(t)
            self.add_free(s)

    def copy_list_structure(self, v):
        if v == 0:
            return 0
        copy_map = {v : self.new_cell(), 0 : 0}
        to_do = [v]
        while len(to_do) != 0:
            s = to_do.pop()
            s_new = copy_map[s]
            self.memory[s_new] = self.memory[s].copy()
            t = self.link(s)
            if t is None:
                # Data term
                assert self.symb(s) is None
                assert self.data(s) is not None
                continue
            assert self.data(s) is None
            t_new = copy_map.get(t, None)
            if t_new is None:
                t_new = copy_map[t] = self.new_cell()
                to_do.append(t)
            self.memory[s_new].link = t_new
            if self.pq(s) & 7 == 2:
                t = self.symb(s)
                t_new = copy_map.get(t, None)
                if t_new is None:
                    t_new = copy_map[t] = self.new_cell()
                    to_do.append(t)
                self.memory[s_new].symb = t_new
        return copy_map[v]


    # Just print list (not structure) if print_structure
    # is False.
    def print_list_structure(self, pq, v, print_structure):

        #
        # For J150, local sublists are renumbered and assigned
        # new local names.  Also for J150 symbols seem to be named
        # locally (if q = 2), regionally if possible otherwise
        # absolute (q = 0) or by an absolute address (if q = 4.)
        # For J151 we don't do this but just print regionally
        # if possible, otherwise absolute.
        #
        def addr_name(pq, s):
            if pq == -1:
                return ('', '')
            elif not print_structure or pq & 7 == 0:
                return ('', self.pp_no_local(s))
            elif pq & 7 == 2:
                return (' ' + str(s), '9' + str(local_dir[s]))
            else:
                return ('', ' ' + str(s))

        def do_print(pq, s):
            addr, loc = addr_name(pq, s)
            if self.is_dt(s):
                ss = s
                new_pq = -1
                s_name = ''
            else:
                ss = self.symb(s)
                new_pq = self.pq(s)
                _, s_name = addr_name(new_pq, ss)
            self.print_symbol(addr, loc, new_pq, ss, s_name, False)

        examined = set([v])
        to_examine = deque([(pq, v)])
        local_dir = {}
        local_ctr = 0
        if print_structure and pq & 7 == 2:
            local_dir[v] = 0
            local_ctr = 1
        print(' ' + ('LOCAL' if print_structure else '     ')
                  + '  NAME  IPL SYMBOL    DATA TERM')
        print(' ' + ('ADDR.' if print_structure else '     ')
                  + '        P Q  SYMB  QP     VALUE')
        while len(to_examine) != 0:
            list_examined = set()
            is_loop = False
            pq, s = to_examine.popleft()
            while s != 0 and not self.is_dt(s):
                if s in list_examined:
                    is_loop = True
                    break
                else:
                    list_examined.add(s)
                t_pq = self.pq(s)
                if t_pq & 7 == 2 and print_structure:
                    t = self.symb(s)
                    if t not in local_dir:
                        local_dir[t] = local_ctr
                        local_ctr += 1
                    if t not in examined:
                        to_examine.append((t_pq, t))
                        examined.add(t)
                do_print(pq, s)
                pq = -1
                s = self.link(s)
            if is_loop:
                print('***Loopy list')
            elif s != 0:
                assert self.is_dt(s)
                do_print(pq, s)

    # Print the data in a data term
    def print_data(self, s):
        if s == 0 or not (self.is_integer_dt(s) or self.is_string_dt(s)):
            print('          0', end = '')
        else:
            d = self.data(s)
            if type(d) == type(''):
                print('      ' + d, end = '')
            elif type(d) == type(0):
                s_d = str(d).translate({45: "'"})
                print('%11s' % s_d, end = '')
            else:
                # Shouldn't happen
                assert False

    def print_symbol(self, addr, local_name, pq, s, s_name, only_print_dt):
            if only_print_dt:
                print(27 * ' ', end = '')
                self.print_data(s)
                print()
                return
            print(' %1s%4s %1s%4s  %1s %1s  %1s%4s' %
                   (addr[ : 1], addr[1 : ],
                    local_name[: 1], local_name[1 : ],
                    str(pq >> 3) if pq >= 0 else '',
                    str(pq & 7) if pq >= 0 else '',
                    s_name[: 1], s_name[1 : ]),
                  end = '')
            if s != 0 and self.is_dt(s):
                print(' %1d%1d' % (self.pq(s) & 7, self.pq(s) >> 3),
                      end = '')
                self.print_data(s)
            print()

    # Return values from machine_routine()

    M_NORMAL: int = 0
    M_HALT: int = 1

    def machine_routine(s, m_no):
        s.memory[s.h3].data -= 1
        match m_no:
            case -1:
            # CRASH, UNDEFINED
                assert False

            case -2:
            # TEST IF (0) = (1)
            # 2 inputs, 0 outputs
                _, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                s.memory[s.h5].symb = s.h_plus if v0 == v1 else s.h_minus

            case -7:
            # HALT, PROCEED ON GO
            # No inputs or outputs
                return Machine.M_HALT

            case -9:
            # ERASE CELL (0)
            # 1 input, 0 outputs
                _, v = s.restore(s.h0)
                s.add_free(v)

            case -17:
            # INCREMENT MACHINE ADDRESS IN (0)
            # 1 input and output
                s.memory[s.h0].symb += 1

            case -18:
            # DECREMENT MACHINE ADDRESS IN (0)
            # 1 input and output
                s.memory[s.h0].symb -= 1

            case -60:
            # GET LINK (used in J60)
            # Type of GET LINK is always internal (differs from J193)
            # 1 input and output
                s.memory[s.h0].pq = 4
                s.memory[s.h0].symb = s.link(s.symb(s.h0))

            case -62:
            # REPLACE LINK: cell pointed to by (0) has link
            # changed to (1); same as J197
            # 2 inputs, 0 outputs
                _, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                s.memory[v0].link = v1

            case -72:
            # ERASE LIST STRUCTURE
            # 1 input, 0 outputs
                _, v0 = s.restore(s.h0)
                s.erase_list_structure(v0)

            case -74:
            # COPY LIST STRUCTURE
            # Doesn't change types as prescribed in J74
            # (this is done by the library)
            # 1 input and output
                s.memory[s.h0].symb = s.copy_list_structure(s.memory[s.h0].symb)

            case -90:
            # CREATE A LIST OF 0 SYMBOLS
            # 0 inputs, 1 output
                s.preserve(s.h0, 4, s.new_cell())

            case -110 | -111 | -112:
            # ADD (-110), SUBTRACT (-111) or MULTIPLY (-112)
            # data term pointed to by (1)
            # to, from or into data term pointed to by (0).
            # Result will be float if either (0) or (1) float,
            # and otherwise integer.
            # 2 inputs, 0 outputs
                _, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                assert s.is_numeric_dt(v0)
                assert s.is_numeric_dt(v1)
                if m_no == -110:
                    s.memory[v0].data += s.memory[v1].data
                elif m_no == -111:
                    s.memory[v0].data -= s.memory[v1].data
                else:
                    s.memory[v0].data *= s.memory[v1].data
                s.memory[v0].pq = \
                          0o11 if type(s.memory[v0].data) == type(0.0) \
                     else 0o01

            case -113:
            # DIVIDE INTEGER DT pointed to by (1)
            #   INTO INTEGER DT pointed to by (0),
            # and place the remainder in integer DT (2).
            # 3 inputs, 0 outputs.
                _, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                _, v2 = s.restore(s.h0)
                assert s.is_integer_dt(v0)
                assert s.is_integer_dt(v1)
                assert s.is_integer_dt(v2)
                if s.memory[v1].data == 0:
                   print('**Error: attempt to divide by zero', file = sys.stderr)
                else:
                   s.memory[v2].data = s.memory[v0].data % s.memory[v1].data
                   s.memory[v0].data //= s.memory[v1].data

            case -114:
            # TEST CELL IDENTITY of cells ptd to by (0), (1)
            # 2 inputs, 0 outputs
                _, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                c0 = s.memory[v0]
                c1 = s.memory[v1]
                if (c0.pq == c1.pq and c0.symb == c1.symb
                                   and c0.link == c1.link
                                   and c0.data == c1.data):
                    s.memory[s.h5].symb = s.h_plus
                else:
                    s.memory[s.h5].symb = s.h_minus

            case -117:
            # TEST ORDER of numeric DTs pointed to by (0), (1)
            # Absolute internal symbols 0, 1, and 2 are returned
            # if (0) < (1), (0) = (1), or (0) > (1).
            # 2 inputs, 1 output
                _, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                assert s.is_numeric_dt(v0)
                assert s.is_numeric_dt(v1)
                n0 = s.memory[v0].data
                n1 = s.memory[v1].data
                ans = 0 if n0 < n1 else 2 if n0 > n1 else 1
                s.preserve(s.h0, 4, ans)

            case -118:
            # TEST if (0) POINTS TO INTEGRAL DT
            # (note: looks at internal data, not PQ)
            # 1 input, no outputs
                _, v0 = s.restore(s.h0)
                t = s.is_integer_dt(v0)
                s.memory[s.h5].symb = s.h_plus if t else s.h_minus

            case -119:
            # TEST if (0) POINTS TO FLOATING DT
            # (note: looks at internal data, not PQ)
            # 1 input, no outputs
                _, v0 = s.restore(s.h0)
                t = s.is_float_dt(v0)
                s.memory[s.h5].symb = s.h_plus if t else s.h_minus

            case -120:
            # TEST if (0) POINTS TO STRING DT
            # (note: looks at internal data, not PQ)
            # 1 input, no outputs
                _, v0 = s.restore(s.h0)
                t = s.is_string_dt(v0)
                s.memory[s.h5].symb = s.h_plus if t else s.h_minus

            case -121:
            # SET (0) IDENTICAL TO (1): take contents of cell (1) and put
            # in cell (0); output = input (0)
            # 2 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                s.memory[v0] = s.memory[v1].copy()
                s.preserve(s.h0, pq, v0)

            case -128:
            # TRANSLATE (0) TO BE DATA TYPE OF (1)
            # (0) is assumed to point to a data term,
            # which is translated to match the type
            # of the data term pointed to by (1).
            # The output is the translated input (0).
            #
            # This may create nonstandard string data terms
            # whose length is not 5.
            #
            # 2 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                assert s.is_dt(v0) and s.is_dt(v1)
                if s.is_integer_dt(v0) and s.is_float_dt(v1):
                    assert s.pq(v0) == 0o01
                    s.memory[v0].pq = 0o11
                    s.memory[v0].data = float(s.memory[v0].data)
                elif s.is_float_dt(v0) and s.is_integer_dt(v1):
                    assert s.pq(v0) == 0o11
                    s.memory[v0].pq = 0o01
                    s.memory[v0].data = int(s.memory[v0].data)
                elif s.is_numeric_dt(v0) and s.is_string_dt(v1):
                    assert s.pq(v0) in [0o01, 0o11]
                    s.memory[v0].pq = 0o21
                    s.memory[v0].data = str(s.memory[v0].data)
                elif s.is_string_dt(v0) and s.is_integer_dt(v1):
                    assert s.pq(v0) == 0o21
                    try:
                        s.memory[v0].data = int(s.memory[v0].data)
                        s.memory[v0].pq = 0o01
                    except ValueError:
                        pass
                elif s.is_string_dt(v0) and s.is_float_dt(v1):
                    assert s.pq(v0) == 0o21
                    try:
                        s.memory[v0].data = float(s.memory[v0].data)
                        s.memory[v0].pq = 0o11
                    except ValueError:
                        pass
                else:
                    pass
                s.preserve(s.h0, pq, v0)

            case -131:
            # GET Q of (0)
            # Q returned as absolute internal symbol.
            # 1 input and output.
                s.memory[s.h0].symb = s.memory[s.h0].pq & 7
                s.memory[s.h0].pq = 4

            case -132:
            # SET Q of (0) to (1), put in (0);
            # Q passed as absolute internal symbol
            # 2 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                new_q = v1 & 7
                pq = (pq & 0o70) | new_q
                s.preserve(s.h0, pq, v0)

            case -133:
            # GET P of (0)
            # P returned as absolute internal symbol.
            # 1 input and output.
                s.memory[s.h0].symb = s.memory[s.h0].pq >> 3
                s.memory[s.h0].pq = 4

            case -134:
            # SET P of (0) to (1), put in (0);
            # P passed as absolute internal symbol
            # 2 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                new_p = v1 & 7
                pq = (pq & 0o07) | (new_p << 3)
                s.preserve(s.h0, pq, v0)

            case -135:
            # GET Q of *(0)
            # Q returned as absolute internal symbol.
            # Like -131 but indirect.
            # 1 input and output.
                v = s.memory[s.h0].symb
                s.memory[s.h0].symb = s.memory[v].pq & 7
                s.memory[s.h0].pq = 4

            case -136:
            # GET P of *(0)
            # Q returned as absolute internal symbol.
            # like -133 but indirect
            # 1 input and output.
                v = s.memory[s.h0].symb
                s.memory[s.h0].symb = s.memory[v].pq >> 3
                s.memory[s.h0].pq = 4

            #
            # Printing
            #

            case -150:
            # PRINT LIST STRUCTURE/LIST (1)
            # Prints list structure if (0) = 0, o.w. list
            # 2 inputs, 0 outputs.
                _, v0 = s.restore(s.h0)
                pq, v1 = s.restore(s.h0)
                s.print_list_structure(pq, v1, v0 == 0)

            case -151:
            # PRINT SYMBOL/DATA TERM (1)
            # Data terms printed without name or type
            # Prints data term structure if (0) = 0, o.w. symbol
            # 2 inputs, 0 outputs.
                _, v0 = s.restore(s.h0)
                pq, v1 = s.restore(s.h0)
                s_nm = s.pp_no_local(v1)
                s.print_symbol('', '', pq, v1, s_nm, v0 == 0)

            #
            # Manipulation functions used in I/O.
            # They use nonstandard string data terms whose length
            # is not 5.
            #

            case -152:
            # ENTER STRING (1) INTO (0) AT (2)
            # (0) and (1) should point to string data
            # terms and (2) to an integer data term.
            # The characters of (0) are replaced with
            # those of (1), starting at (zero-based) offset
            # (2).  If the offset is past the end of (0),
            # (0) is padded with blanks.  If the offset
            # is negative, (0) does not change.
            # The output is the same as input (0).
            # 3 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                _, v2 = s.restore(s.h0)
                assert s.is_string_dt(v0)
                assert s.is_string_dt(v1)
                assert s.is_integer_dt(v2)
                ss = s.data(v0)
                ofs = s.data(v2)
                if ofs >= 0:
                    ss = enter_string(ss, s.data(v1), ofs)
                s.memory[v0].data = ss
                s.preserve(s.h0, pq, v0)

            case -153:
            # ENTER STRING FORM OF SYMBOL (1) INTO (0)
            # (0) should point to a string data term,
            # whose value is changed to the string form
            # of the symbol in (1).
            # (0) is returned.
            # Used to implement J156.
            # 2 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                assert s.is_string_dt(v0)
                ss = s.prettyprint(v1)
                # "A0 is entered as A" according to
                # [MAN1964], section 16.2, part 2.
                if (len(ss) == 2 and ss[0] not in '0123456789'
                                 and ss[1] == '0'):
                    ss = ss[0]
                s.memory[v0].data = ss
                s.preserve(s.h0, pq, v0)

            case -154:
            # CLEAR STRING (0)
            # (0) should point to a string data term,
            # which is made the empty string.
            #
            # The output is the same as the input.
            # 1 input and output.
                v = s.symb(s.h0)
                assert s.is_string_dt(v)
                s.memory[v].data = ''

            case -155:
            # TRIM STRING (0)
            # (0) should point to a string data term,
            # whose trailing whitespace is deleted.
            # The output is the same as input (0).
            # 1 input and output.
                v = s.symb(s.h0)
                assert s.is_string_dt(v)
                s.memory[v].data = s.data(v).rstrip()

            case -156:
            # TAKE LENGTH OF DATA TERM (0)
            # (0) is assumed to point to a string data term,
            # which is changed to be an integer data term
            # equal to the length of the original string.
            # Output (0) equals input (0).
            # 1 input and output.
                v = s.symb(s.h0)
                assert s.is_string_dt(v)
                assert s.pq(v) == 0o21
                s.memory[v].data = len(s.data(v))
                s.memory[v].pq = 0o01

            case -157:
            # TAKE SUBSTRING OF (0) STARTING AT (1) WITH LENGTH (2)
            # (0) is assumed to point to a string data term,
            # and (1) and (2) to integer data terms.
            # The value of (0) is changed to its substring which starts
            # at (0-based) offset equal to (1)
            # and has length equal to (2).
            # If the offset or length extends past the end of (0),
            # those characters are left out.
            # Output (0) equals input (0).
            # 3 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                _, v2 = s.restore(s.h0)
                assert s.is_string_dt(v0)
                assert s.is_integer_dt(v1)
                assert s.is_integer_dt(v2)
                ofs = s.data(v1)
                l = s.data(v2)
                s.memory[v0].data = s.data(v0)[ofs : ofs + l]
                s.preserve(s.h0, pq, v0)

            case -158:
            # INPUT LINE SYMBOL FROM (0)
            # Takes string data term (0)
            # and tries to interpret it as a symbol.
            # Used to implement J181.
            # 1 input; 0 outputs and - if fails, 1 output and + if succeeds.
                _, v = s.restore(s.h0)
                assert s.is_string_dt(v)
                field = s.data(v)
                if field == '':
                    s.memory[s.h5].symb = s.h_minus
                else:
                    if field[0] in Parser.regions:
                        region = field[0]
                        field = field[1 : ]
                    else:
                        region = None
                    some_digits = False
                    v = 0
                    for c in field:
                        if c in '0123456789':
                            some_digits = True
                            v = v * 10 + '0123456789'.index(c)
                    if region is not None:
                        name = region + str(v)
                        v = s.symbols.get(name, None)
                        if v is None:
                            v = s.new_cell()
                            s.symbols[name] = v
                            s.anti_symbols[v] = name
                        s.preserve(s.h0, 0, v)
                        s.memory[s.h5].symb = s.h_plus
                    elif some_digits:
                        s.preserve(s.h0, 4, v)
                        s.memory[s.h5].symb = s.h_plus
                    else:
                        s.memory[s.h5].symb = s.h_minus

            case -159:
            # INPUT INTEGER LINE DATA TERM (0) FROM (1)
            # Takes string data term (1) and tries to
            # interpret its value and place it into
            # integer data term (0).
            # Output is input (0).
            # Used to implement J182.
            # Returns - if fails, + if succeeds.
            # 2 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                assert s.is_string_dt(v1)
                assert s.is_integer_dt(v0)
                field = s.data(v1)
                some_digits = False
                sg = 0
                v = 0
                for c in field:
                    if not some_digits:
                        if c == '+':
                            sg = 1
                        if c == '-':
                            sg = -1
                    if c in '0123456789':
                        some_digits = True
                        v = v * 10 + '0123456789'.index(c)
                s.memory[v0].data = (sg if sg != 0 else 1) * v
                s.memory[s.h5].symb = s.h_plus if some_digits else s.h_minus
                s.preserve(s.h0, pq, v0)

            case -160:
            # INPUT STRING LINE DATA TERM (0)
            # Takes string data term (1), pads or
            # truncates it to five characters long,
            # and places it into string data term (0).
            # Output is input (0).
            # Used to implement J182.
            # Returns - if fails (because it's blank), + if succeeds.
            # 2 inputs, 1 output.
                pq, v0 = s.restore(s.h0)
                _, v1 = s.restore(s.h0)
                assert s.is_string_dt(v0)
                assert s.is_string_dt(v1)
                field = s.data(v1)
                if len(field) > 5:
                    field = field[-5 : ]
                elif len(field) < 5:
                    field = (field + '     ')[ : 5]
                s.memory[v0].data = field
                s.memory[s.h5].symb = s.h_plus if field != '     ' else s.h_minus
                s.preserve(s.h0, pq, v0)

            #
            # Line printing
            #

            case -161:
            # PRINT STRING (0)
            # (0) should point to a string data term,
            # which is printed (on a new line.)
            # 1 input, 0 outputs.
                _, v = s.restore(s.h0)
                assert s.is_string_dt(v)
                print(s.memory[v].data)

            #
            # Line reading
            #

            case -180:
            # READ LINE INTO STRING (0)
            # (0) should point to a string data term.
            # If there is input, its value is replaced by
            # a line read in from input and we return +.
            # If there is no input, its value does not
            # change and we return -.
            # Output (0) equals input (0).
            # 1 input and output.
                v = s.symb(s.h0)
                assert s.is_string_dt(v)
                s.memory[s.h5].symb = s.h_plus
                try:
                    s.memory[v].data = input()
                except EOFError:
                    s.memory[s.h5].symb = s.h_minus

        return Machine.M_NORMAL

    def s_of(self, q, s):
        pq = 0
        match q:
            case 0:
                pass
            case 1:
                pq = self.pq(s)
                s = self.symb(s)
            case 2:
                s = self.symb(s)
                pq = self.pq(s)
                s = self.symb(s)
            case 3:
                self.start_trace()
            case 4:
                self.continue_trace()
            case 5:
                # Machine language
                pass
            case 6:
                # Routine in fast-aux. storage, NIY
                assert False
            case 7:
                # Routine in slow-aux. storage, NIY
                assert False
        return pq, s

    # Returns false if at end
    def cycle(self):
        insn = self.memory[Machine.h1].symb
        w_insn = self.memory[insn]

        if w_insn.pq == 0o05:
            match self.machine_routine(w_insn.symb):
                case Machine.M_NORMAL:
                    return self.advance(w_insn.link)
                case Machine.M_HALT:
                    return False

        # Q
        pq, s = self.s_of(w_insn.pq & 7, w_insn.symb)

        # P
        match w_insn.pq >> 3:
            case 0:
                 self.preserve(Machine.h1, pq, s)
                 self.level += 1
                 self.memory[Machine.h3].data += 1
                 return True
            case 1:
                 self.preserve(Machine.h0, pq, s)
            case 2:
                 self.memory[s].pq = self.pq(Machine.h0)
                 self.memory[s].symb = self.symb(Machine.h0)
                 self.restore(Machine.h0)
            case 3:
                 self.restore(s)
            case 4:
                 self.preserve(s, self.pq(s), self.symb(s))
            case 5:
                 self.memory[Machine.h0].pq = pq
                 self.memory[Machine.h0].symb = s
            case 6:
                 self.memory[s].pq = self.pq(Machine.h0)
                 self.memory[s].symb = self.symb(Machine.h0)
            case 7:
                 if self.memory[self.h5].symb == Machine.h_minus:
                     return self.advance(s)

        return self.advance(w_insn.link)
