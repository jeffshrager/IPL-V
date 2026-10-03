# Python 3

from __future__ import annotations

import sys

import util
from util import complain, WARNING, ERROR
import dataclasses

# IPL-V parser.

# David Moews, July 2026.  Released into the public domain, CC0.

# Fields of an IPL-V line

@dataclasses.dataclass
class Line:
    filename: str
    line_no: int
    left_comment: str
    is_this_data: bool
    tp: str            # ' ' if absent
    name: str          # '' if omitted, otherwise regularized
    sg: str            # ' ', + or -
    p: int             # -1 (omitted) to 7
    q: int             # -1 (omitted) to 7
    symb: str          # '' if omitted or for data terms, otherwise regularized
    link: str          # '' if omitted or for data terms, otherwise regularized
    data: int | float | str | types.EllipsisType | None
                       # Only for data terms, None otherwise
                       # ... is used for data terms with unknown type
    right_comment: str

    def astuple(self):
        return dataclasses.astuple(self)

    def copy(self):
        return Line(self.filename, self.line_no, self.left_comment,
                    self.is_this_data,
                    self.tp, self.name, self.sg, self.p, self.q,
                    self.symb, self.link, self.data,
                    self.right_comment)

    def print(self):
        if self.tp == '1':
            return '%-40s1%-s' % (self.left_comment, self.right_comment)

        if self.data is None:
            printed_data = '%-5s %-5s' % (self.symb, self.link)
        else:
            assert self.symb == '' and self.link == ''
            if type(self.data) == type(''):
                assert len(self.data) == 5
                printed_data = self.data + '      '
            elif type(self.data) == type(0):
                printed_data = '%8d' % abs(self.data)
                printed_data = (' ' + printed_data[ : 4] +
                                      '  ' + printed_data[4 : ])
            else:
                print(
          '**Error: Only integer and string data terms have been implemented.',
                      file = sys.stderr)
                printed_data = ''
        v = ('%-40s%1s %-5s%1s%1s%1s%11s%-s' %
             (self.left_comment, self.tp, self.name,
              self.sg,
              ' ' if self.p == -1 else str(self.p),
              ' ' if self.q == -1 else str(self.q),
              printed_data, self.right_comment))
        return v.rstrip()

class Parser:

    regions: str = "ABCDEFGHIJKLMNOPQRSTUVWXYZ()+-/=.,$*@'"

    #
    # Returns empty string for blank;
    # string starting with '9-' for local symbols;
    # string starting with an allowed character
    # (A-Z or ()+-/=.,$*@') for regional symbols;
    # numeric-only string for internal symbols;
    # None if it can't be parsed
    #
    # (see [MAN1964], part 2, sections 1.3, 1.6, 18.2.)
    #
    # We allow ' for regional symbols since the Logic Theorist
    # program uses it.
    #
    # As an extension we allow regional symbols starting with @
    # (these are used to address the lower-level routines)
    #
    def regularize(name):
        # Blanks usually refer to the next line
        # but will be 0 if the next line has a regional or internal
        # symbol as name ([MAN1964], part 2, section 1.6)
        if name.strip() == '':
            return ''
        first = name[ : 1]
        st = 0 if first in ' 012345678' else 1
        v = 0
        for c in name[st : ]:
            if c in '0123456789':
                v = v * 10 + '0123456789'.index(c)
        if st == 0:
            return str(v)         # Internal
        if first == '9':
            return '9-' + str(v)  # Local
        if first not in Parser.regions:
            return None           # Syntax error
        return first + str(v) # Regional

    #
    # Local names may end up prefixed by section names,
    # so we check for - after the first character of
    # a regional or internal name to avoid local names.
    #
    def is_regional(name):
        return (name != '' and name[0] in Parser.regions
                           and '-' not in name[1 : ])

    def is_internal(name):
        return (name != '' and name[0] in '0123456789'
                           and '-' not in name)

    def is_local(name):
        return name == '' or '-' in name[1 : ]

    def name_ok(name):
        return (Parser.is_regional(name) +
                Parser.is_internal(name) +
                Parser.is_local(name) == 1)

    # Returns -2 on error, -1 on absent
    def get_p_or_q(p_or_q):
        return ' 01234567'.find(p_or_q) - 1

#
# Note: Signed lines (with sign + or -) in program text should be
#       interpreted as data ([MAN1964], part 2, section 3.5, p. 156)
#

    # Takes list of unparsed lines to list of parsed lines
    # name, symb and link in parsed lines are regularized
    def parser(lines):

        rv = []
        is_data = False

        for filename, line_no, l in (t.astuple() for t in lines):
            left_comment = l[ : 40].rstrip()
            l = l[40 : ]

            if len(l) < 21:
                l += ' ' * (21 - len(l))

            tp = l[: 1]

            if tp == '1':
                rv.append(Line(filename, line_no, left_comment, False,
                               '1', '', ' ', -1, -1, '', '', None,
                               l[1 : ].rstrip()))
                continue

            name = Parser.regularize(l[2 : 7])
            if name is None:
                complain(ERROR, filename, line_no, 'Bad name')
                name = ''

            sg = l[7 : 8]
            if sg not in ' +-':
                sg = ' '
                complain(ERROR, filename, line_no, 'Bad sign')

            p = Parser.get_p_or_q(l[8 : 9])
            if p == -2:
                complain(ERROR, filename, line_no, 'Bad p')
                p = -1

            q = Parser.get_p_or_q(l[9 : 10])
            if q == -2:
                complain(ERROR, filename, line_no, 'Bad q')
                q = -1

            symb = l[10 : 15]
            link = l[16 : 21]

            right_comment = l[21 : ].rstrip()

            if tp == '5':
                is_data = q in [1, 3, 5]
                is_this_data = is_data_term = False
            elif tp in [' ', '0']:
                is_this_data = is_data or sg in '+-'
                is_data_term = is_this_data and q == 1
            else:
                is_data = is_this_data = is_data_term = False

            if not is_data_term:
                symb = Parser.regularize(symb)
                if symb is None:
                    complain(ERROR, filename, line_no, 'Bad symbol')
                    symb = ''
                assert Parser.name_ok(symb)
                link = Parser.regularize(link)
                if link is None:
                    complain(ERROR, filename, line_no, 'Bad link')
                    link = ''
                assert Parser.name_ok(link)
                data = None
            else:
                use_p = p if p != -1 else 0
                match use_p:

                    case 0:
                        # Format: (see [MAN1964], part 2, section 1.7,
                        #          Figure 2, p. 140)
                        #
                        # sign, 4 digits in SYMB, 4 digits in LINK
                        #
                        n1 = symb.strip()
                        n2 = link.strip()
                        if (len(n1) > 4 or len(n2) > 4 or
                            not all(c in '0123456789' for c in n1 + n2)):
                            data = 0
                            complain(ERROR, filename, line_no,
                                     'Bad integer data term')
                        else:
                            data = ((-1 if sg == '-' else 1) *
                                    (int('0' + n1) * 10000 + int('0' + n2)))

                    case 2:
                        # Format: (see [MAN1964], part 2, section 1.7,
                        #          Figure 2, p. 140)
                        #
                        # five characters of SYMB
                        data = (symb + '     ')[ : 5]
                    case _:
                        complain(ERROR, filename, line_no,
                                 'Unknown data term type %1o1' % use_p)
                        data = ...
                symb = link = ''

            assert Parser.name_ok(name)

            rv.append(Line(filename, line_no, left_comment,
                           is_this_data,
                           tp, name, sg, p, q, symb, link, data,
                           right_comment))

        return rv

def main():
    lines = util.get_unparsed_lines(None)
    lines = util.remove_extensions(lines)
    lines = Parser.parser(lines)
    for l in lines:
        print(l.print())

if __name__ == '__main__':
    main()
