# Python 3

# Miscellaneous utility functions and classes.

# David Moews, July 2026.  Released into the public domain, CC0.

import sys

import dataclasses

WARNING = 1
ERROR = 2

def complain(severity, fn, line_no, msg):
    msg = ('**Error: ' if severity >= ERROR else '**Warning: ') + msg
    if line_no >= 0:
        msg += ', line %d' % line_no
    if fn is not None and fn != '':
        msg += ', file %s' % fn
    print(msg + '.', file = sys.stderr)

@dataclasses.dataclass
class UnparsedLine:
    filename: str
    line_no: int
    line: str

    def astuple(self):
        return dataclasses.astuple(self)

def trim_newline(l):
    if l[-1 : ] == '\n':
        return l[ : -1]
    else:
        return l

# If fn is None, use the standard input.
def get_unparsed_lines(fn):
    f = None
    lines = []
    if fn is None:
        f = sys.stdin
        print_fn = 'stdin'
    else:
        print_fn = fn
        try:
            f = open(fn, 'r')
        except:
            complain(ERROR, None, -1, "Cannot open '%s'" % fn)
    if f is not None:
        lines = [UnparsedLine(fn, i + 1, trim_newline(l))
                     for i, l in enumerate(f.readlines())]
        f.close()
    return lines

def remove_extension(l):
    if l[ : 1] == '#':
        l = l[1 : ]
        split = l[: 40].rfind(' ')
        if len(l) > 40 and split >= 0:
            l_left = l[ : split]
            l_right = l[split + 1 : ]
        else:
            l_left = l[ : 40]
            l_right = l[40 : ]
        return '%-40s1 %-s' % (l_left, l_right)
    elif l[ : 1] == '%':
        return ' ' * 42 + l[1 : ]
    else:
        return l

def remove_extensions(unparsed_lines):
    return [UnparsedLine(t.filename, t.line_no, remove_extension(t.line))
                for t in unparsed_lines]
