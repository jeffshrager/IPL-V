# Python 3.

# David Moews, July 2026.  Released into the public domain, CC0.

#
# Take a file of propositional logic expressions, each line of the form
#
#   <name> <expression> [<possible-suffix>] [<extra ignored field>...]
#
# and reformat it into IPL code suitable for running with the
# 1963 Stefferud version of the Logic Theorist program;
# also, print a suitable executive program to process these
# expressions.
#
# This output code should be appended to the patched version of the
# original (1963) Logic Theorist code from Stefferud's RAND
# memorandum, THE LOGIC THEORY MACHINE: A MODEL HEURISTIC PROGRAM.
#

# The input file has two sections, the first being axioms
# and the second problems.  They should be separated by a blank line.

import sys

exprs = {}

def add_expression(j, l):
    global exprs
    assert len(l) in [2, 3]
    if len(l) == 2:
        l += [None]
    exprs[j] = l

def print_expression(j):
    name, symbs, suffix = exprs[j]
    print(' ' * 42 + 'X' + str(j) + ' ' * (8 - (1 + len(str(j)))) + '9-1')
    for i in range(len(symbs)):
        c = symbs[i]
        print(' ' * 50 + c + '0', end = '')
        if i < len(symbs) - 1:
            print()
        else:
            print('    0')
    print(' ' * 42 + '9-1     0')
    print(' ' * 50 + 'Q7')
    if suffix is not None:
        print(' ' * 50 + '9-2')
        print(' ' * 50 + 'Q18')
        print(' ' * 50 + '9-3   0')
    else:
        print(' ' * 50 + '9-2   0')
    print(' ' * 42 +     '9-2   21' + name)
    if suffix is not None:
        print(' ' * 42 +     '9-3   21' + suffix)

in_axioms = True
in_problems = False

axioms = []
problems = []

j = 2

for l in sys.stdin.readlines():
    l = l.split()[ : 3]

    if l == []:
        if in_axioms:
            in_problems = True
            continue

    if in_problems:
        problems.append(j)
        add_expression(j, l)
        j += 1
    elif in_axioms:
        axioms.append(j)
        add_expression(j, l)
        j += 1

local_label_index = 100

print('''      EXECUTIVE HEADER                  5
                                          Z1    40H0
                                                  M88
                                                40H0
                                                  J15
                                                  J75   J72
                                          X1      J0''')


for j in axioms:
    print('''                                                10X#
                                                40H0
                                                  P50
                                                709-%
                                                  M50   9-@
                                          9-%   Z1
                                          9-@   J0'''.translate({ord('#'): str(j),
               ord('@'): str(local_label_index),
               ord('%'): str(local_label_index + 1) }))
    local_label_index += 2

print('''                                                  J154
                                                  J155
                                                  J155''')

for j in problems:
    print('''                                                10X#
                                                40H0
                                                  P50
                                                709-%
                                                40H0
                                                  M70
                                                10L3
                                                  J6
                                                  J65   9-@
                                          9-%   Z1
                                          9-@   J0'''.translate({ord('#'): str(j),
               ord('@'): str(local_label_index),
               ord('%'): str(local_label_index + 1) }))
    local_label_index += 2

print('''                                                  M2    0
     RUN DATA HEADER                    5       01''')


for j in axioms:
    print_expression(j)
for j in problems:
    print_expression(j)

print('     KICK OFF FOR PROVING THEOREMS      5         X1')
