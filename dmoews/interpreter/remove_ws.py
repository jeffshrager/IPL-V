# Python 3

#
# Remove use of Ws and J20 to J59
# from an IPL-V file, to the extent possible.
#
# David Moews, July 2026.  Released into the public domain, CC0.
#

from iplparser import Line, Parser
import util

def process_chunk(output_lines, chunk):
    locals = set()
    w_map = {}

    def new_local_name():
        n = 0
        while '9-' + str(n) in locals:
            n += 1
        nm = '9-' + str(n)
        locals.add(nm)
        return nm

    def get_w_label(w_num):
        if w_num not in w_map:
            w_map[w_num] = new_local_name()
        return w_map[w_num]

    def process_j(j_num):
        j_type = j_num // 10
        max_w_num = j_num % 10
        w_labels = [get_w_label(i) for i in range(max_w_num + 1)]
        match j_type:
            case 2:
                return [(2, 0, w_labels[i]) for i in range(max_w_num + 1)]
            case 3:
                return [(3, 0, w_labels[i]) for i in range(max_w_num + 1)]
            case 4:
                return [(4, 0, w_labels[i]) for i in range(max_w_num + 1)]
            case 5:
                return [(4, 0, w_labels[i]) for i in range(max_w_num + 1)] + \
                       [(2, 0, w_labels[i]) for i in range(max_w_num + 1)]

    # Collect locals, find last non-comment line

    max_non_comment_idx = None

    for i, l in enumerate(chunk):
        if l.tp != '1':
            max_non_comment_idx = i
        for symb in [l.name, l.symb, l.link]:
            if Parser.is_local(symb):
                locals.add(symb)

    chunk_postlude = []

    for i, l_orig in enumerate(chunk):

        filename, line_no, left_comment, is_this_data, \
        tp, name, sg, p, q, symb, link, data, right_comment = l_orig.astuple()

        if l_orig.data is not None:
            output_lines.append(l_orig)
            continue

        l = l_orig.copy()

        if symb == '' and i == max_non_comment_idx:
            l.symb = symb = '0'

        if link == '' and i == max_non_comment_idx:
            l.link = link = '0'

        if is_this_data:
            output_lines.append(l)
            continue

        if symb[ : 1] == 'W' and 0 <= int(symb[1 :] ) <= 9:
            l.symb = symb = get_w_label(int(symb[1 : ]))

        if l.link[ : 1] == 'W' and 0 <= int(link[1 :] ) <= 9:
            l.link = link = get_w_label(int(link[1 : ]))

        if link[ : 1] == 'J' and 20 <= int(link[1 : ]) <= 59:
            new_stmts = process_j(int(link[1 : ]))
            l.link = link = new_label = new_local_name()
            ln = len(new_stmts)
            chunk_postlude.extend(
               Line(filename, line_no, '', False,
                    ' ', new_label if i == 0 else '',
                    ' ', new_stmts[i][0], new_stmts[i][1], new_stmts[i][2],
                    '0' if i == ln - 1 else '', None, '') for i in range(ln))

        if symb[ : 1] == 'J' and 20 <= int(symb[1 : ]) <= 59 \
                             and q in [0, -1] and p in [-1, 0, 7]:
            j_num = int(symb[1 : ])
            if p == 7:
                l.symb = symb = new_label = new_local_name()
                output_lines.append(l)
                new_stmts = process_j(j_num)
                ln = len(new_stmts)
                chunk_postlude.extend(
                    Line(filename, line_no, '', False,
                         ' ', new_label if i == 0 else '',
                         ' ', new_stmts[i][0], new_stmts[i][1], new_stmts[i][2],
                         '0' if i == ln - 1 else '', None, '') for i in range(ln))
            else:
                new_stmts = process_j(j_num)
                ln = len(new_stmts)
                output_lines.extend(
                    Line(filename, line_no, left_comment if i == 0 else '',
                         False,
                         ' ', name if i == 0 else '',
                         ' ', new_stmts[i][0], new_stmts[i][1], new_stmts[i][2],
                         link if i == ln - 1 else '', None,
                         right_comment if i == ln - 1 else '') for i in range(ln))
        else:
            output_lines.append(l)

    output_lines.extend(chunk_postlude)

    for loc in w_map.values():
        output_lines.append(Line(filename, line_no, '', False,
                                 ' ', loc,
                                 ' ', -1, -1, '0', '0', None, ''))

def remove_ws(lines):

    output_lines = []
    chunk = []

    for l in lines:

        if l.tp == '1':
            chunk.append(l)
            continue

        if l.tp not in ' 0':
            if chunk != []:
                process_chunk(output_lines, chunk)
            chunk = []
            output_lines.append(l)
        else:
            if not Parser.is_local(l.name):
                if chunk != []:
                    process_chunk(output_lines, chunk)
                chunk = []

            chunk.append(l)

    if chunk != []:
        process_chunk(output_lines, chunk)

    return output_lines

def main():
    lines = util.get_unparsed_lines(None)
    lines = util.remove_extensions(lines)
    lines = Parser.parser(lines)
    lines = remove_ws(lines)
    for l in lines:
        print(l.print())

if __name__ == '__main__':
    main()
