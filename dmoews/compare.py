"""Compare per-theorem results of the Lisp run with Stefferud's 1963 output."""
import re, sys
def parse(path):
    rows, cur = [], None
    lines = [l.lstrip(':').rstrip() for l in open(path, errors='replace')]
    for i, l in enumerate(lines):
        if l.strip() == 'TO PROVE':
            m = re.match(r'\s*\*?(\d\.\d+)', lines[i+1])
            cur = {'thm': m.group(1)}; rows.append(cur)
        elif cur is not None:
            s = l.strip()
            if s.startswith('PROOF FOUND'): cur['res'] = 'proved'
            elif s.startswith('NO PROOF'): cur['res'] = 'NO PROOF'
            for k in ('EFFORT', 'SUBPROBLEMS', 'SUBSTITUTIONS'):
                m = re.match(k + r'\s+LIMIT\s+\d+\s+ACTUAL\s+(\d+)', s)
                if m: cur[k] = int(m.group(1))
    return rows
a = parse(sys.argv[1]); b = parse(sys.argv[2])
print(f"{'thm':6}{'1963':>10}{'lisp':>10}  {'subp':>9}  {'subst':>9}  {'effort 1963/lisp':>18}")
for x, y in zip(a, b):
    flag = '' if (x.get('res'), x.get('SUBPROBLEMS'), x.get('SUBSTITUTIONS')) == (y.get('res'), y.get('SUBPROBLEMS'), y.get('SUBSTITUTIONS')) else '  <-- differs'
    print(f"{x['thm']:6}{x.get('res','?'):>10}{y.get('res','?'):>10}  {x.get('SUBPROBLEMS')!s:>4}/{y.get('SUBPROBLEMS')!s:<4}  {x.get('SUBSTITUTIONS')!s:>4}/{y.get('SUBSTITUTIONS')!s:<4}  {x.get('EFFORT')!s:>8}/{y.get('EFFORT')!s:<8}{flag}")
print(len(a), len(b))
