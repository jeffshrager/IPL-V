# Python 3

# test.py: Test a program.

# CC0, released into the public domain.

# David Moews, 2019, 2025, 2026.

import subprocess
import sys

class TestFileError(Exception):
    pass

def is_ok(v):
    return 'OK' if v else 'not OK'

def split_space(x):
    return [] if x == b'' else x.split(b' ')

command_name = sys.argv[1].split(' ')

test_failed = False

if len(sys.argv) >= 4:
    usage_file = open(sys.argv[3], 'rb')
    usage = command_name[0].encode('utf-8').join(usage_file.read().split(b'@'))
    usage_file.close()
else:
    usage = ''

test_file = open(sys.argv[2], 'rb')
testfile = test_file.read()
test_file.close()

while testfile != b'':
    i = testfile.index(b'\n')
    line = testfile[:i]
    testfile = testfile[i+1:]
    if line == b'' or line[0] == 35:
        pass
    elif line[:2] == b'IN':
        arglist = [arg.decode('utf-8') for arg in split_space(line[3:])]
        desired_output_list = []
        desired_errout_list = []
        stdin_list = []
        desired_retcode = 0
        the_stdout = subprocess.PIPE
        while  (testfile[:3] == b'RTC' or testfile[:3] == b'OUT'
             or testfile[:3] == b'ERR' or testfile[:3] == b'FIN'
             or testfile[:1] == b'#'   or testfile[:3] == b'NLO'):
            i = testfile.index(b'\n')
            if testfile[:1] == b'#':
                testfile = testfile[i+1:]
                continue
            piece = testfile[4:i]
            if piece == b'$USAGE':
                piece = usage
            if testfile[:3] == b'OUT':
                desired_output_list.append(piece)
            elif testfile[:3] == b'FIN':
                stdin_list.append(piece)
            elif testfile[:3] == b'ERR':
                desired_errout_list.append(piece)
            elif testfile[:3] == b'RTC':
                desired_retcode = int(piece)
            elif testfile[:3] == b'NLO':
                the_stdout = subprocess.DEVNULL
            testfile = testfile[i+1:]
        cmdline = command_name + arglist
        p = subprocess.Popen(cmdline, stdin=subprocess.PIPE,
                                              stdout=the_stdout,
                                              stderr=subprocess.PIPE)
        (output, errout) = p.communicate(input=b'\n'.join(stdin_list))
        if output is None:
            output = b''
        desired_output = b'\n'.join(desired_output_list)
        desired_errout = b'\n'.join(desired_errout_list)
        if p.returncode != desired_retcode:
            print('Command ' + ' '.join(cmdline)
                             + ' retcode ' + str(p.returncode)
                             + ', desired is ' + str(desired_retcode))
            test_failed = True
        if output != desired_output or errout != desired_errout:
            print('Command ' + ' '.join(cmdline)
                             + ' output ' + is_ok(output == desired_output)
                             + ' error ' + is_ok(errout == desired_errout))
            if output != desired_output:
                print('Output:')
                print()
                sys.stdout.flush()
                sys.stdout.buffer.write(output)
                sys.stdout.flush()
                print()
                print('Desired output:')
                print()
                sys.stdout.flush()
                sys.stdout.buffer.write(desired_output)
                sys.stdout.flush()
                print()
            if errout != desired_errout:
                print('Error output:')
                print()
                sys.stdout.flush()
                sys.stdout.buffer.write(errout)
                sys.stdout.flush()
                print()
                print('Desired error output:')
                print()
                sys.stdout.flush()
                sys.stdout.buffer.write(desired_errout)
                sys.stdout.flush()
                print()
            test_failed = True
    else:
        print('Error in test file')
        raise TestFileError()

if not test_failed:
    print('All tests OK')
