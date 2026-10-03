#!/bin/sh
python3 test.py 'python3 iplv.py' iplv.test iplv.usage
python3 test.py 'python3 remove_ws.py' remove_ws.test
python3 test.py 'python3 iplparser.py' iplparser.test
