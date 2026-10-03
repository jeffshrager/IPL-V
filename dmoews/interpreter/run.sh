#!/bin/sh
python3 iplv.py --extra-syntax lib-ws.iplv --remove-ws lib-simon.iplv lib-misc.iplv --no-remove-ws lib-j100.iplv lib-shuffle-ws.iplv lib-hs.iplv lib-generators-new.iplv lib-at.iplv --no-extra-syntax $1
