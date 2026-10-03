#!/bin/sh
cp -i ../logic-theorist-1963-stefferud.iplv patched-logic-theorist.iplv
patch <logic-theorist-patch.txt
python3 logictoiplv.py <../logic-theorist-1963-stefferud-input.txt >>patched-logic-theorist.iplv
