#!/usr/bin/env python

import sys
import pymake.engine

filename = sys.argv[1]
source = None

with open(filename, 'rU') as fh:
    source = fh.read()

statements = pymake.engine.parsestring(source, filename)
print(statements.to_source())
