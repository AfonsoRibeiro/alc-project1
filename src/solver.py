#!/usr/bin/env python3

import sys
import time
from problem import Problem

if __name__ == '__main__':
    p = Problem(sys.stdin, 'rc2')
    begin = time.perf_counter()
    p.encode()
    p.solve()
    #print('{} s'.format(time.perf_counter() - begin), file=sys.stderr)
