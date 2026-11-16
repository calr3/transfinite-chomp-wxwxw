#!/usr/bin/env python3
"""Exact P/N of the finite truncations U(M1,M2,M3) = U ∩ [0,M1)×[0,M2)×[0,M3) of the three-plane
position U = N^3 minus up(1,1,1). Each plane is a finite rectangle; the position is finite, so
chomp3f's answer is exact. Lists the P truncations with M1 <= M2 <= M3 <= MAX.

usage: utrunc.py CHOMP3F MAX [TIMEOUT]
"""
import subprocess
import sys


def main():
    binary, mx = sys.argv[1], int(sys.argv[2])
    timeout = float(sys.argv[3]) if len(sys.argv) > 3 else 600
    for s in range(3, 3 * mx + 1):
        for m1 in range(1, mx + 1):
            for m2 in range(m1, mx + 1):
                m3 = s - m1 - m2
                if m3 < m2 or m3 > mx:
                    continue
                gens = "%d,0,0 0,%d,0 0,0,%d 1,1,1" % (m1, m2, m3)
                try:
                    out = subprocess.run([binary, "solve", gens], capture_output=True, text=True,
                                         timeout=timeout).stdout
                    res = out.split(":")[1].split()[0] + ("" if "exact" in out else "?")
                except subprocess.TimeoutExpired:
                    res = "timeout"
                print("U(%d,%d,%d)  %s" % (m1, m2, m3, res), flush=True)


main()
