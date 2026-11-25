#!/usr/bin/env python3
"""Exact chains "cut cell c at z = 0, 1, 2, ..." for a list of positions, with the rod solver.

usage: chain_runs.py RODF CELL ZMAX TIMEOUT JOBS MEM_MB < positions

  positions  one per line: nine entries in the order (0,0),(0,1),(0,2) | (1,0),... ; w = omega
  CELL       the infinite column that is cut, as x,y; the position after the cut must have two
             infinite columns, so that the solver is exact
  ZMAX       last cut height tried

For each position the solver runs "rodf -K" (one process, shared memory) and stops at the first
P member. Output, one line per position: the first P member, or the height up to which every
member is N, and why the run stopped (done, timeout, memory).
"""
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

rodf, cell, zmax, timeout, jobs, mem_mb = sys.argv[1:7]
cx, cy = map(int, cell.split(","))
zmax, timeout, jobs, mem_mb = int(zmax), float(timeout), int(jobs), int(mem_mb)


def rss_mb(pid):
    try:
        for line in open("/proc/%d/status" % pid):
            if line.startswith("RssAnon"):
                return int(line.split()[1]) // 1024
    except OSError:
        pass
    return 0


def run(line):
    pos = line.replace("|", " ").split()
    cols = [sum(1 for y in range(3) if pos[3 * x + y] != "0") for x in range(3)]
    cols = [c for c in cols if c > 0]
    cells = [(x, y) for x in range(len(cols)) for y in range(cols[x])]
    hs = ",".join(pos[3 * x + y] for (x, y) in cells)
    idx = cells.index((cx, cy))
    cmd = [rodf, "-a", "2", "-d", "12", "-L", "60000000", "-K", str(idx), "-Z", str(zmax), "-v", "1",
           "-p", hs, "".join(map(str, cols))]
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    t0 = time.time()
    why = "done"
    while p.poll() is None:
        time.sleep(0.5)
        if time.time() - t0 > timeout:
            p.kill()
            why = "timeout"
        elif rss_mb(p.pid) > mem_mb:
            p.kill()
            why = "memory"
    out = p.communicate()[0]
    lastN, firstP, inexact = -1, None, []
    for l in out.splitlines():
        t = l.split()
        if len(t) >= 5 and t[0] == "cut" and t[2] == "at":
            z = int(t[3].rstrip(":"))
            v = t[4]
            if v.endswith("?"):
                inexact.append(z)
            elif v == "P":
                firstP = z
            elif v == "N" and firstP is None:
                lastN = z
    res = ("first P member at %d" % firstP) if firstP is not None else ("N up to %d" % lastN)
    if inexact:
        res += "; not exact at %s" % inexact
    return "%s : %s (%s, %.0f s)" % (line.strip(), res, why, time.time() - t0)


lines = [l for l in sys.stdin if l.strip() and not l.startswith("#")]
with ThreadPoolExecutor(jobs) as ex:
    for r in ex.map(run, lines):
        print(r, flush=True)
