#!/usr/bin/env python3
"""Run the rod solver on single options "cut cell c at height z" of a position.

usage: option_runs.py RODF COLS POSITION ASSUMED TIMEOUT JOBS MEM_MB cell:z,z,z cell:z,...

  COLS      base by column heights, for example 322 or 333
  POSITION  heights of the cells of COLS, column by column, w = omega
  ASSUMED   file of assumed P-positions (rodf -A), or "-" for none
  TIMEOUT   seconds per option
  JOBS      options run in parallel
  MEM_MB    an option is stopped when its resident memory exceeds this (no address-space
            limit: the solver reserves a 2 GB stack and a 1 GB pool that it mostly does not use)
  cell:z,.. cells as x.y, cut heights as a list or ranges a-b

Only the verdicts "N exact" and "P exact" (and "N via assumed P") are reliable; see notes/24 §7.
"""
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

rodf, cols, pos, assumed, timeout, jobs, mem_mb = sys.argv[1:8]
timeout = float(timeout)
jobs = int(jobs)
mem_mb = int(mem_mb)
cells = [(x, y) for x, c in enumerate(cols) for y in range(int(c))]
h = pos.split(",")
cases = []
for spec in sys.argv[8:]:
    c, zs = spec.split(":")
    cx, cy = map(int, c.split("."))
    for z in zs.split(","):
        if "-" in z:
            lo, hi = map(int, z.split("-"))
            cases += [(cx, cy, t) for t in range(lo, hi + 1)]
        else:
            cases.append((cx, cy, int(z)))


def rss_mb(pid):
    try:
        with open("/proc/%d/statm" % pid) as f:
            return int(f.read().split()[1]) * 4096 // (1 << 20)
    except OSError:
        return 0


def run(case):
    cx, cy, z = case
    g = []
    for (x, y), v in zip(cells, h):
        if x >= cx and y >= cy and (v == "w" or int(v) > z):
            v = str(z)
        g.append(v)
    cmd = [rodf] + (["-A", assumed] if assumed != "-" else []) + ["-a", "2", "-d", "10", "-p", ",".join(g), cols]
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    t0 = time.time()
    verdict = None
    while p.poll() is None:
        time.sleep(0.5)
        if time.time() - t0 > timeout:
            p.kill()
            verdict = "timeout"
        elif rss_mb(p.pid) > mem_mb:
            p.kill()
            verdict = "memory limit"
    out, err = p.communicate()
    if verdict is None:
        res = [l for l in out.splitlines() if " : " in l]
        if res:
            verdict = res[-1].split(" : ", 1)[1]
        else:
            verdict = "crash: " + (err.strip().splitlines()[-1][:60] if err.strip() else "no verdict")
    return case, ",".join(g), verdict, time.time() - t0


with ThreadPoolExecutor(jobs) as ex:
    for (cx, cy, z), g, v, dt in ex.map(run, cases):
        print("cut (%d,%d) at %d = %s : %s   [%.0f s]" % (cx, cy, z, g, v, dt), flush=True)
