#!/usr/bin/env python3
"""Turn "N in the census" into "N exact" where the solver can certify the reply.

usage: verify_census_options.py RODF CENSUS_OUTPUT TIMEOUT JOBS [MEM_MB]

Reads the report lines of "base3_table ... -T Z" for the positions with every free cell
infinite. For each position that is N in the census without a P cut of the poison column, the
options labelled P are tried in order of height: the position left by the option is given to
the rod solver. If the solver answers "P exact" the top position is N, exactly, by that reply.
If it answers "N exact" by a lower cut of the same column, that lower cut is tried instead.
If no proposed option works, the solver is run on the position itself.
(The solver is exact for positions with two infinite columns; for others it says "heuristic"
and the option does not count.)

Output: one line per position: "N exact, reply (x,y)@z", or "not certified" with the verdicts.
"""
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

rodf, census, timeout, jobs = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4])
mem_mb = int(sys.argv[5]) if len(sys.argv) > 5 else 3000
CELLS = [(x, y) for x in range(3) for y in range(3)]


def rss_mb(pid):
    try:
        with open("/proc/%d/statm" % pid) as f:
            return int(f.read().split()[1]) * 4096 // (1 << 20)
    except OSError:
        return 0


def solve(pos):
    """pos: nine entries ('w' or int), x-major. Returns the solver's verdict string."""
    cols = [sum(1 for y in range(3) if pos[3 * x + y] != 0) for x in range(3)]
    cols = [c for c in cols if c > 0]
    hs = ",".join(str(pos[3 * x + y]) for x in range(len(cols)) for y in range(cols[x]))
    # -L: step limit of one period certificate; the default 3e6 is too low for deep replies
    p = subprocess.Popen([rodf, "-a", "3", "-d", "12", "-L", "60000000", "-p", hs, "".join(map(str, cols))],
                         stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    t0 = time.time()
    while p.poll() is None:
        time.sleep(0.2)
        if time.time() - t0 > timeout:
            p.kill()
            p.communicate()
            return "timeout"
        if rss_mb(p.pid) > mem_mb:
            p.kill()
            p.communicate()
            return "memory limit"
    out = p.communicate()[0]
    res = [l for l in out.splitlines() if " : " in l]
    return res[-1].split(" : ", 1)[1].strip() if res else "no verdict"


def cut(pos, cx, cy, z):
    out = []
    for (x, y), v in zip(CELLS, pos):
        if x >= cx and y >= cy and (v == "w" or v > z):
            v = z
        out.append(v)
    return out


tasks = []
for line in open(census):
    if not line.startswith(" w") or "N in the census" not in line or "no P cut" not in line:
        continue
    head = line.split("  :")[0]
    pos = [t if t == "w" else int(t) for t in head.replace("|", " ").split()]
    opts = [(int(z), int(x), int(y)) for x, y, z in re.findall(r"option labelled P: \((\d),(\d)\)@(\d+)", line)]
    tasks.append((head.strip(), pos, sorted(opts)))


def run(task):
    head, pos, opts = task
    tried = []
    for z, x, y in opts:
        v = solve(cut(pos, x, y, z))
        if v.startswith("P exact"):
            return "%s : N exact, reply (%d,%d)@%d" % (head, x, y, z)
        # The census can have the height wrong (a finite cut above H). If the solver beats the
        # proposed position by a lower cut of the same column, that lower cut is the reply.
        m = re.match(r"N exact\s+move: cell \((\d),(\d)\) at height (\d+)", v)
        if m and (int(m.group(1)), int(m.group(2))) == (x, y):
            t = int(m.group(3))
            if solve(cut(pos, x, y, t)).startswith("P exact"):
                return "%s : N exact, reply (%d,%d)@%d (census: @%d)" % (head, x, y, t, z)
        tried.append("(%d,%d)@%d %s" % (x, y, z, v.split("   ")[0]))
    # Last resort: the solver on the position itself. "N exact" means it found an exact P option.
    v = solve(pos)
    m = re.match(r"N exact\s+move: cell \((\d),(\d)\) at height (\d+)", v)
    if m:
        return "%s : N exact, reply (%s,%s)@%s (solver's own; census: %s)" % (
            head, m.group(1), m.group(2), m.group(3), "; ".join(tried))
    return "%s : not certified [%s]" % (head, "; ".join(tried))


with ThreadPoolExecutor(jobs) as ex:
    n = ok = 0
    for res in ex.map(run, tasks):
        n += 1
        ok += ": N exact" in res
        print(res, flush=True)
    print("# %d positions, %d certified N" % (n, ok))
