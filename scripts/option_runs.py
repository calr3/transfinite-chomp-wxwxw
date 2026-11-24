#!/usr/bin/env python3
"""Run the rod solver on single options "cut cell c at z" of a position.
usage: optrun.py RODF COLS POSITION ASSUMED TIMEOUT JOBS MEMKB cell:z,z,z cell:z,...   (cells as x.y)
POSITION: heights of the cells of COLS, column by column, w = omega."""
import subprocess, sys, resource
from concurrent.futures import ThreadPoolExecutor
rodf, cols, pos, assumed, timeout, jobs, memkb = sys.argv[1:8]
timeout=float(timeout); jobs=int(jobs); memkb=int(memkb)
cells=[(x,y) for x,c in enumerate(cols) for y in range(int(c))]
h=pos.split(",")
cases=[]
for spec in sys.argv[8:]:
    c,zs=spec.split(":"); cx,cy=map(int,c.split("."))
    for z in zs.split(","): cases.append((cx,cy,int(z)))
def lim():
    resource.setrlimit(resource.RLIMIT_AS,(memkb*1024,memkb*1024))
def run(case):
    cx,cy,z=case
    g=[]
    for (x,y),v in zip(cells,h):
        if x>=cx and y>=cy and (v=="w" or int(v)>z): v=str(z)
        g.append(v)
    try:
        out=subprocess.run([rodf,"-A",assumed,"-a","2","-d","10","-p",",".join(g),cols],capture_output=True,text=True,timeout=timeout,preexec_fn=lim)
        res=[l for l in out.stdout.splitlines() if " : " in l]
        v=res[-1].split(" : ",1)[1] if res else ("crash: "+out.stderr.strip().splitlines()[-1][:60] if out.stderr.strip() else "no verdict")
    except subprocess.TimeoutExpired:
        v="timeout"
    return case,",".join(g),v
with ThreadPoolExecutor(jobs) as ex:
    for (cx,cy,z),g,v in ex.map(run,cases):
        print("cut (%d,%d) at %d = %s : %s"%(cx,cy,z,g,v),flush=True)
