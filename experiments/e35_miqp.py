"""E35b: the MIQP baseline on the instances of E35 (Section 7.4).

Replays the first n instances of the configuration (M, K, k) of e35_scale.py (same seed, same generator) and
solves the cardinality-constrained long-only problem
    max 2 m'w - sum_i d_i rho_i - q   s.t.  q >= u' Sf u,  u = B'w,  sum z <= k,  z binary,  w >= 0,
with one of three formulations:
  * persp_gurobi:  w_i^2 <= rho_i z_i (perspective) and w_i <= U_i z_i, Gurobi; the size-limited license admits
                   at most 200 variables when the model has quadratic terms, so only 3M + K + 1 <= 200 (M = 50);
  * persp_scip:    the same perspective formulation with SCIP;
  * bigM_scip:     w_i^2 <= rho_i and w_i <= U_i z_i, SCIP.
    U_i = (m_i + sqrt(B_i'Sf B_i G*))_+ / d_i is valid: an optimal portfolio of any support has
    w_i = (m_i - B_i't0)_+/d_i (Theorem 2.1) and |B_i't0| <= sqrt(B_i'Sf B_i) sqrt(t0'P t0) <= sqrt(B_i'Sf B_i G*).
    The link w_i <= U_i z_i is needed also in the perspective formulation: without it, the feasibility tolerance
    of w_i^2 <= rho_i z_i with z_i = 0 and rho_i = 0 lets every asset carry a weight of the order of 1e-3, and
    the solver reports values above the optimum (this happened in a first run without the link, which was discarded).
The support {i : z_i > 1/2} of the solver's incumbent is evaluated exactly (F_LO, NNLS) and compared with the
reference; the gap is (dual bound - exact value)/exact value.
Time limit per solve (default 600 s), one thread. Each output line is one instance: the values of the reference
(branch and bound of E35, read from results/E35/<M>_<K>_<k>.jsonl) and of each solver (status, time, incumbent,
dual bound, relative gap, nodes).
Usage:  python3 -I e35_miqp.py <M> <K> <k> <n> <forms> [--tl seconds]      forms: comma separated subset of
        persp_gurobi,persp_scip,bigM_scip
"""
import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import e34_localized as E


def bigM_bounds(m, d, B, Sf, Gstar):
    sysv = np.einsum('ij,jk,ik->i', B, Sf, B)
    return np.maximum(m + np.sqrt(sysv * max(Gstar, 0.0)), 0.0) / d


def solve_gurobi(m, d, B, Sf, k, tl, U):
    import gurobipy as gp
    from gurobipy import GRB
    M, K = B.shape
    env = gp.Env(empty=True)
    env.setParam('OutputFlag', 0)
    env.start()
    mdl = gp.Model(env=env)
    mdl.Params.TimeLimit = tl
    mdl.Params.Threads = 1
    mdl.Params.MIPGap = 1e-9
    w = mdl.addMVar(M, lb=0.0, ub=U)
    z = mdl.addMVar(M, vtype=GRB.BINARY)
    rho = mdl.addMVar(M, lb=0.0)
    u = mdl.addMVar(K, lb=-GRB.INFINITY)
    q = mdl.addVar(lb=0.0)
    mdl.addConstr(u == B.T @ w)
    mdl.addConstr(w <= U * z)
    for i in range(M):
        mdl.addConstr(w[i] * w[i] <= rho[i] * z[i])
    mdl.addConstr(z.sum() <= k)
    mdl.addConstr(u @ Sf @ u <= q)
    mdl.setObjective(2 * m @ w - d @ rho - q, GRB.MAXIMIZE)
    t0 = time.time()
    mdl.optimize()
    out = dict(status={2: 'optimal', 9: 'timelimit'}.get(int(mdl.Status), str(mdl.Status)),
               time=time.time() - t0, obj=None, bound=None, nodes=int(mdl.NodeCount))
    if mdl.SolCount > 0:
        out['obj'] = float(mdl.ObjVal)
        out['bound'] = float(mdl.ObjBound)
        out['support'] = [int(i) for i in np.nonzero(z.X > 0.5)[0]]
    return out


def solve_scip(m, d, B, Sf, k, tl, form, U):
    from pyscipopt import Model, quicksum
    M, K = B.shape
    mdl = Model()
    mdl.hideOutput()
    mdl.setParam('limits/time', tl)
    mdl.setParam('limits/gap', 1e-9)
    mdl.setParam('parallel/maxnthreads', 1)
    ub = [float(x) for x in U]
    w = [mdl.addVar(lb=0.0, ub=ub[i]) for i in range(M)]
    z = [mdl.addVar(vtype='B') for _ in range(M)]
    rho = [mdl.addVar(lb=0.0) for _ in range(M)]
    u = [mdl.addVar(lb=None) for _ in range(K)]
    q = mdl.addVar(lb=0.0)
    ob = mdl.addVar(lb=None)
    for l in range(K):
        mdl.addCons(u[l] == quicksum(float(B[i, l]) * w[i] for i in range(M)))
    for i in range(M):
        mdl.addCons(w[i] <= ub[i] * z[i])
        if form == 'persp':
            mdl.addCons(w[i] * w[i] <= rho[i] * z[i])
        else:
            mdl.addCons(w[i] * w[i] <= rho[i])
    mdl.addCons(quicksum(z) <= k)
    mdl.addCons(quicksum(float(Sf[a, b]) * u[a] * u[b] for a in range(K) for b in range(K)) <= q)
    mdl.addCons(ob <= quicksum(2 * float(m[i]) * w[i] - float(d[i]) * rho[i] for i in range(M)) - q)
    mdl.setObjective(ob, 'maximize')
    t0 = time.time()
    mdl.optimize()
    out = dict(status=str(mdl.getStatus()), time=time.time() - t0, obj=None, bound=float(mdl.getDualbound()),
               nodes=int(mdl.getNNodes()))
    if mdl.getNSols() > 0:
        out['obj'] = float(mdl.getObjVal())
        sol = mdl.getBestSol()
        out['support'] = [i for i in range(M) if mdl.getSolVal(sol, z[i]) > 0.5]
    return out


def isolated(fun, args):
    """Run one solve in a child process, so that a crash of the solver (SCIP 10.0 aborted with a memory-corruption
    error, exit code 134, on three instances with M = 2000) is recorded instead of killing the run."""
    import multiprocessing as mp
    ctx = mp.get_context('fork')
    q = ctx.Queue()

    def child():
        try:
            q.put(fun(*args))
        except Exception as e:  # noqa
            q.put(dict(error=repr(e)[:200]))
    p = ctx.Process(target=child)
    p.start()
    p.join()
    if p.exitcode != 0:
        return dict(error='the solver process died with exit code %s' % p.exitcode)
    return q.get()


def main():
    M, K, k, n = map(int, sys.argv[1:5])
    forms = sys.argv[5].split(',')
    tl = float(sys.argv[sys.argv.index('--tl') + 1]) if '--tl' in sys.argv else 600.0
    here = os.path.dirname(os.path.abspath(__file__))
    ref = [json.loads(l) for l in open(os.path.join(here, 'results', 'E35', f'{M}_{K}_{k}.jsonl')) if l.strip()]
    seed = ref[0]['seed']
    rng = np.random.default_rng(seed)
    for it in range(n):
        m, d, B, Sf = E.stress_instance(rng, M, K)
        r = ref[it]
        assert r['it'] == it
        rec = dict(M=M, K=K, k=k, it=it, seed=seed, bnb=r['bnb'], bnb_time=r['bnb_time'], bnb_done=r['bnb_done'],
                   Fh=r['Fh'], G=r['G'], tl=tl)
        for f in forms:
            U = bigM_bounds(m, d, B, Sf, r['G'])
            if f == 'persp_gurobi' and 3 * M + K + 1 > 200:
                continue
            if f == 'persp_gurobi':
                job = (solve_gurobi, (m, d, B, Sf, k, tl, U))
            elif f == 'persp_scip':
                job = (solve_scip, (m, d, B, Sf, k, tl, 'persp', U))
            elif f == 'bigM_scip':
                job = (solve_scip, (m, d, B, Sf, k, tl, 'bigM', U))
            else:
                raise ValueError(f)
            o = isolated(*job)
            if o.get('support') is not None:
                sup = o.pop('support')
                o['card'] = len(sup)
                o['exact'] = float(E.flo(m, d, B, Sf, sup)[0]) if sup else 0.0
                o['vs_bnb'] = o['exact'] / r['bnb'] - 1
                if o.get('bound') is not None:
                    o['gap'] = (o['bound'] - o['exact']) / max(abs(o['exact']), 1e-12)
            rec[f] = o
        print(json.dumps(rec), flush=True)


if __name__ == '__main__':
    main()
