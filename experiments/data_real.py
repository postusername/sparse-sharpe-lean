"""Real data of Section 6: factor models V = diag(d) + B Sf B' from public data.

Files (downloaded into data/ on first use and checked against data/SHA256SUMS when that file lists them):
  * K. R. French data library: 49_Industry_Portfolios_CSV.zip, F-F_Research_Data_Factors_CSV.zip,
    F-F_Research_Data_5_Factors_2x3_CSV.zip -- monthly returns, the 120 months July 2016 - June 2026 (fixed dates;
    the library is updated every month and revised occasionally, so the checksums of the files used are recorded);
  * OR-Library (J. E. Beasley): port1..port5.txt (Chang et al. 2000: Hang Seng, DAX, FTSE 100, S&P 100, Nikkei 225),
    indtrack6.txt (S&P 500, 457 stocks, 291 weekly prices), indtrack8.txt (Russell 3000, 2151 stocks; the stocks with
    a weekly return above 100% in absolute value are removed).

model(name, K) -> dict(name, m, d, B, Sf, M, K, omega, names) with d > 0.
FF49-K1/K3/K5: time-series regressions with intercept on the market factor, the three and the five Fama-French
factors; the others: statistical factor models from the K leading eigenpairs of the covariance matrix.
"""
import hashlib
import io
import os
import re
import sys
import urllib.request
import zipfile

import numpy as np

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
FF = "https://mba.tuck.dartmouth.edu/pages/faculty/ken.french/ftp/"
OR = "https://people.brunel.ac.uk/~mastjjb/jeb/orlib/files/"
FIRST, LAST = 201607, 202606          # the window of the paper (120 months)


def _sums():
    p = os.path.join(DATA, "SHA256SUMS")
    if not os.path.exists(p):
        return {}
    out = {}
    for ln in open(p):
        if ln.strip() and not ln.startswith("#"):
            h, f = ln.split()
            out[f] = h
    return out


def _fetch(url, fname):
    os.makedirs(DATA, exist_ok=True)
    path = os.path.join(DATA, fname)
    if not os.path.exists(path):
        with urllib.request.urlopen(url, timeout=120) as r, open(path, "wb") as f:
            f.write(r.read())
    want = _sums().get(fname)
    if want:
        got = hashlib.sha256(open(path, "rb").read()).hexdigest()
        if got != want:
            print("WARNING: %s differs from the file used in the paper (sha256 %s, expected %s); the French data "
                  "library revises its files from time to time" % (fname, got[:12], want[:12]), file=sys.stderr)
    return path


def _zip_csv(path):
    with zipfile.ZipFile(path) as z:
        name = [n for n in z.namelist() if n.lower().endswith(".csv")][0]
        return z.read(name).decode("latin-1").splitlines()


def _monthly_block(lines, header_has):
    """The first monthly block: rows YYYYMM, v1..vn after the header line that contains header_has."""
    hdr = next(i for i, ln in enumerate(lines) if header_has in ln)
    names = [p.strip() for p in lines[hdr].split(",")][1:]
    rows, dates = [], []
    for ln in lines[hdr + 1:]:
        parts = [p.strip() for p in ln.split(",")]
        if len(parts) != len(names) + 1 or not re.fullmatch(r"\d{6}", parts[0]):
            if rows:
                break
            continue
        dates.append(int(parts[0]))
        rows.append([float(x) for x in parts[1:]])
    return np.array(dates), np.array(rows), names


def load_ff_monthly():
    ind = _monthly_block(_zip_csv(_fetch(FF + "49_Industry_Portfolios_CSV.zip", "ff49m.zip")), "Agric")
    f3 = _monthly_block(_zip_csv(_fetch(FF + "F-F_Research_Data_Factors_CSV.zip", "ff3m.zip")), "Mkt-RF")
    f5 = _monthly_block(_zip_csv(_fetch(FF + "F-F_Research_Data_5_Factors_2x3_CSV.zip", "ff5m.zip")), "Mkt-RF")
    common = np.intersect1d(np.intersect1d(ind[0], f3[0]), f5[0])
    common = common[(common >= FIRST) & (common <= LAST)]
    assert len(common) == 120, (len(common), common[:1], common[-1:])
    pick = lambda blk: blk[1][np.searchsorted(blk[0], common)]
    R = pick(ind) / 100.0
    R[R <= -0.99] = np.nan
    F3, F5 = pick(f3), pick(f5)
    rf = F3[:, 3] / 100.0
    ok = ~np.isnan(R).any(axis=1)
    assert ok.all(), 'missing values in the window'
    return dict(dates=common[ok], R=R[ok] - rf[ok][:, None], F3=F3[ok, :3] / 100.0, F5=F5[ok, :5] / 100.0,
                names=ind[2])


def _regression_model(R, F):
    T = len(R)
    X = np.hstack([np.ones((T, 1)), F])
    coef, *_ = np.linalg.lstsq(X, R, rcond=None)
    B = coef[1:].T
    resid = R - X @ coef
    d = resid.var(axis=0, ddof=X.shape[1])
    Sf = np.cov(F.T) if F.shape[1] > 1 else np.array([[F.var(ddof=1)]])
    m = R.mean(axis=0)
    return m, d, B, Sf


def _pca_model(m, V, K):
    w, U = np.linalg.eigh(V)
    idx = np.argsort(w)[::-1][:K]
    B = U[:, idx] * np.sqrt(w[idx])
    d = np.diag(V) - np.sum(B ** 2, axis=1)
    return m, d, B, np.eye(K)


def load_port(i):
    toks = open(_fetch(OR + f"port{i}.txt", f"port{i}.txt")).read().split()
    n = int(toks[0])
    mu = np.array(toks[1:1 + 2 * n:2], float)
    sd = np.array(toks[2:2 + 2 * n:2], float)
    C = np.eye(n)
    rest = toks[1 + 2 * n:]
    for a in range(0, len(rest) - 2, 3):
        p, q = int(rest[a]) - 1, int(rest[a + 1]) - 1
        if 0 <= p < n and 0 <= q < n:
            C[p, q] = C[q, p] = float(rest[a + 2])
    V = C * np.outer(sd, sd)
    return mu, V


def load_indtrack(i):
    path = _fetch(OR + f"indtrack{i}.txt", f"indtrack{i}.txt")
    toks = open(path).read().split()
    N, T = int(toks[0]), int(toks[1])
    vals = np.array(toks[2:], float)
    # T weekly periods, T + 1 prices; the first series is the index, then the stocks (indtrack8 has one series more
    # than its header says: the first N stocks are taken)
    P = vals[:(len(vals) // (T + 1)) * (T + 1)].reshape(-1, T + 1)[1:N + 1]
    ret = P[:, 1:] / P[:, :-1] - 1.0
    bad = np.abs(ret).max(axis=1) > 1.0
    ret = ret[~bad]
    return ret.mean(axis=1), np.cov(ret), int(bad.sum())


def model(name, K):
    """name: 'FF49' | 'port1'..'port5' | 'SP500' | 'Russell'."""
    names = None
    if name == "FF49":
        D = load_ff_monthly()
        names = D["names"]
        F = {1: D["F3"][:, :1], 3: D["F3"], 5: D["F5"]}[K]
        m, d, B, Sf = _regression_model(D["R"], F)
    elif name.startswith("port"):
        mu, V = load_port(int(name[4:]))
        m, d, B, Sf = _pca_model(mu, V, K)
    elif name in ("SP500", "Russell"):
        mu, V, nbad = load_indtrack(6 if name == "SP500" else 8)
        m, d, B, Sf = _pca_model(mu, V, K)
    else:
        raise ValueError(name)
    assert np.all(d > 0), (name, K, d.min())
    omega = float(np.max(np.einsum("ij,jk,ik->i", B, Sf, B) / d))
    return dict(name=f"{name}-K{K}", m=m, d=d, B=B, Sf=Sf, M=len(m), K=K, omega=omega, names=names)


if __name__ == "__main__":
    for nm, Ks in [("FF49", [1, 3, 5]), ("port1", [1, 3, 5]), ("port5", [1, 3, 5]),
                   ("SP500", [1, 3, 5, 10]), ("Russell", [1, 3, 5, 10])]:
        for K in Ks:
            mdl = model(nm, K)
            print("%-14s M=%4d K=%2d  ω=max B'ΣB/d = %8.3f  max V_ii/d_i = %8.3f  m>0: %d" % (
                mdl["name"], mdl["M"], K, mdl["omega"], 1 + mdl["omega"], int((mdl["m"] > 0).sum())))
