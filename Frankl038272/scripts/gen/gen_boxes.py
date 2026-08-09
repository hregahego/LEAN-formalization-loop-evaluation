from fractions import Fraction as F

# ---------- exact replicas of EntropyBound.Constants.{yOf,logMid,logTail,logLo,logHi} ----------
def yOf(a): return (a - 1) / (a + 1)
def logMid(a, J):
    y = yOf(a)
    return sum(2 * F(1, 2*j+1) * y**(2*j+1) for j in range(J))
def logTail(a, J):
    y = yOf(a)
    return F(2, 2*J+1) * abs(y)**(2*J+1) * (1 - y*y)**-1
def logLo(a, J): return logMid(a, J) - logTail(a, J)
def logHi(a, J): return logMid(a, J) + logTail(a, J)

J = 14        # depth for the shifted artanh series
J2 = 14       # depth for log 2

def shift_k(x):
    k = 0
    while x * 2**k < 1:
        k += 1
    assert x * 2**k < 2, (x, k)
    return k

def log_lo(x):
    k = shift_k(x)
    return logLo(x * 2**k, J) - k * logHi(F(2), J2), k
def log_hi(x):
    k = shift_k(x)
    return logHi(x * 2**k, J) - k * logLo(F(2), J2), k

D = 14                       # decimal digits kept in the emitted certificates
SC = 10**D
def rdown(q): 
    from math import floor
    n = (q * SC)
    return F(n.numerator // n.denominator, SC)
def rup(q):
    n = (q * SC)
    return F(-((-n.numerator) // n.denominator), SC)
def dec(q):
    """exact decimal string for a Fraction with denominator dividing 10**D"""
    assert SC % q.denominator == 0, q
    n = q.numerator * (SC // q.denominator)
    sign = '-' if n < 0 else ''
    n = abs(n)
    s = str(n).rjust(D+1, '0')
    return f"{sign}{s[:-D]}.{s[-D:]}"

PTS = ['1/10','3/20','1/5','1/4','3/10','7/20','2/5','9/20','1/2','11/20','3/5','13/20',
       '7/10','3/4','4/5','17/20','9/10','19/20','39/40','99/100','199/200','999/1000',
       '99999/100000']
P = [F(s) for s in PTS]

data = []
for p in P:
    l1, k1 = log_lo(1 + p); h1, _ = log_hi(1 + p)
    l2, k2 = log_lo(1 - p); h2, _ = log_hi(1 - p)
    lo1, hi1 = rdown(l1), rup(h1)
    lo2, hi2 = rdown(l2), rup(h2)
    # Q lower / upper, Qder upper
    qa = rdown(((1+p)*lo1 + (1-p)*lo2) / p**2)
    qb = rup(((1+p)*hi1 + (1-p)*hi2) / p**2)
    db = rup((-((2+p)*lo1) - (2-p)*lo2) / p**3)
    data.append(dict(p=p, lo1=lo1, hi1=hi1, lo2=lo2, hi2=hi2, k1=k1, k2=k2, qa=qa, qb=qb, db=db))

ok = True
for i in range(len(P)-1):
    a, b = data[i], data[i+1]
    nlo = a['qa'] - (1 - a['p']) * b['db']
    cert = 64 * b['qb'] <= 81 * nlo**2
    ratio = float(81*nlo**2/(64*b['qb']))
    if not (nlo > 0 and cert):
        ok = False
        print("FAIL box", i, PTS[i], PTS[i+1], float(nlo), ratio)
    else:
        print(f"box {i:2d} [{PTS[i]},{PTS[i+1]}] nlo={float(nlo):.8f} ratio={ratio:.5f}")
print("ALL OK" if ok else "SOME FAILED")

import json, sys
out = []
for d in data:
    out.append({k: (str(v) if isinstance(v, F) else v) for k, v in d.items()})
json.dump({'pts': PTS, 'data': out}, open('scripts/gen/boxdata.json','w'), indent=1)
