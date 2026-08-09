import json
from fractions import Fraction as F
exec(open('scripts/gen/gen_boxes.py').read().split("PTS = ")[0])   # reuse helpers

d = json.load(open('scripts/gen/boxdata.json'))
PTS = d['pts']
DATA = [{k: (F(v) if k not in ('k1','k2') else v) for k, v in e.items()} for e in d['data']]
N = len(PTS)

def q(x):  # Lean numeral for a Fraction point like 3/20
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else str(x.numerator)

HEAD = '''/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Proofs.EntropySpeed.Enclose

/-!
# Stage E item E3 — %s

Certified endpoint enclosures and per-box lower bounds for
`Ader z = (Qser z - (1-z) * Qder z) / Real.sqrt (Qser z)` on %s.

Every number here is a **certificate**: the `Real.log` bounds come from
`EntropyBound.EntropySpeed.log_ge_of` / `.log_le_of` (the shared artanh series of
`EntropyBound.Constants.logLo`/`logHi` at depth `J = 14`, after a `2 ^ k` shift), the
`Qser`/`Qder` bounds from `EntropyBound.EntropySpeed.Qser_ge_of` / `.Qser_le_of` /
`.Qder_le_of`, and each `box_*` lemma from `EntropyBound.EntropySpeed.box_bound`, which
bounds `Ader` on the whole **closed** box — no grid evaluation anywhere.
-/

noncomputable section

namespace EntropyBound.EntropySpeed

open EntropyBound.Constants

'''

def log_block(i, which):
    """which in {'lo1','hi1','lo2','hi2'}"""
    e = DATA[i]; p = e['p']
    if which in ('lo1', 'hi1'):
        x = 1 + p; arg = f"1 + {q(p)}"; k = e['k1']
    else:
        x = 1 - p; arg = f"1 - {q(p)}"; k = e['k2']
    c = e[which]
    nm = f"{which}_{i}"
    if which.startswith('lo'):
        stmt = f"theorem {nm} : ({dec(c)} : ℝ) ≤ Real.log ({arg}) := by"
        call = f"log_ge_of ({q(x)}) ({dec(c)}) {k} {J} {J2} (by norm_num)"
    else:
        stmt = f"theorem {nm} : Real.log ({arg}) ≤ ({dec(c)} : ℝ) := by"
        call = f"log_le_of ({q(x)}) ({dec(c)}) {k} {J} {J2} (by norm_num)"
    return (f"{stmt}\n"
            f"  have h := {call}\n"
            f"    (by norm_num [logLo, logHi, logMid, logTail_of_one_le, yOf, Finset.sum_range_succ])\n"
            f"  norm_num at h ⊢\n"
            f"  linarith\n")

def qlo_block(i):
    e = DATA[i]
    return (f"theorem Qlo_{i} : ({dec(e['qa'])} : ℝ) ≤ Qser ({q(e['p'])}) :=\n"
            f"  Qser_ge_of (by norm_num) (by norm_num) lo1_{i} lo2_{i} (by norm_num)\n")

def qhi_block(i):
    e = DATA[i]
    return (f"theorem Qhi_{i} : Qser ({q(e['p'])}) ≤ ({dec(e['qb'])} : ℝ) :=\n"
            f"  Qser_le_of (by norm_num) (by norm_num) hi1_{i} hi2_{i} (by norm_num)\n")

def dhi_block(i):
    e = DATA[i]
    return (f"theorem Dhi_{i} : Qder ({q(e['p'])}) ≤ ({dec(e['db'])} : ℝ) :=\n"
            f"  Qder_le_of (by norm_num) (by norm_num) lo1_{i} lo2_{i} (by norm_num)\n")

def box_block(j):
    a = DATA[j]['p']; b = DATA[j+1]['p']
    return (f"theorem box_{j} : ∀ z : ℝ, {q(a)} ≤ z → z ≤ {q(b)} →\n"
            f"    8 / 9 ≤ (Qser z - (1 - z) * Qder z) / Real.sqrt (Qser z) := by\n"
            f"  refine box_bound (a := {q(a)}) (b := {q(b)}) ?_ ?_ ?_ Qlo_{j} Qhi_{j+1} Dhi_{j+1} ?_ ?_ <;>\n"
            f"    norm_num\n")

def emit(fname, title, rng, pt_lo, pt_hi, boxes, need_qlo, need_hi, skip_logs=()):
    out = [HEAD % (title, rng)]
    for i in range(pt_lo, pt_hi + 1):
        out.append(f"/-! #### Certificates at `z = {q(DATA[i]['p'])}` -/\n\n")
        if i in need_qlo or i in need_hi:
            if (i in need_qlo or i in need_hi) and i not in skip_logs:
                out.append(log_block(i, 'lo1')); out.append("\n")
                out.append(log_block(i, 'lo2')); out.append("\n")
            if i in need_hi and i not in skip_logs:
                out.append(log_block(i, 'hi1')); out.append("\n")
                out.append(log_block(i, 'hi2')); out.append("\n")
            if i in need_qlo:
                out.append(qlo_block(i)); out.append("\n")
            if i in need_hi:
                out.append(qhi_block(i)); out.append("\n")
                out.append(dhi_block(i)); out.append("\n")
    out.append("/-! #### The per-box bounds -/\n\n")
    for j in boxes:
        out.append(box_block(j)); out.append("\n")
    out.append("end EntropyBound.EntropySpeed\n\nend\n")
    open(fname, 'w').write("".join(out))

SPLIT = 11
# BoxesLow: points 0..SPLIT, boxes 0..SPLIT-1
emit('EntropyBound/Proofs/EntropySpeed/BoxesLow.lean',
     'box certificates on `[1/10, 13/20]`', '`[1/10, 13/20]`',
     0, SPLIT, list(range(0, SPLIT)),
     need_qlo=set(range(0, SPLIT)), need_hi=set(range(1, SPLIT + 1)))
# BoxesHigh: points SPLIT..N-1, boxes SPLIT..N-2 ; Qlo_SPLIT comes from BoxesLow
out_head = None
emit('EntropyBound/Proofs/EntropySpeed/BoxesHigh.lean',
     'box certificates on `[13/20, 99999/100000]`', '`[13/20, 99999/100000]`',
     SPLIT, N - 1, list(range(SPLIT, N - 1)),
     need_qlo=set(range(SPLIT, N - 1)), need_hi=set(range(SPLIT + 1, N)),
     skip_logs={SPLIT})
# BoxesHigh must import BoxesLow (for Qlo_11 .. and lo1_11/lo2_11 already there)
s = open('EntropyBound/Proofs/EntropySpeed/BoxesHigh.lean').read()
s = s.replace('import EntropyBound.Proofs.EntropySpeed.Enclose',
              'import EntropyBound.Proofs.EntropySpeed.BoxesLow')
open('EntropyBound/Proofs/EntropySpeed/BoxesHigh.lean','w').write(s)
print("emitted")
