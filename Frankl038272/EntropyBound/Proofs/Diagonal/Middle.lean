/-
Copyright (c) 2026 EntropyBound formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EntropyBound formalization agents
-/
import EntropyBound.Defs
import EntropyBound.Theorems
import EntropyBound.Proofs.Diagonal.Endpoints
import EntropyBound.Proofs.Diagonal.Low
import EntropyBound.Proofs.Diagonal.BoxesA
import EntropyBound.Proofs.Diagonal.BoxesB
import EntropyBound.Proofs.Diagonal.BoxesC

/-!
# Stage G items G4, G5 — `diagonal_middle` (#43) and `diagonal_estimate` (#44)

`BLUEPRINT.md` Stage G item G4 / OBLIGATION 2, `SKETCH.md` (7d).

The range `[10⁻⁶, 1 - 10⁻⁶]` is covered by

* `Diagonal.Dfun_pos_low` on `(0, 1/8]` (`Proofs/Diagonal/Low.lean`), an elementary
  argument that keeps the polynomial profile term instead of discarding it, and
* the 134 derivative-corrected mean-value boxes `Diagonal.box_000 … box_133`
  tiling `[1/8, 1 - 10⁻⁶]` (`Proofs/Diagonal/Boxes{A,B,C}.lean`), each an instance of
  `Diagonal.Dfun_box_pos`.

Neither ingredient samples `Dfun`: every box lemma bounds `Dfun` on the **closed** box
`[a,b]` by `Dfun m - K·hh` where `K` is a certified bound for `|Dder|` on that box.
-/

noncomputable section

namespace EntropyBound.Diagonal

open EntropyBound

/-- The middle range `[1/8, 1 - 10⁻⁶]`, tiled by the box certificates. -/
theorem Dfun_pos_boxes {s : ℝ} (h1 : (1 : ℝ) / 8 ≤ s) (h2 : s ≤ 1 - 1 / 1000000) :
    0 < Dfun s := by
  rcases le_or_gt s (7 / 50) with hb0 | hb0
  · exact box_000 h1 hb0
  rcases le_or_gt s (4 / 25) with hb1 | hb1
  · exact box_001 hb0.le hb1
  rcases le_or_gt s (9 / 50) with hb2 | hb2
  · exact box_002 hb1.le hb2
  rcases le_or_gt s (1 / 5) with hb3 | hb3
  · exact box_003 hb2.le hb3
  rcases le_or_gt s (11 / 50) with hb4 | hb4
  · exact box_004 hb3.le hb4
  rcases le_or_gt s (6 / 25) with hb5 | hb5
  · exact box_005 hb4.le hb5
  rcases le_or_gt s (13 / 50) with hb6 | hb6
  · exact box_006 hb5.le hb6
  rcases le_or_gt s (7 / 25) with hb7 | hb7
  · exact box_007 hb6.le hb7
  rcases le_or_gt s (3 / 10) with hb8 | hb8
  · exact box_008 hb7.le hb8
  rcases le_or_gt s (8 / 25) with hb9 | hb9
  · exact box_009 hb8.le hb9
  rcases le_or_gt s (17 / 50) with hb10 | hb10
  · exact box_010 hb9.le hb10
  rcases le_or_gt s (9 / 25) with hb11 | hb11
  · exact box_011 hb10.le hb11
  rcases le_or_gt s (19 / 50) with hb12 | hb12
  · exact box_012 hb11.le hb12
  rcases le_or_gt s (2 / 5) with hb13 | hb13
  · exact box_013 hb12.le hb13
  rcases le_or_gt s (21 / 50) with hb14 | hb14
  · exact box_014 hb13.le hb14
  rcases le_or_gt s (11 / 25) with hb15 | hb15
  · exact box_015 hb14.le hb15
  rcases le_or_gt s (23 / 50) with hb16 | hb16
  · exact box_016 hb15.le hb16
  rcases le_or_gt s (12 / 25) with hb17 | hb17
  · exact box_017 hb16.le hb17
  rcases le_or_gt s (49 / 100) with hb18 | hb18
  · exact box_018 hb17.le hb18
  rcases le_or_gt s (1 / 2) with hb19 | hb19
  · exact box_019 hb18.le hb19
  rcases le_or_gt s (51 / 100) with hb20 | hb20
  · exact box_020 hb19.le hb20
  rcases le_or_gt s (13 / 25) with hb21 | hb21
  · exact box_021 hb20.le hb21
  rcases le_or_gt s (53 / 100) with hb22 | hb22
  · exact box_022 hb21.le hb22
  rcases le_or_gt s (27 / 50) with hb23 | hb23
  · exact box_023 hb22.le hb23
  rcases le_or_gt s (11 / 20) with hb24 | hb24
  · exact box_024 hb23.le hb24
  rcases le_or_gt s (14 / 25) with hb25 | hb25
  · exact box_025 hb24.le hb25
  rcases le_or_gt s (57 / 100) with hb26 | hb26
  · exact box_026 hb25.le hb26
  rcases le_or_gt s (29 / 50) with hb27 | hb27
  · exact box_027 hb26.le hb27
  rcases le_or_gt s (59 / 100) with hb28 | hb28
  · exact box_028 hb27.le hb28
  rcases le_or_gt s (599 / 1000) with hb29 | hb29
  · exact box_029 hb28.le hb29
  rcases le_or_gt s (607 / 1000) with hb30 | hb30
  · exact box_030 hb29.le hb30
  rcases le_or_gt s (307 / 500) with hb31 | hb31
  · exact box_031 hb30.le hb31
  rcases le_or_gt s (31 / 50) with hb32 | hb32
  · exact box_032 hb31.le hb32
  rcases le_or_gt s (313 / 500) with hb33 | hb33
  · exact box_033 hb32.le hb33
  rcases le_or_gt s (63 / 100) with hb34 | hb34
  · exact box_034 hb33.le hb34
  rcases le_or_gt s (127 / 200) with hb35 | hb35
  · exact box_035 hb34.le hb35
  rcases le_or_gt s (16 / 25) with hb36 | hb36
  · exact box_036 hb35.le hb36
  rcases le_or_gt s (161 / 250) with hb37 | hb37
  · exact box_037 hb36.le hb37
  rcases le_or_gt s (81 / 125) with hb38 | hb38
  · exact box_038 hb37.le hb38
  rcases le_or_gt s (163 / 250) with hb39 | hb39
  · exact box_039 hb38.le hb39
  rcases le_or_gt s (131 / 200) with hb40 | hb40
  · exact box_040 hb39.le hb40
  rcases le_or_gt s (329 / 500) with hb41 | hb41
  · exact box_041 hb40.le hb41
  rcases le_or_gt s (33 / 50) with hb42 | hb42
  · exact box_042 hb41.le hb42
  rcases le_or_gt s (331 / 500) with hb43 | hb43
  · exact box_043 hb42.le hb43
  rcases le_or_gt s (83 / 125) with hb44 | hb44
  · exact box_044 hb43.le hb44
  rcases le_or_gt s (333 / 500) with hb45 | hb45
  · exact box_045 hb44.le hb45
  rcases le_or_gt s (167 / 250) with hb46 | hb46
  · exact box_046 hb45.le hb46
  rcases le_or_gt s (67 / 100) with hb47 | hb47
  · exact box_047 hb46.le hb47
  rcases le_or_gt s (84 / 125) with hb48 | hb48
  · exact box_048 hb47.le hb48
  rcases le_or_gt s (337 / 500) with hb49 | hb49
  · exact box_049 hb48.le hb49
  rcases le_or_gt s (27 / 40) with hb50 | hb50
  · exact box_050 hb49.le hb50
  rcases le_or_gt s (169 / 250) with hb51 | hb51
  · exact box_051 hb50.le hb51
  rcases le_or_gt s (677 / 1000) with hb52 | hb52
  · exact box_052 hb51.le hb52
  rcases le_or_gt s (339 / 500) with hb53 | hb53
  · exact box_053 hb52.le hb53
  rcases le_or_gt s (679 / 1000) with hb54 | hb54
  · exact box_054 hb53.le hb54
  rcases le_or_gt s (17 / 25) with hb55 | hb55
  · exact box_055 hb54.le hb55
  rcases le_or_gt s (681 / 1000) with hb56 | hb56
  · exact box_056 hb55.le hb56
  rcases le_or_gt s (341 / 500) with hb57 | hb57
  · exact box_057 hb56.le hb57
  rcases le_or_gt s (683 / 1000) with hb58 | hb58
  · exact box_058 hb57.le hb58
  rcases le_or_gt s (171 / 250) with hb59 | hb59
  · exact box_059 hb58.le hb59
  rcases le_or_gt s (137 / 200) with hb60 | hb60
  · exact box_060 hb59.le hb60
  rcases le_or_gt s (343 / 500) with hb61 | hb61
  · exact box_061 hb60.le hb61
  rcases le_or_gt s (687 / 1000) with hb62 | hb62
  · exact box_062 hb61.le hb62
  rcases le_or_gt s (86 / 125) with hb63 | hb63
  · exact box_063 hb62.le hb63
  rcases le_or_gt s (689 / 1000) with hb64 | hb64
  · exact box_064 hb63.le hb64
  rcases le_or_gt s (69 / 100) with hb65 | hb65
  · exact box_065 hb64.le hb65
  rcases le_or_gt s (691 / 1000) with hb66 | hb66
  · exact box_066 hb65.le hb66
  rcases le_or_gt s (173 / 250) with hb67 | hb67
  · exact box_067 hb66.le hb67
  rcases le_or_gt s (693 / 1000) with hb68 | hb68
  · exact box_068 hb67.le hb68
  rcases le_or_gt s (347 / 500) with hb69 | hb69
  · exact box_069 hb68.le hb69
  rcases le_or_gt s (139 / 200) with hb70 | hb70
  · exact box_070 hb69.le hb70
  rcases le_or_gt s (87 / 125) with hb71 | hb71
  · exact box_071 hb70.le hb71
  rcases le_or_gt s (349 / 500) with hb72 | hb72
  · exact box_072 hb71.le hb72
  rcases le_or_gt s (7 / 10) with hb73 | hb73
  · exact box_073 hb72.le hb73
  rcases le_or_gt s (351 / 500) with hb74 | hb74
  · exact box_074 hb73.le hb74
  rcases le_or_gt s (88 / 125) with hb75 | hb75
  · exact box_075 hb74.le hb75
  rcases le_or_gt s (353 / 500) with hb76 | hb76
  · exact box_076 hb75.le hb76
  rcases le_or_gt s (177 / 250) with hb77 | hb77
  · exact box_077 hb76.le hb77
  rcases le_or_gt s (71 / 100) with hb78 | hb78
  · exact box_078 hb77.le hb78
  rcases le_or_gt s (713 / 1000) with hb79 | hb79
  · exact box_079 hb78.le hb79
  rcases le_or_gt s (179 / 250) with hb80 | hb80
  · exact box_080 hb79.le hb80
  rcases le_or_gt s (719 / 1000) with hb81 | hb81
  · exact box_081 hb80.le hb81
  rcases le_or_gt s (361 / 500) with hb82 | hb82
  · exact box_082 hb81.le hb82
  rcases le_or_gt s (363 / 500) with hb83 | hb83
  · exact box_083 hb82.le hb83
  rcases le_or_gt s (73 / 100) with hb84 | hb84
  · exact box_084 hb83.le hb84
  rcases le_or_gt s (147 / 200) with hb85 | hb85
  · exact box_085 hb84.le hb85
  rcases le_or_gt s (37 / 50) with hb86 | hb86
  · exact box_086 hb85.le hb86
  rcases le_or_gt s (149 / 200) with hb87 | hb87
  · exact box_087 hb86.le hb87
  rcases le_or_gt s (3 / 4) with hb88 | hb88
  · exact box_088 hb87.le hb88
  rcases le_or_gt s (189 / 250) with hb89 | hb89
  · exact box_089 hb88.le hb89
  rcases le_or_gt s (19 / 25) with hb90 | hb90
  · exact box_090 hb89.le hb90
  rcases le_or_gt s (767 / 1000) with hb91 | hb91
  · exact box_091 hb90.le hb91
  rcases le_or_gt s (31 / 40) with hb92 | hb92
  · exact box_092 hb91.le hb92
  rcases le_or_gt s (39 / 50) with hb93 | hb93
  · exact box_093 hb92.le hb93
  rcases le_or_gt s (789 / 1000) with hb94 | hb94
  · exact box_094 hb93.le hb94
  rcases le_or_gt s (799 / 1000) with hb95 | hb95
  · exact box_095 hb94.le hb95
  rcases le_or_gt s (81 / 100) with hb96 | hb96
  · exact box_096 hb95.le hb96
  rcases le_or_gt s (41 / 50) with hb97 | hb97
  · exact box_097 hb96.le hb97
  rcases le_or_gt s (83 / 100) with hb98 | hb98
  · exact box_098 hb97.le hb98
  rcases le_or_gt s (21 / 25) with hb99 | hb99
  · exact box_099 hb98.le hb99
  rcases le_or_gt s (17 / 20) with hb100 | hb100
  · exact box_100 hb99.le hb100
  rcases le_or_gt s (43 / 50) with hb101 | hb101
  · exact box_101 hb100.le hb101
  rcases le_or_gt s (87 / 100) with hb102 | hb102
  · exact box_102 hb101.le hb102
  rcases le_or_gt s (22 / 25) with hb103 | hb103
  · exact box_103 hb102.le hb103
  rcases le_or_gt s (89 / 100) with hb104 | hb104
  · exact box_104 hb103.le hb104
  rcases le_or_gt s (9 / 10) with hb105 | hb105
  · exact box_105 hb104.le hb105
  rcases le_or_gt s (91 / 100) with hb106 | hb106
  · exact box_106 hb105.le hb106
  rcases le_or_gt s (23 / 25) with hb107 | hb107
  · exact box_107 hb106.le hb107
  rcases le_or_gt s (93 / 100) with hb108 | hb108
  · exact box_108 hb107.le hb108
  rcases le_or_gt s (47 / 50) with hb109 | hb109
  · exact box_109 hb108.le hb109
  rcases le_or_gt s (19 / 20) with hb110 | hb110
  · exact box_110 hb109.le hb110
  rcases le_or_gt s (24 / 25) with hb111 | hb111
  · exact box_111 hb110.le hb111
  rcases le_or_gt s (97 / 100) with hb112 | hb112
  · exact box_112 hb111.le hb112
  rcases le_or_gt s (489 / 500) with hb113 | hb113
  · exact box_113 hb112.le hb113
  rcases le_or_gt s (123 / 125) with hb114 | hb114
  · exact box_114 hb113.le hb114
  rcases le_or_gt s (989 / 1000) with hb115 | hb115
  · exact box_115 hb114.le hb115
  rcases le_or_gt s (124 / 125) with hb116 | hb116
  · exact box_116 hb115.le hb116
  rcases le_or_gt s (199 / 200) with hb117 | hb117
  · exact box_117 hb116.le hb117
  rcases le_or_gt s (997 / 1000) with hb118 | hb118
  · exact box_118 hb117.le hb118
  rcases le_or_gt s (499 / 500) with hb119 | hb119
  · exact box_119 hb118.le hb119
  rcases le_or_gt s (2497 / 2500) with hb120 | hb120
  · exact box_120 hb119.le hb120
  rcases le_or_gt s (9993 / 10000) with hb121 | hb121
  · exact box_121 hb120.le hb121
  rcases le_or_gt s (2499 / 2500) with hb122 | hb122
  · exact box_122 hb121.le hb122
  rcases le_or_gt s (9997 / 10000) with hb123 | hb123
  · exact box_123 hb122.le hb123
  rcases le_or_gt s (4999 / 5000) with hb124 | hb124
  · exact box_124 hb123.le hb124
  rcases le_or_gt s (99989 / 100000) with hb125 | hb125
  · exact box_125 hb124.le hb125
  rcases le_or_gt s (49997 / 50000) with hb126 | hb126
  · exact box_126 hb125.le hb126
  rcases le_or_gt s (99997 / 100000) with hb127 | hb127
  · exact box_127 hb126.le hb127
  rcases le_or_gt s (49999 / 50000) with hb128 | hb128
  · exact box_128 hb127.le hb128
  rcases le_or_gt s (99999 / 100000) with hb129 | hb129
  · exact box_129 hb128.le hb129
  rcases le_or_gt s (199999 / 200000) with hb130 | hb130
  · exact box_130 hb129.le hb130
  rcases le_or_gt s (999997 / 1000000) with hb131 | hb131
  · exact box_131 hb130.le hb131
  rcases le_or_gt s (499999 / 500000) with hb132 | hb132
  · exact box_132 hb131.le hb132
  rcases le_or_gt s (999999 / 1000000) with hb133 | hb133
  · exact box_133 hb132.le hb133
  · linarith

end EntropyBound.Diagonal

namespace EntropyBound

open EntropyBound.Diagonal

/-- **Frozen #43** (`Theorems.lean:193`). -/
theorem diagonal_middle_proof :
    ∀ s : ℝ, 1 / 1000000 ≤ s → s ≤ 1 - 1 / 1000000 → 0 < Dfun s := by
  intro s hlo hhi
  rcases le_or_gt s (1 / 8 : ℝ) with h | h
  · exact Dfun_pos_low (by linarith) h
  · exact Dfun_pos_boxes h.le hhi

/-- **Frozen #44** (`Theorems.lean:196`). -/
theorem diagonal_estimate_proof : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ Dfun s := by
  intro s hs0 hs1
  rcases eq_or_lt_of_le hs1 with heq | hlt
  · rw [heq, EntropyBound.diagonal_at_one_proof]
  · rcases le_or_gt s (1 / 1000000) with hsm | hsm
    · exact (EntropyBound.diagonal_small_proof s hs0 hsm).le
    · rcases le_or_gt (1 - 1 / 1000000) s with hlg | hlg
      · exact (EntropyBound.diagonal_large_proof s hlg hlt).le
      · exact (diagonal_middle_proof s hsm.le hlg.le).le

end EntropyBound

namespace EntropyBound.Solution

theorem diagonal_middle :
    ∀ s : ℝ, 1 / 1000000 ≤ s → s ≤ 1 - 1 / 1000000 → 0 < Dfun s :=
  EntropyBound.diagonal_middle_proof

theorem diagonal_estimate : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ Dfun s :=
  EntropyBound.diagonal_estimate_proof

end EntropyBound.Solution

/-! ### No-drift gates -/

example : @EntropyBound.diagonal_middle = @EntropyBound.Solution.diagonal_middle := rfl
example : @EntropyBound.diagonal_estimate = @EntropyBound.Solution.diagonal_estimate := rfl

/-! ### Guardrails -/

example : EntropyBound.Dfun 1 = 0 := EntropyBound.diagonal_at_one_proof

/-- The Stage G cheat-watch spot check, now proved by the **derivative-corrected** box
machinery on a box of width `10⁻³` (the endpoint-monotone certificate of
`Proofs/Diagonal/Enclose.lean` needed width `6 · 10⁻⁶`). -/
example : 0 < EntropyBound.Dfun (686 / 1000) :=
  EntropyBound.diagonal_middle_proof (686 / 1000) (by norm_num) (by norm_num)

end
