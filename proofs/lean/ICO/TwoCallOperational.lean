import ICO.TwoCallCertificate
import ICO.BudgetTesting
import ICO.HaarMoments
import ICO.AllChannelPadding
import QIT.Util.SDP.HermitianPSDTraceDuality

/-!
# Unconditional operational proof of Proposition `prop:two-call`

This module closes the operational link between the kernel-checked rational SDP dual
certificate in `ICO.TwoCallCertificate` and arbitrary two-call adaptive quantum
strategies (`ICO.BudgetQueryTree.Tree (Fin 4 × M) O 2 B`).

Specifically:
1. **Section 1**: Proves positive semidefiniteness of the `256 × 256` dual matrices
   `Z` and `Z - Δ` via approximate integer block-Cholesky factors paired with exact
   diagonally dominant Gershgorin remainders decomposed into rank-one PSD matrices,
   together with `W_0 - W_1 = Δ` and the causal partial-trace identities on `Wires4`.
2. **Section 2**: Compiles any two-call `BudgetQueryTree.Tree (Fin 4 × M) O 2 B`,
   initial state `ρ : State B`, and `T : BinaryHypothesisTest O` (with zero extra
   `Nonempty` assumptions on `M`, `O`, `B`) via `ICO.AdaptiveSequentialProtocol.budget`
   into explicit positive semidefinite two-slot tester matrices `testerAccept` and
   `testerReject` on `Wires4`, proving the Born-Choi trace identity and causal dual
   trace collapse `(zMatrix * (testerAccept + testerReject)).trace.re = 4 / 25`.
3. **Section 3**: Identifies the Haar-averaged two-copy Choi operator of rank-one
   dephasing `Δ_U` with `w0Matrix` via `QIT.unitaryTwirl` invariance on the 17-dimensional
   commutant space, identifies `choiTwoCopy modelChannel = w1Matrix`, and derives the
   noise-interpolated identity for `E_{p,U} = (1 - p) id + p Δ_U` vs `M_p = (1 - p) id + p Λ`.
4. **Section 4**: Combines Sections 1–3 with `ICO.TwoCallCertificate.two_call_switch_success`
   to prove Proposition `prop:two-call` unconditionally (both at `p = 1` and for general
   noise rate `0 ≤ p ≤ 1`).
-/

namespace ICO.TwoCallOperational

open Matrix QIT MeasureTheory
open ICO.TwoCallCertificate ICO.SwitchObservable ICO.SwitchExperiment
open ICO.BudgetQueryTree ICO.BudgetTesting
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option maxRecDepth 200000
set_option maxHeartbeats 2400000
set_option Elab.async false

/-! ## Section 1: Wire indexing and Gershgorin + block-Cholesky PSD soundness -/

/-- Four-wire index `(a_I, a_O, b_I, b_O)` on `Fin 4` matching `encode4`. -/
abbrev Wires4 := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- Encode `(ai, ao, bi, bo) : Wires4` into `Fin 256`. -/
def wires4ToFin256 (w : Wires4) : Fin 256 :=
  ⟨encode4 w.1.val w.2.1.val w.2.2.1.val w.2.2.2.val, by
    rcases w with ⟨ai, ao, bi, bo⟩
    dsimp [encode4]
    omega⟩

/-- Decode `Fin 256` into `Wires4`. -/
def fin256ToWires4 (idx : Fin 256) : Wires4 :=
  (⟨idx.val / 64 % 4, by omega⟩,
   ⟨idx.val / 16 % 4, by omega⟩,
   ⟨idx.val / 4 % 4, by omega⟩,
   ⟨idx.val % 4, by omega⟩)

/-- Canonical bijection `Wires4 ≃ Fin 256`. -/
def wires4Equiv : Wires4 ≃ Fin 256 where
  toFun := wires4ToFin256
  invFun := fin256ToWires4
  left_inv w := by
    rcases w with ⟨ai, ao, bi, bo⟩
    ext <;> dsimp [wires4ToFin256, fin256ToWires4, encode4] <;> omega
  right_inv idx := by
    ext
    dsimp [wires4ToFin256, fin256ToWires4, encode4]
    omega

@[simp] theorem fin256ToWires4_wires4ToFin256 (w : Wires4) :
    fin256ToWires4 (wires4ToFin256 w) = w :=
  wires4Equiv.left_inv w

@[simp] theorem wires4ToFin256_fin256ToWires4 (idx : Fin 256) :
    wires4ToFin256 (fin256ToWires4 idx) = idx :=
  wires4Equiv.right_inv idx

private theorem of_range_all {n : Nat} {P : Nat → Bool}
    (h : (List.range n).all P = true) {k : Nat} (hk : k < n) : P k = true :=
  (List.all_eq_true.mp h) k (List.mem_range.mpr hk)

theorem sumBelow_eq_sum_range (n : Nat) (f : Nat → Int) :
    sumBelow n f = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumBelow, Finset.sum_range_succ, ih]

/-- Partition of `0..255` into 55 charge-sector blocks. -/
def blocks55 : List (List Nat) := [[51], [35, 50], [34], [19, 49], [18, 33], [17], [55, 115], [39, 54, 99, 114], [38, 98], [59, 179], [3, 23, 43, 48, 53, 58, 63, 83, 113, 163, 178, 243], [2, 22, 62, 32, 37, 47, 42, 82, 97, 242, 227, 162], [46, 226], [27, 57, 147, 177], [1, 41, 61, 16, 26, 31, 21, 161, 146, 241, 211, 81], [30, 45, 210, 225], [25, 145], [29, 209], [119], [103, 118], [102], [123, 183], [87, 67, 107, 117, 112, 122, 127, 7, 52, 167, 182, 247], [86, 66, 126, 101, 96, 111, 106, 6, 36, 246, 231, 166], [110, 230], [187], [171, 131, 151, 186, 176, 181, 191, 11, 56, 91, 121, 251], [0, 5, 10, 15, 20, 40, 60, 65, 80, 85, 90, 95, 105, 125, 130, 150, 160, 165, 170, 175, 190, 195, 215, 235, 240, 245, 250, 255], [254, 194, 214, 239, 224, 229, 234, 14, 44, 94, 109, 174], [238], [155, 185], [169, 129, 189, 154, 144, 159, 149, 9, 24, 249, 219, 89], [253, 193, 233, 223, 208, 218, 213, 13, 28, 173, 158, 93], [222, 237], [153], [157, 217], [221], [71, 116], [70, 100], [75, 120, 135, 180], [84, 104, 124, 69, 74, 79, 64, 164, 134, 244, 199, 4], [78, 108, 198, 228], [139, 184], [168, 148, 188, 138, 133, 143, 128, 88, 73, 248, 203, 8], [252, 212, 232, 207, 197, 202, 192, 92, 77, 172, 142, 12], [206, 236], [137, 152], [141, 156, 201, 216], [205, 220], [68], [72, 132], [76, 196], [136], [140, 200], [204]]

/-- Canonical `S_4`-representative ID `0..5` for each of the 55 charge blocks. -/
def blockRepId55 : List Nat := [0, 1, 0, 1, 1, 0, 2, 3, 2, 2, 4, 4, 2, 3, 4, 3, 2, 2, 0, 1, 0, 2, 4, 4, 2, 0, 4, 5, 4, 0, 1, 4, 4, 1, 0, 2, 0, 1, 1, 3, 4, 3, 1, 4, 4, 1, 1, 3, 1, 0, 2, 2, 0, 2, 0]

/-- Block index `b ∈ 0..54` of each of the 6 canonical representative blocks `0..5`. -/
def repBlockIdx6 : List Nat := [0, 1, 6, 7, 10, 27]

/-- `16 × 16` nested list lookup `(blockId, localPos)` for each `idx ∈ 0..255`. -/
def idxToBlkPos16x16 : List (List (Nat × Nat)) := [
  [(27, 0), (14, 0), (11, 0), (10, 0), (40, 11), (27, 1), (23, 7), (22, 7), (43, 11), (31, 7), (27, 2), (26, 7), (44, 11), (32, 7), (28, 7), (27, 3)],
  [(14, 3), (5, 0), (4, 0), (3, 0), (27, 4), (14, 6), (11, 1), (10, 1), (31, 8), (16, 0), (14, 4), (13, 0), (32, 8), (17, 0), (15, 0), (14, 5)],
  [(11, 3), (4, 1), (2, 0), (1, 0), (23, 8), (11, 4), (8, 0), (7, 0), (27, 5), (14, 1), (11, 6), (10, 2), (28, 8), (15, 1), (12, 0), (11, 5)],
  [(10, 3), (3, 1), (1, 1), (0, 0), (22, 8), (10, 4), (7, 1), (6, 0), (26, 8), (13, 1), (10, 5), (9, 0), (27, 6), (14, 2), (11, 2), (10, 6)],
  [(40, 6), (27, 7), (23, 1), (22, 1), (49, 0), (40, 3), (38, 0), (37, 0), (50, 0), (43, 8), (40, 4), (39, 0), (51, 0), (44, 8), (41, 0), (40, 5)],
  [(27, 8), (14, 11), (11, 7), (10, 7), (40, 0), (27, 9), (23, 0), (22, 0), (43, 7), (31, 11), (27, 10), (26, 9), (44, 7), (32, 11), (28, 9), (27, 11)],
  [(23, 4), (11, 8), (8, 1), (7, 2), (38, 1), (23, 3), (20, 0), (19, 0), (40, 1), (27, 12), (23, 6), (22, 2), (41, 1), (28, 10), (24, 0), (23, 5)],
  [(22, 4), (10, 8), (7, 3), (6, 1), (37, 1), (22, 3), (19, 1), (18, 0), (39, 1), (26, 10), (22, 5), (21, 0), (40, 2), (27, 13), (23, 2), (22, 6)],
  [(43, 6), (31, 1), (27, 14), (26, 1), (50, 1), (43, 4), (40, 8), (39, 2), (52, 0), (46, 0), (43, 3), (42, 0), (53, 0), (47, 0), (44, 10), (43, 5)],
  [(31, 4), (16, 1), (14, 8), (13, 2), (43, 1), (31, 6), (27, 15), (26, 2), (46, 1), (34, 0), (31, 3), (30, 0), (47, 1), (35, 0), (32, 10), (31, 5)],
  [(27, 16), (14, 7), (11, 11), (10, 9), (40, 7), (27, 17), (23, 11), (22, 9), (43, 0), (31, 0), (27, 18), (26, 0), (44, 9), (32, 9), (28, 11), (27, 19)],
  [(26, 4), (13, 3), (10, 10), (9, 1), (39, 3), (26, 5), (22, 10), (21, 1), (42, 1), (30, 1), (26, 3), (25, 0), (43, 2), (31, 2), (27, 20), (26, 6)],
  [(44, 6), (32, 1), (28, 1), (27, 21), (51, 1), (44, 4), (41, 2), (40, 10), (53, 1), (47, 2), (44, 5), (43, 10), (54, 0), (48, 0), (45, 0), (44, 3)],
  [(32, 4), (17, 1), (15, 2), (14, 10), (44, 1), (32, 6), (28, 2), (27, 22), (47, 3), (35, 1), (32, 5), (31, 10), (48, 1), (36, 0), (33, 0), (32, 3)],
  [(28, 4), (15, 3), (12, 1), (11, 10), (41, 3), (28, 5), (24, 1), (23, 10), (44, 2), (32, 2), (28, 6), (27, 23), (45, 1), (33, 1), (29, 0), (28, 3)],
  [(27, 24), (14, 9), (11, 9), (10, 11), (40, 9), (27, 25), (23, 9), (22, 11), (43, 9), (31, 9), (27, 26), (26, 11), (44, 0), (32, 0), (28, 0), (27, 27)]
]

def lookupBlkPos (i : Nat) : Nat × Nat :=
  (idxToBlkPos16x16.getD (i / 16) []).getD (i % 16) (0, 0)

/-- Approximate integer lower-triangular Cholesky factors on the 6 representative blocks of `zScaled`. -/
def zCholReps6 : List (List (List Int)) := [
  [[1833]],
  [[1833], [956, 1564]],
  [[1833], [1785, 417]],
  [[2021], [-358, 1989], [394, 1316, 1482], [1226, 621, -1365, 578]],
  [[1784], [-621, 1746], [-621, -594, 1642], [220, 933, 1330, 2797], [-27, -528, -312, -581, 1913], [-27, -114, -603, -581, -155, 1907], [-647, -708, -1009, 392, -193, -210, 680], [-333, 77, -375, -842, 1064, -218, -543, 1227], [-736, 2116, 1508, 1556, 229, -399, 1084, -1621, 1165], [-333, -379, -55, -842, -304, 1043, -543, -564, -755, 785], [-736, 698, 2503, 1556, -416, 196, 1084, 29, 1574, -998, 714], [-1069, 319, 454, 1662, -757, -821, 1203, -536, 819, -435, 161, 408]],
  [[3275], [-820, 1859], [-820, -264, 1840], [-820, -264, -305, 1815], [1029, -1635, 130, 154, 3692], [1029, 362, -1600, 154, 552, 3651], [1029, 362, 417, -1552, 552, 475, 3620], [3004, -8, -195, -230, 1559, 116, 102, 2416], [-1083, 940, -334, -395, 75, -51, -45, -367, 1288], [881, -1519, 121, 143, 1736, 504, 442, -846, -468, 1791], [-30, 0, -148, -98, -746, -755, 199, 454, 197, -315, 1608], [-30, 0, -73, -162, -746, 99, -774, 454, 197, -315, -322, 1575], [911, 163, -1189, 241, 1109, 2856, 243, -1107, 21, -824, -518, 390, 1819], [911, 163, 435, -1132, 1109, 612, 2800, -1107, 21, -824, 486, -429, -1588, 887], [3004, -192, -35, -230, 348, 1524, 102, 1721, 807, 279, 96, -365, -273, -112, 1384], [911, -1200, -8, 241, 2989, 669, 243, -1162, -946, 67, 618, 338, 982, 87, 297, 1352], [-1083, -464, 883, -395, -39, 82, -45, 169, -603, 4, 105, -86, -276, 40, -581, 342, 923], [-30, -146, -21, -98, -858, -625, 199, 417, 216, -867, 601, -463, 271, -40, 210, -641, 504, 773], [881, 336, -1486, 143, 758, 1642, 442, -552, -44, -26, -1093, 309, 124, 91, -570, -458, -247, -134, 1382], [-30, -72, -10, -162, -14, -753, -774, 103, -136, 341, -205, -501, 46, -133, 557, 448, 166, 90, -338, 1346], [911, 408, 223, -1132, 771, 1005, 2800, -655, 92, -368, 277, -140, -520, 380, -1227, -986, 28, 15, -1217, -74, 765], [3004, -192, -221, -73, 348, 299, 1498, 1721, 807, 279, -376, 21, 184, -230, 387, 824, 701, -171, -9, 39, -131, 740], [911, -1200, 239, 32, 2989, 328, 632, -1162, -946, 67, 207, 673, -815, 555, 888, 201, 239, 680, -9, 39, -131, -227, 705], [911, 408, -1154, 32, 771, 2907, 632, -655, 92, -368, -193, 243, 640, 78, -984, -791, -770, -418, -263, 1119, 564, -227, -312, 632], [-1083, -464, -536, 806, -39, -34, 87, 169, -603, 4, -106, 86, 260, -99, 509, -279, -808, 0, 8, -1, -39, -283, 26, 42, 483], [-30, -146, -94, -37, -858, 116, -645, 417, 216, -867, -574, 496, -256, 98, -163, 557, -440, -677, 8, -1, -39, 112, -262, 42, 86, 475], [-30, -72, -158, -37, -14, -866, -645, 103, -136, 341, -450, -301, -105, -94, 535, 430, 200, 108, -1273, 83, 74, 112, 153, -216, 86, 72, 469], [881, 336, 387, -1442, 758, 652, 1570, -552, -44, -26, 522, -1009, -64, 140, -550, -442, -130, -71, 328, -1250, 9, -108, -149, -239, -46, -38, -33, 487]]
]

/-- Approximate integer lower-triangular Cholesky factors on the 6 representative blocks of `zdScaled`. -/
def zdCholReps6 : List (List (List Int)) := [
  [[5949]],
  [[8864], [-4871, 7405]],
  [[6830], [-1648, 6628]],
  [[8909], [91, 8909], [3673, -4975, 6414], [-4937, 3724, 5842, 2646]],
  [[10863], [806, 9002], [806, 184, 9000], [-11025, -4418, -4328, 10589], [2853, 1187, 1073, -228, 8267], [2853, 1097, 1164, -228, -1335, 8158], [3659, 1281, 1255, -3870, -279, -328, 8648], [-263, 4375, 651, -821, -3689, 1091, 1846, 5618], [-9903, -10756, -5651, 2116, 4455, 1177, -4321, 4815, 3623], [-263, 740, 4361, -821, 1672, -3464, 1846, -1706, -606, 5318], [-9903, -5870, -10639, 2116, 442, 4587, -4321, -1853, 1129, 4621, 3201], [-10167, -5130, -5027, 1806, 1966, 2314, -3689, -3559, 523, -4842, -18, 2640]],
  [[8463], [-618, 7792], [-618, -1201, 7699], [-618, -1201, -1403, 7570], [-6766, -2789, 2710, 3258, 14954], [-6766, 3107, -2338, 3258, -4859, 14142], [-6766, 3107, 3630, -1705, -4859, -6808, 12396], [9289, 2268, -2440, -2933, -7616, -5074, -8576, 5643], [-2748, -2147, 761, 914, -1183, 268, 453, 2414, 6325], [-1162, -3077, 405, 487, 3978, 214, 362, -458, -1611, 6450], [890, 1371, -2052, -1238, -522, -2268, 431, -604, 57, 570, 6811], [890, 1371, -843, -2243, -522, 1469, -1781, -604, 57, 570, -1912, 6537], [-2052, 2746, -3702, 1724, -6434, 10287, -68, -3510, 4430, -3347, -795, 1013, 8641], [-2052, 2746, 2370, -3326, -6434, -5012, 8984, -3510, 4430, -3347, 1195, -479, -6880, 5227], [9289, -2760, 1865, -2933, -2324, -8851, -8576, -1206, -513, -236, 32, 420, 1916, 1377, 4932], [-2052, -4081, 2143, 1724, 11820, -2742, -68, 3492, -6091, 1138, 4063, 842, -4349, -2900, -1339, 4747], [-2748, 1082, -2005, 914, 638, -1032, 453, -1091, -3015, 30, 794, -565, -2230, 637, 2914, -367, 4539], [890, -2239, 1038, -1238, -1975, -1231, 431, 139, 881, -3021, -2116, 1494, 1058, -324, -1144, 2705, 2471, 3807], [-1162, 874, -2978, 487, -1090, 3832, 362, -26, 888, -422, -3053, -806, 985, 14, -757, -1000, -582, -316, 5521], [890, -1044, 1225, -2243, 1559, -16, -1781, 575, -964, -139, 1840, -3011, 725, -590, -530, -701, -717, -390, 1000, 5480], [-2052, 1919, 3079, -3326, -2649, -7714, 8984, -601, 1851, -283, 148, -1573, -3863, 1993, -2907, -3841, 4551, 2472, -5169, 232, 4172], [9289, -2760, -3224, 1299, -2324, -3256, -11887, -1206, -513, -236, 394, 149, -692, 2256, -2116, -645, -1386, 2095, -43, 145, 1225, 3406], [-2052, -4081, 1305, 2421, 11820, 1260, -2436, 3492, -6091, 1138, -333, 4136, 1709, -4940, -46, -2212, 1002, -2303, -43, 145, 1225, -1011, 3253], [-2052, 1919, -3831, 2421, -2649, 11588, -2436, -601, 1851, -283, -1551, -299, 4282, -750, 2609, 3447, -4499, -2443, 1200, 4522, -3978, -1011, -1372, 2949], [-2748, 1082, 1264, -1804, 638, 894, -686, -1091, -3015, 30, -765, 603, 2161, -842, -2478, 402, -4036, -218, 65, 131, -126, 1289, 35, 55, 2210], [890, -2239, -1406, 795, -1975, 970, -871, 139, 881, -3021, 2028, -1611, -1038, 382, 1060, -2275, -2381, -3267, 65, 131, -126, -349, 1241, 55, 213, 2200], [890, -1044, -2429, 795, 1559, -1553, -871, 575, -964, -139, -3407, 921, -934, -31, 508, 671, 785, 426, -4935, -245, 81, -349, -474, 1149, 213, 194, 2191], [-1162, 874, 1021, -2840, -1090, -1527, 3533, -26, 888, -422, 83, -3156, -776, 607, 436, 576, 703, 382, -942, -4865, 46, -485, -659, -1033, 316, 287, 263, 2188]]
]

/-- The 15 canonical row indices of `rowCanonTable`. -/
def canonRows15 : List Nat := [0, 1, 4, 5, 6, 16, 17, 18, 20, 21, 22, 24, 25, 26, 27]

/-- Entry `(i, j)` of the block-lower-triangular Cholesky matrix defined by `reps`. -/
def cholEntry (reps : List (List (List Int))) (i j : Nat) : Int :=
  let bp_i := lookupBlkPos i
  let bp_j := lookupBlkPos j
  if bp_i.1 != bp_j.1 then 0
  else if bp_i.2 < bp_j.2 then 0
  else
    let repId := blockRepId55.getD bp_i.1 0
    ((reps.getD repId []).getD bp_i.2 []).getD bp_j.2 0

/-- Block-local inner product `∑_{t ≤ min(r_i, r_j)} L_{rep}[r_i][t] * L_{rep}[r_j][t]`. -/
def cholRowDot (reps : List (List (List Int))) (repId ri rj : Nat) : Int :=
  let rep := reps.getD repId []
  let rowi := rep.getD ri []
  let rowj := rep.getD rj []
  sumBelow (Nat.min ri rj + 1) fun t => rowi.getD t 0 * rowj.getD t 0

def checkPartOk : Bool :=
  (List.range 256).all fun i =>
    let bp := lookupBlkPos i
    let blk := blocks55.getD bp.1 []
    bp.1 < 55 && bp.2 < blk.length && blk.getD bp.2 999 == i &&
      chargeVec i == chargeVec (blk.getD 0 0)

def checkBlkItemsOk : Bool :=
  (List.range 55).all fun b =>
    let blk := blocks55.getD b []
    blockRepId55.getD b 99 < 6 &&
    (List.range blk.length).all fun t =>
      let idx := blk.getD t 999
      idx < 256 && lookupBlkPos idx == (b, t)

def checkDistinctChargesOk : Bool :=
  (List.range 55).all fun b1 =>
    (List.range 55).all fun b2 =>
      if b1 == b2 then true
      else chargeVec ((blocks55.getD b1 []).getD 0 0) != chargeVec ((blocks55.getD b2 []).getD 0 0)

def checkCanonRowOk : Bool :=
  let rowsOk := (List.range 256).all fun i =>
    let r := (rowCanonTable.getD (i / 16) []).getD (i % 16) 0
    let p := (rowPermTable.getD (i / 16) []).getD (i % 16) 0
    let pRow := permPairTable.getD p []
    r < 15 && p < 24 && pRow.getD (i / 16) 0 * 16 + pRow.getD (i % 16) 0 == canonRows15.getD r 999
  let selfOk := (List.range 15).all fun r =>
    let ci := canonRows15.getD r 999
    ci < 256 && (rowCanonTable.getD (ci / 16) []).getD (ci % 16) 99 == r &&
      (rowPermTable.getD (ci / 16) []).getD (ci % 16) 99 == 0
  let idPermOk := (List.range 16).all fun ab => (permPairTable.getD 0 []).getD ab 999 == ab
  rowsOk && selfOk && idPermOk

def checkPermPairOk : Bool :=
  (List.range 24).all fun p =>
    let perm := perms24.getD p []
    let pRow := permPairTable.getD p []
    (List.range 4).all (fun a =>
      applyPerm perm a < 4 && invPerm perm (applyPerm perm a) == a &&
      applyPerm perm (invPerm perm a) == a) &&
    (List.range 4).all fun a =>
      (List.range 4).all fun b =>
        pRow.getD (a * 4 + b) 999 == applyPerm perm a * 4 + applyPerm perm b

def checkOrbitChargeOk : Bool :=
  (List.range 15).all fun r =>
    let ci := canonRows15.getD r 0
    let ch_i := chargeVec ci
    (List.range 256).all fun jp =>
      let oid := ((canonOrbitTable.getD r []).getD (jp / 16) []).getD (jp % 16) 0
      if oid == 0 then true else ch_i == chargeVec jp

def checkJLambdaPermOk : Bool :=
  (List.range 24).all fun p =>
    let pRow := permPairTable.getD p []
    (List.range 16).all fun ab =>
      (List.range 16).all fun ce =>
        jLambdaScaled5 (pRow.getD ab 0) (pRow.getD ce 0) == jLambdaScaled5 ab ce

def checkSubmatOk : Bool :=
  (List.range 55).all fun b =>
    let blk := blocks55.getD b []
    let repId := blockRepId55.getD b 0
    let repBlk := blocks55.getD (repBlockIdx6.getD repId 0) []
    blk.length == repBlk.length &&
    (List.range blk.length).all fun r =>
      (List.range blk.length).all fun c =>
        let i := blk.getD r 0; let j := blk.getD c 0
        let ri := repBlk.getD r 0; let rj := repBlk.getD c 0
        zScaled i j == zScaled ri rj && deltaScaled4200 i j == deltaScaled4200 ri rj

def checkBlocksAndSymmetry : Bool :=
  checkPartOk && checkBlkItemsOk && checkDistinctChargesOk && checkCanonRowOk &&
    checkPermPairOk && checkOrbitChargeOk && checkJLambdaPermOk && checkSubmatOk

theorem blocks_and_symmetry_ok : checkBlocksAndSymmetry = true := by decide

/-- Check on ONLY the 6 representative blocks (`953` pairs total) that `M_int - L Lᵀ`
is symmetric and diagonally dominant. -/
def checkRep6CholGershgorin (M_int : Nat → Nat → Int) (reps : List (List (List Int))) : Bool :=
  (List.range 6).all fun repId =>
    let blk := blocks55.getD (repBlockIdx6.getD repId 0) []
    let n := blk.length
    (List.range n).all fun r =>
      let i := blk.getD r 0
      let diagRem := M_int i i - cholRowDot reps repId r r
      let symOk := (List.range n).all fun c =>
        let j := blk.getD c 0
        M_int i j - cholRowDot reps repId r c == M_int j i - cholRowDot reps repId c r
      let offSum := sumBelow n fun c =>
        if c == r then 0
        else
          let j := blk.getD c 0
          ((M_int i j - cholRowDot reps repId r c).natAbs : Int)
      symOk && decide (offSum ≤ diagRem)

theorem z_rep6_chol_gershgorin : checkRep6CholGershgorin zScaled zCholReps6 = true := by decide

theorem zd_rep6_chol_gershgorin : checkRep6CholGershgorin zdScaled zdCholReps6 = true := by decide

/-- Check `deltaScaled4200 = w0Scaled4200 - w1Scaled4200` on all 15 canonical rows. -/
def checkCanon15DeltaEq : Bool :=
  (List.range 15).all fun r =>
    let ci := canonRows15.getD r 0
    (List.range 256).all fun jp =>
      deltaScaled4200 ci jp == w0Scaled4200 ci jp - w1Scaled4200 ci jp

theorem canon15_delta_eq_ok : checkCanon15DeltaEq = true := by decide

/-- Check both causal partial-trace identities of `zScaled` for all `ai ∈ {0, 1, 2, 3}`. -/
def checkZCausalAllAi : Bool :=
  let c1 := (List.range 4).all fun ai =>
    (List.range 4).all fun ao =>
      (List.range 4).all fun ai' =>
        (List.range 4).all fun ao' =>
          let trBIBO := sumBelow 16 fun xbo =>
            zScaled (encode4 ai ao (xbo / 4) (xbo % 4)) (encode4 ai' ao' (xbo / 4) (xbo % 4))
          (List.range 4).all fun bi =>
            (List.range 4).all fun bi' =>
              let lhs := 4 * sumBelow 4 fun bo =>
                zScaled (encode4 ai ao bi bo) (encode4 ai' ao' bi' bo)
              lhs == (if bi == bi' then trBIBO else 0)
  let c2 := (List.range 4).all fun ai =>
    (List.range 4).all fun ai' =>
      let lhs := sumBelow 64 fun idx =>
        zScaled (encode4 ai (idx / 16 % 4) (idx / 4 % 4) (idx % 4))
          (encode4 ai' (idx / 16 % 4) (idx / 4 % 4) (idx % 4))
      lhs == (if ai == ai' then 409600000 else 0)
  c1 && c2

theorem all_z_causal_traces_ok : checkZCausalAllAi = true := by decide

/-! ### Section 1b: Complex dual matrices, `W_0 - W_1 = Δ`, and PSD proofs -/

noncomputable section

/-- Exact dual certificate matrix `Z` on `Wires4`. -/
def zMatrix : CMatrix Wires4 :=
  fun u v => (zScaled (wires4ToFin256 u).val (wires4ToFin256 v).val : ℂ) / 640000000

/-- Exact two-copy Haar dephasing Choi matrix `W_0` on `Wires4`. -/
def w0Matrix : CMatrix Wires4 :=
  fun u v => (w0Scaled4200 (wires4ToFin256 u).val (wires4ToFin256 v).val : ℂ) / 4200

/-- Exact two-copy model Choi matrix `W_1 = J(Λ)^⊗2` on `Wires4`. -/
def w1Matrix : CMatrix Wires4 :=
  fun u v => (w1Scaled4200 (wires4ToFin256 u).val (wires4ToFin256 v).val : ℂ) / 4200

/-- Exact two-copy Choi difference `Δ = W_0 - W_1` on `Wires4`. -/
def deltaMatrix : CMatrix Wires4 :=
  fun u v => (deltaScaled4200 (wires4ToFin256 u).val (wires4ToFin256 v).val : ℂ) / 4200

private theorem part_ok : checkPartOk = true := by
  have h := blocks_and_symmetry_ok
  unfold checkBlocksAndSymmetry at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1

private theorem blk_items_ok : checkBlkItemsOk = true := by
  have h := blocks_and_symmetry_ok
  unfold checkBlocksAndSymmetry at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

private theorem distinct_charges_ok : checkDistinctChargesOk = true := by
  have h := blocks_and_symmetry_ok
  unfold checkBlocksAndSymmetry at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.2

private theorem canon_row_ok : checkCanonRowOk = true := by
  have h := blocks_and_symmetry_ok
  unfold checkBlocksAndSymmetry at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.2

private theorem perm_pair_ok : checkPermPairOk = true := by
  have h := blocks_and_symmetry_ok
  unfold checkBlocksAndSymmetry at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

private theorem orbit_charge_ok : checkOrbitChargeOk = true := by
  have h := blocks_and_symmetry_ok
  unfold checkBlocksAndSymmetry at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

private theorem jlambda_perm_ok : checkJLambdaPermOk = true := by
  have h := blocks_and_symmetry_ok
  unfold checkBlocksAndSymmetry at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

private theorem submat_ok : checkSubmatOk = true := by
  have h := blocks_and_symmetry_ok
  unfold checkBlocksAndSymmetry at h
  simp only [Bool.and_eq_true] at h
  exact h.2

private theorem getD_eq_of_ne {α : Type*} (l : List α) (n : Nat) (d₁ d₂ : α)
    (hne : l.getD n d₁ ≠ d₁) : l.getD n d₂ = l.getD n d₁ := by
  simp only [List.getD] at hne ⊢
  cases h : l[n]? with
  | none => simp [h] at hne
  | some _ => rfl

private theorem permPair_lt_16 {p ab : Nat} (hp : p < 24) (hab : ab < 16) :
    (permPairTable.getD p []).getD ab 0 < 16 ∧
      (permPairTable.getD p []).getD ab 0 =
        applyPerm (perms24.getD p []) (ab / 4) * 4 + applyPerm (perms24.getD p []) (ab % 4) := by
  have hp0 := of_range_all perm_pair_ok hp
  simp only [Bool.and_eq_true] at hp0
  have ha : ab / 4 < 4 := by omega
  have hb : ab % 4 < 4 := by omega
  have ha_lt : applyPerm (perms24.getD p []) (ab / 4) < 4 := by
    have h1 := of_range_all hp0.1 ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1
  have hb_lt : applyPerm (perms24.getD p []) (ab % 4) < 4 := by
    have h1 := of_range_all hp0.1 hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1
  have hp2 := of_range_all (of_range_all hp0.2 ha) hb
  simp only [beq_iff_eq] at hp2
  have hab_eq : ab / 4 * 4 + ab % 4 = ab := by omega
  rw [hab_eq] at hp2
  have h999 : (permPairTable.getD p []).getD ab 0 = (permPairTable.getD p []).getD ab 999 :=
    getD_eq_of_ne _ _ 999 0 (by omega)
  rw [h999, hp2]
  exact ⟨by omega, rfl⟩

private theorem applyPerm_inj {p x y : Nat} (hp : p < 24) (hx : x < 4) (hy : y < 4) :
    applyPerm (perms24.getD p []) x = applyPerm (perms24.getD p []) y ↔ x = y := by
  constructor
  · intro heq
    have hp0 := of_range_all perm_pair_ok hp
    simp only [Bool.and_eq_true] at hp0
    have hx0 := of_range_all hp0.1 hx
    have hy0 := of_range_all hp0.1 hy
    simp only [Bool.and_eq_true, beq_iff_eq] at hx0 hy0
    calc
      x = invPerm (perms24.getD p []) (applyPerm (perms24.getD p []) x) := hx0.1.2.symm
      _ = invPerm (perms24.getD p []) (applyPerm (perms24.getD p []) y) := by rw [heq]
      _ = y := hy0.1.2
  · intro h; subst h; rfl

private theorem w0Scaled4200_no_sum_guard (i j : Nat) :
    w0Scaled4200 i j =
      let ai := i / 64 % 4; let ao := i / 16 % 4; let bi := i / 4 % 4; let bo := i % 4
      let ai' := j / 64 % 4; let ao' := j / 16 % 4; let bi' := j / 4 % 4; let bo' := j % 4
      let col := [ai, ao', bi, bo']
      5 * (perms24.map fun q =>
        if ai' == col.getD (applyPerm q 0) 0 &&
           ao == col.getD (applyPerm q 1) 0 &&
           bi' == col.getD (applyPerm q 2) 0 &&
           bo == col.getD (applyPerm q 3) 0 then
          weingartenNum13440 q
        else 0).sum := by
  unfold w0Scaled4200
  dsimp only
  by_cases hsum : (j / 64 % 4 + i / 16 % 4 + j / 4 % 4 + i % 4 !=
      i / 64 % 4 + j / 16 % 4 + i / 4 % 4 + j % 4) = true
  · rw [if_pos hsum]
    suffices hzero : ∀ q ∈ perms24,
        (if (j / 64 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 0) 0 &&
             i / 16 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 1) 0 &&
             j / 4 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 2) 0 &&
             i % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 3) 0) = true
         then weingartenNum13440 q else 0) = 0 by
      have hmap : (perms24.map fun q =>
          if (j / 64 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 0) 0 &&
              i / 16 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 1) 0 &&
              j / 4 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 2) 0 &&
              i % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 3) 0)
          then weingartenNum13440 q else 0).sum = 0 := by
        refine List.sum_eq_zero ?_
        intro x hx
        rcases List.mem_map.mp hx with ⟨q, hq, rfl⟩
        exact hzero q hq
      rw [hmap]
      simp
    intro q hq
    by_cases hcond :
        (j / 64 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 0) 0 &&
         i / 16 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 1) 0 &&
         j / 4 % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 2) 0 &&
         i % 4 == [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD (applyPerm q 3) 0) = true
    · exfalso
      simp only [bne_iff_ne] at hsum
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rcases hcond with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
      have g0 (a b c d : Nat) : [a, b, c, d].getD 0 0 = a := rfl
      have g1 (a b c d : Nat) : [a, b, c, d].getD 1 0 = b := rfl
      have g2 (a b c d : Nat) : [a, b, c, d].getD 2 0 = c := rfl
      have g3 (a b c d : Nat) : [a, b, c, d].getD 3 0 = d := rfl
      unfold perms24 at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [applyPerm, g0, g1, g2, g3] at h0 h1 h2 h3; omega)
    · rw [if_neg hcond]
  · rw [if_neg hsum]

private theorem deltaScaled4200_eq_sub_all {i j : Nat} (hi : i < 256) (hj : j < 256) :
    deltaScaled4200 i j = w0Scaled4200 i j - w1Scaled4200 i j := by
  have hcr := canon_row_ok
  unfold checkCanonRowOk at hcr
  simp only [Bool.and_eq_true] at hcr
  rcases hcr with ⟨⟨hrows, hself⟩, hidPerm⟩
  have hri := of_range_all hrows hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hri
  rcases hri with ⟨⟨hr_lt, hp_lt⟩, hci_eq⟩
  let r := (rowCanonTable.getD (i / 16) []).getD (i % 16) 0
  let p := (rowPermTable.getD (i / 16) []).getD (i % 16) 0
  let pRow := permPairTable.getD p []
  have hself_r := of_range_all hself hr_lt
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hself_r
  rcases hself_r with ⟨⟨hci_lt, hci_r⟩, hci_p⟩
  have hci_lt_r : canonRows15.getD r 999 < 256 := hci_lt
  have hci_999 : canonRows15.getD r 0 = canonRows15.getD r 999 :=
    getD_eq_of_ne _ _ 999 0 (by omega)
  let ci := canonRows15.getD r 0
  have hci_lt' : ci < 256 := by dsimp [ci]; rw [hci_999]; exact hci_lt
  have hci_eq' : pRow.getD (i / 16) 0 * 16 + pRow.getD (i % 16) 0 = ci := by
    dsimp [ci, pRow, p, r]; rw [hci_999]; exact hci_eq
  have hi_hi := permPair_lt_16 hp_lt (show i / 16 < 16 by omega)
  have hi_lo := permPair_lt_16 hp_lt (show i % 16 < 16 by omega)
  have hj_hi := permPair_lt_16 hp_lt (show j / 16 < 16 by omega)
  have hj_lo := permPair_lt_16 hp_lt (show j % 16 < 16 by omega)
  let jp := pRow.getD (j / 16) 0 * 16 + pRow.getD (j % 16) 0
  have hjp_lt : jp < 256 := by
    have h1 : pRow.getD (j / 16) 0 < 16 := hj_hi.1
    have h2 : pRow.getD (j % 16) 0 < 16 := hj_lo.1
    dsimp [jp]; omega
  have hcanon_eq := of_range_all (of_range_all canon15_delta_eq_ok hr_lt) hjp_lt
  simp only [beq_iff_eq] at hcanon_eq
  have hjp_div : jp / 16 = pRow.getD (j / 16) 0 := by
    have h2 : pRow.getD (j % 16) 0 < 16 := hj_lo.1
    dsimp [jp]; omega
  have hjp_mod : jp % 16 = pRow.getD (j % 16) 0 := by
    have h2 : pRow.getD (j % 16) 0 < 16 := hj_lo.1
    dsimp [jp]; omega
  have hci_r0 : (rowCanonTable.getD (ci / 16) []).getD (ci % 16) 0 = r := by
    have hc : (rowCanonTable.getD (ci / 16) []).getD (ci % 16) 99 = r := by
      dsimp [ci]; rw [hci_999]; exact hci_r
    exact (getD_eq_of_ne _ _ 99 0 (by omega)).trans hc
  have hci_p0 : (rowPermTable.getD (ci / 16) []).getD (ci % 16) 0 = 0 := by
    have hc : (rowPermTable.getD (ci / 16) []).getD (ci % 16) 99 = 0 := by
      dsimp [ci]; rw [hci_999]; exact hci_p
    exact (getD_eq_of_ne _ _ 99 0 (by omega)).trans hc
  have hid_div : (permPairTable.getD 0 []).getD (jp / 16) 0 = jp / 16 := by
    have h0 := of_range_all hidPerm (show jp / 16 < 16 by omega)
    simp only [beq_iff_eq] at h0
    exact (getD_eq_of_ne _ _ 999 0 (by omega)).trans h0
  have hid_mod : (permPairTable.getD 0 []).getD (jp % 16) 0 = jp % 16 := by
    have h0 := of_range_all hidPerm (show jp % 16 < 16 by omega)
    simp only [beq_iff_eq] at h0
    exact (getD_eq_of_ne _ _ 999 0 (by omega)).trans h0
  have horb : orbitId ci jp = orbitId i j := by
    unfold orbitId
    dsimp only
    rw [hci_r0, hci_p0, hid_div, hid_mod, hjp_div, hjp_mod]
  have hdelta : deltaScaled4200 ci jp = deltaScaled4200 i j := by
    unfold deltaScaled4200; rw [horb]
  have hw1 : w1Scaled4200 ci jp = w1Scaled4200 i j := by
    unfold w1Scaled4200
    have hci_div : ci / 16 = pRow.getD (i / 16) 0 := by
      have h2 : pRow.getD (i % 16) 0 < 16 := hi_lo.1
      omega
    have hci_mod : ci % 16 = pRow.getD (i % 16) 0 := by
      have h2 : pRow.getD (i % 16) 0 < 16 := hi_lo.1
      omega
    rw [hci_div, hci_mod, hjp_div, hjp_mod]
    have hj1 := of_range_all (of_range_all (of_range_all jlambda_perm_ok hp_lt)
      (show i / 16 < 16 by omega)) (show j / 16 < 16 by omega)
    have hj2 := of_range_all (of_range_all (of_range_all jlambda_perm_ok hp_lt)
      (show i % 16 < 16 by omega)) (show j % 16 < 16 by omega)
    simp only [beq_iff_eq] at hj1 hj2
    dsimp only [pRow, p]
    rw [hj1, hj2]
  have hw0 : w0Scaled4200 ci jp = w0Scaled4200 i j := by
    rw [w0Scaled4200_no_sum_guard ci jp, w0Scaled4200_no_sum_guard i j]
    dsimp only
    let perm := perms24.getD p []
    have hp0 := of_range_all perm_pair_ok hp_lt
    simp only [Bool.and_eq_true] at hp0
    have perm_lt {x : Nat} (hx : x < 4) : applyPerm perm x < 4 := by
      have h1 := of_range_all hp0.1 hx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1.1.1
    have hci_w : ci / 64 % 4 = applyPerm perm (i / 64 % 4) ∧
        ci / 16 % 4 = applyPerm perm (i / 16 % 4) ∧
        ci / 4 % 4 = applyPerm perm (i / 4 % 4) ∧
        ci % 4 = applyPerm perm (i % 4) := by
      have h1 : pRow.getD (i / 16) 0 =
          applyPerm perm (i / 16 / 4) * 4 + applyPerm perm (i / 16 % 4) := hi_hi.2
      have h2 : pRow.getD (i % 16) 0 =
          applyPerm perm (i % 16 / 4) * 4 + applyPerm perm (i % 16 % 4) := hi_lo.2
      have hb0 := perm_lt (show i / 64 % 4 < 4 by omega)
      have hb1 := perm_lt (show i / 16 % 4 < 4 by omega)
      have hb2 := perm_lt (show i / 4 % 4 < 4 by omega)
      have hb3 := perm_lt (show i % 4 < 4 by omega)
      have hd1 : i / 16 / 4 = i / 64 % 4 := by omega
      have hd2 : i % 16 / 4 = i / 4 % 4 := by omega
      have hd3 : i % 16 % 4 = i % 4 := by omega
      rw [hd1] at h1; rw [hd2, hd3] at h2
      omega
    have hjp_w : jp / 64 % 4 = applyPerm perm (j / 64 % 4) ∧
        jp / 16 % 4 = applyPerm perm (j / 16 % 4) ∧
        jp / 4 % 4 = applyPerm perm (j / 4 % 4) ∧
        jp % 4 = applyPerm perm (j % 4) := by
      have h1 : pRow.getD (j / 16) 0 =
          applyPerm perm (j / 16 / 4) * 4 + applyPerm perm (j / 16 % 4) := hj_hi.2
      have h2 : pRow.getD (j % 16) 0 =
          applyPerm perm (j % 16 / 4) * 4 + applyPerm perm (j % 16 % 4) := hj_lo.2
      have hb0 := perm_lt (show j / 64 % 4 < 4 by omega)
      have hb1 := perm_lt (show j / 16 % 4 < 4 by omega)
      have hb2 := perm_lt (show j / 4 % 4 < 4 by omega)
      have hb3 := perm_lt (show j % 4 < 4 by omega)
      have hd1 : j / 16 / 4 = j / 64 % 4 := by omega
      have hd2 : j % 16 / 4 = j / 4 % 4 := by omega
      have hd3 : j % 16 % 4 = j % 4 := by omega
      rw [hd1] at h1; rw [hd2, hd3] at h2
      dsimp [jp]
      omega
    rw [hci_w.1, hci_w.2.1, hci_w.2.2.1, hci_w.2.2.2,
        hjp_w.1, hjp_w.2.1, hjp_w.2.2.1, hjp_w.2.2.2]
    congr 2
    refine List.map_congr_left fun q hq => ?_
    have hq_vals : ∀ t < 4, applyPerm q t < 4 := by
      intro t ht
      unfold perms24 at hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (interval_cases t <;> decide)
    have col_eq (k : Nat) (hk : k < 4) :
        [applyPerm perm (i / 64 % 4), applyPerm perm (j / 16 % 4),
         applyPerm perm (i / 4 % 4), applyPerm perm (j % 4)].getD k 0 =
        applyPerm perm ([i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD k 0) ∧
        [i / 64 % 4, j / 16 % 4, i / 4 % 4, j % 4].getD k 0 < 4 := by
      interval_cases k <;> simp [List.getD] <;> omega
    have eq_beq {x y : Nat} (hx : x < 4) (hy : y < 4) :
        (applyPerm perm x == applyPerm perm y) = (x == y) := by
      by_cases hxy : x = y
      · subst hxy; simp
      · have hne : applyPerm perm x ≠ applyPerm perm y :=
          mt (applyPerm_inj hp_lt hx hy).mp hxy
        simp [hxy, hne]
    rcases col_eq (applyPerm q 0) (hq_vals 0 (by omega)) with ⟨hc0, hlt0⟩
    rcases col_eq (applyPerm q 1) (hq_vals 1 (by omega)) with ⟨hc1, hlt1⟩
    rcases col_eq (applyPerm q 2) (hq_vals 2 (by omega)) with ⟨hc2, hlt2⟩
    rcases col_eq (applyPerm q 3) (hq_vals 3 (by omega)) with ⟨hc3, hlt3⟩
    rw [hc0, hc1, hc2, hc3,
        eq_beq (by omega) hlt0, eq_beq (by omega) hlt1,
        eq_beq (by omega) hlt2, eq_beq (by omega) hlt3]
  linarith

/-- Exact identity `W_0 - W_1 = Δ` on `Wires4`. -/
theorem w0Matrix_sub_w1Matrix_eq_deltaMatrix :
    w0Matrix - w1Matrix = deltaMatrix := by
  ext u v
  simp only [Matrix.sub_apply, w0Matrix, w1Matrix, deltaMatrix]
  have h := deltaScaled4200_eq_sub_all (wires4ToFin256 u).isLt (wires4ToFin256 v).isLt
  rw [h]
  push_cast
  ring

/-- Any real symmetric diagonally dominant matrix is positive semidefinite over `ℂ`
via an explicit sum of rank-one PSD matrices (`rankOneMatrix_pos`). -/
theorem gershgorin_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ)
    (hSym : ∀ i j, R i j = R j i)
    (hDom : ∀ i, (∑ j ∈ Finset.univ.erase i, |R i j|) ≤ R i i) :
    (R.map Complex.ofReal).PosSemidef := by
  let d : ι → ℝ := fun u => R u u - ∑ v ∈ Finset.univ.erase u, |R u v|
  let sgn : ι → ι → ℝ := fun u v => if 0 ≤ R u v then 1 else -1
  let wt : ι → ι → ℝ := fun u v => Real.sqrt (|R u v| / 2)
  let ψDiag : ι → ι → ℂ := fun u k =>
    if k = u then (Real.sqrt (d u) : ℂ) else 0
  let ψPair : ι × ι → ι → ℂ := fun uv k =>
    if k = uv.1 then (wt uv.1 uv.2 : ℂ)
    else if k = uv.2 then ((wt uv.1 uv.2 * sgn uv.1 uv.2 : ℝ) : ℂ)
    else 0
  have hDecomp : R.map Complex.ofReal =
      (∑ u : ι, rankOneMatrix (ψDiag u)) +
      (∑ uv ∈ Finset.univ.offDiag, rankOneMatrix (ψPair uv)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, rankOneMatrix_apply]
    by_cases hij : i = j
    · subst hij
      have hdiag : (∑ u : ι, ψDiag u i * star (ψDiag u i)) = ((d i : ℝ) : ℂ) := by
        rw [Finset.sum_eq_single i]
        · simp only [ψDiag, ↓reduceIte, Complex.star_def, Complex.conj_ofReal]
          norm_cast
          exact Real.mul_self_sqrt (sub_nonneg.mpr (hDom i))
        · intro u _ hui
          simp [ψDiag, hui.symm]
        · intro h; exact absurd (Finset.mem_univ i) h
      have hoff : (∑ uv ∈ Finset.univ.offDiag, ψPair uv i * star (ψPair uv i)) =
          ((∑ v ∈ Finset.univ.erase i, |R i v| : ℝ) : ℂ) := by
        have hterm : ∀ uv ∈ (Finset.univ : Finset ι).offDiag,
            ψPair uv i * star (ψPair uv i) =
              (if i = uv.1 then ((|R i uv.2| / 2 : ℝ) : ℂ) else 0) +
              (if i = uv.2 then ((|R uv.1 i| / 2 : ℝ) : ℂ) else 0) := by
          rintro ⟨u, v⟩ huv
          rcases Finset.mem_offDiag.mp huv with ⟨_, _, huv_ne⟩
          dsimp only
          by_cases h1 : u = i
          · subst h1
            have h2 : u ≠ v := huv_ne
            simp only [ψPair, wt, h2, ↓reduceIte, add_zero, Complex.star_def, Complex.conj_ofReal]
            norm_cast
            exact Real.mul_self_sqrt (by positivity)
          · have hi1 : i ≠ u := Ne.symm h1
            by_cases h2 : v = i
            · subst h2
              simp only [ψPair, hi1, ↓reduceIte, zero_add, Complex.star_def, Complex.conj_ofReal]
              norm_cast
              have hs2 : sgn u v * sgn u v = 1 := by
                dsimp [sgn]; split_ifs <;> norm_num
              calc
                (wt u v * sgn u v) * (wt u v * sgn u v)
                    = (wt u v * wt u v) * (sgn u v * sgn u v) := by ring
                _ = |R u v| / 2 := by
                    rw [hs2, mul_one]
                    dsimp [wt]
                    exact Real.mul_self_sqrt (by positivity)
            · have hi2 : i ≠ v := Ne.symm h2
              simp [ψPair, hi1, hi2]
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
        have hL : (∑ uv ∈ (Finset.univ : Finset ι).offDiag,
            if i = uv.1 then ((|R i uv.2| / 2 : ℝ) : ℂ) else 0) =
            ∑ v ∈ Finset.univ.erase i, ((|R i v| / 2 : ℝ) : ℂ) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun uv _ => uv.2) ?_ ?_ ?_ ?_
          · intro uv huv
            simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at huv
            exact Finset.mem_erase.mpr ⟨huv.2.symm ▸ huv.1.symm, Finset.mem_univ _⟩
          · intro a ha b hb hab
            simp only [Finset.mem_filter] at ha hb
            exact Prod.ext (ha.2.symm.trans hb.2) hab
          · intro v hv
            refine ⟨(i, v), ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
            exact ⟨(Finset.mem_erase.mp hv).1.symm, trivial⟩
          · intro uv huv
            simp
        have hR : (∑ uv ∈ (Finset.univ : Finset ι).offDiag,
            if i = uv.2 then ((|R uv.1 i| / 2 : ℝ) : ℂ) else 0) =
            ∑ u ∈ Finset.univ.erase i, ((|R i u| / 2 : ℝ) : ℂ) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_bij (fun uv _ => uv.1) ?_ ?_ ?_ ?_
          · intro uv huv
            simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and] at huv
            exact Finset.mem_erase.mpr ⟨huv.2 ▸ huv.1, Finset.mem_univ _⟩
          · intro a ha b hb hab
            simp only [Finset.mem_filter] at ha hb
            exact Prod.ext hab (ha.2.symm.trans hb.2)
          · intro u hu
            refine ⟨(u, i), ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
            exact ⟨(Finset.mem_erase.mp hu).1, trivial⟩
          · intro uv huv
            simp [hSym uv.1 i]
        rw [hL, hR, ← Finset.sum_add_distrib]
        push_cast
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
      rw [hdiag, hoff]
      dsimp [d]
      push_cast
      ring
    · have hdiag0 : (∑ u : ι, ψDiag u i * star (ψDiag u j)) = 0 := by
        refine Finset.sum_eq_zero fun u _ => ?_
        by_cases hiu : i = u
        · subst hiu; simp [ψDiag, Ne.symm hij]
        · simp [ψDiag, hiu]
      have hoff_ij : (∑ uv ∈ Finset.univ.offDiag, ψPair uv i * star (ψPair uv j)) =
          ((R i j : ℝ) : ℂ) := by
        have hsub : {(i, j), (j, i)} ⊆ (Finset.univ : Finset ι).offDiag := by
          intro uv huv
          simp only [Finset.mem_insert, Finset.mem_singleton] at huv
          rcases huv with rfl | rfl <;>
            simp [Finset.mem_offDiag, hij, Ne.symm hij]
        rw [← Finset.sum_subset hsub]
        · have hne_pair : (i, j) ≠ (j, i) := fun h => hij (Prod.mk.inj h).1
          rw [Finset.sum_pair hne_pair]
          have hji : j ≠ i := Ne.symm hij
          simp only [ψPair, ↓reduceIte, hij, hji, Complex.star_def, Complex.conj_ofReal]
          norm_cast
          have hs_ij : |R i j| * sgn i j = R i j := by
            dsimp [sgn]
            split_ifs with h0
            · rw [abs_of_nonneg h0, mul_one]
            · rw [abs_of_neg (lt_of_not_ge h0)]; ring
          have hs_ji : |R j i| * sgn j i = R i j := by
            rw [hSym j i]
            dsimp [sgn]
            rw [hSym j i]
            exact hs_ij
          have hw_ij : wt i j * wt i j = |R i j| / 2 := by
            dsimp [wt]; exact Real.mul_self_sqrt (by positivity)
          have hw_ji : wt j i * wt j i = |R j i| / 2 := by
            dsimp [wt]; exact Real.mul_self_sqrt (by positivity)
          calc
            wt i j * (wt i j * sgn i j) + (wt j i * sgn j i) * wt j i
                = (wt i j * wt i j) * sgn i j + (wt j i * wt j i) * sgn j i := by ring
            _ = (|R i j| * sgn i j) / 2 + (|R j i| * sgn j i) / 2 := by
                rw [hw_ij, hw_ji]; ring
            _ = R i j := by rw [hs_ij, hs_ji]; ring
        · rintro ⟨u, v⟩ huv hnot
          rcases Finset.mem_offDiag.mp huv with ⟨_, _, huv_ne⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
          rcases hnot with ⟨hne1, hne2⟩
          by_cases hi1 : u = i
          · subst hi1
            have hj2 : j ≠ v := fun h => hne1 (Prod.ext rfl h.symm)
            simp [ψPair, Ne.symm hij, hj2]
          · have hiu : i ≠ u := Ne.symm hi1
            by_cases hi2 : v = i
            · subst hi2
              have hj1 : j ≠ u := fun h => hne2 (Prod.ext h.symm rfl)
              simp [ψPair, hiu, hj1, Ne.symm hij]
            · have hiv : i ≠ v := Ne.symm hi2
              simp [ψPair, hiu, hiv]
      rw [hdiag0, hoff_ij, zero_add]
  rw [hDecomp]
  exact PosSemidef.add
    (Matrix.posSemidef_sum _ fun u _ => rankOneMatrix_pos (ψDiag u))
    (Matrix.posSemidef_sum _ fun uv _ => rankOneMatrix_pos (ψPair uv))

private theorem orbitId_eq_zero_of_charge_ne {i j : Nat} (hi : i < 256) (hj : j < 256)
    (hch : chargeVec i ≠ chargeVec j) : orbitId i j = 0 := by
  by_contra hne
  have hcr := canon_row_ok
  unfold checkCanonRowOk at hcr
  simp only [Bool.and_eq_true] at hcr
  have hri := of_range_all hcr.1.1 hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hri
  rcases hri with ⟨⟨hr_lt, hp_lt⟩, hci_eq⟩
  let r := (rowCanonTable.getD (i / 16) []).getD (i % 16) 0
  let p := (rowPermTable.getD (i / 16) []).getD (i % 16) 0
  let pRow := permPairTable.getD p []
  have hself_r := of_range_all hcr.1.2 hr_lt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hself_r
  have hci_lt999 : canonRows15.getD r 999 < 256 := hself_r.1.1
  have hci_999 : canonRows15.getD r 0 = canonRows15.getD r 999 :=
    getD_eq_of_ne _ _ 999 0 (by omega)
  let ci := canonRows15.getD r 0
  let jp := pRow.getD (j / 16) 0 * 16 + pRow.getD (j % 16) 0
  have hj_hi := permPair_lt_16 hp_lt (show j / 16 < 16 by omega)
  have hj_lo := permPair_lt_16 hp_lt (show j % 16 < 16 by omega)
  have hi_hi := permPair_lt_16 hp_lt (show i / 16 < 16 by omega)
  have hi_lo := permPair_lt_16 hp_lt (show i % 16 < 16 by omega)
  have hjp_lt : jp < 256 := by
    have h1 : pRow.getD (j / 16) 0 < 16 := hj_hi.1
    have h2 : pRow.getD (j % 16) 0 < 16 := hj_lo.1
    dsimp [jp]; omega
  have hjp_div : jp / 16 = pRow.getD (j / 16) 0 := by
    have h2 : pRow.getD (j % 16) 0 < 16 := hj_lo.1
    dsimp [jp]; omega
  have hjp_mod : jp % 16 = pRow.getD (j % 16) 0 := by
    have h2 : pRow.getD (j % 16) 0 < 16 := hj_lo.1
    dsimp [jp]; omega
  have horb_chk := of_range_all (of_range_all orbit_charge_ok hr_lt) hjp_lt
  dsimp only at horb_chk
  have hoid_eq : ((canonOrbitTable.getD r []).getD (jp / 16) []).getD (jp % 16) 0 = orbitId i j := by
    unfold orbitId
    dsimp only
    rw [hjp_div, hjp_mod]
  rw [hoid_eq] at horb_chk
  have hoid_b : (orbitId i j == 0) = false := beq_false_of_ne hne
  rw [hoid_b] at horb_chk
  simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at horb_chk
  -- Now `chargeVec ci = chargeVec jp` implies `chargeVec i = chargeVec j` via `perm` bijection:
  let perm := perms24.getD p []
  have hp0 := of_range_all perm_pair_ok hp_lt
  simp only [Bool.and_eq_true] at hp0
  have perm_lt {x : Nat} (hx : x < 4) : applyPerm perm x < 4 := by
    have h1 := of_range_all hp0.1 hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact h1.1.1
  have hci_eq' : pRow.getD (i / 16) 0 * 16 + pRow.getD (i % 16) 0 = ci := by
    dsimp [ci, pRow, p, r]; rw [hci_999]; exact hci_eq
  have ch_perm {u up : Nat} (hu : u < 256)
      (hup : pRow.getD (u / 16) 0 * 16 + pRow.getD (u % 16) 0 = up)
      (k : Nat) (hk : k < 4) :
      (chargeVec u).getD k 0 = (chargeVec up).getD (applyPerm perm k) 0 := by
    have hu_hi := permPair_lt_16 hp_lt (show u / 16 < 16 by omega)
    have hu_lo := permPair_lt_16 hp_lt (show u % 16 < 16 by omega)
    have h1 : pRow.getD (u / 16) 0 =
        applyPerm perm (u / 16 / 4) * 4 + applyPerm perm (u / 16 % 4) := hu_hi.2
    have h2 : pRow.getD (u % 16) 0 =
        applyPerm perm (u % 16 / 4) * 4 + applyPerm perm (u % 16 % 4) := hu_lo.2
    have hb0 := perm_lt (show u / 64 % 4 < 4 by omega)
    have hb1 := perm_lt (show u / 16 % 4 < 4 by omega)
    have hb2 := perm_lt (show u / 4 % 4 < 4 by omega)
    have hb3 := perm_lt (show u % 4 < 4 by omega)
    have hd1 : u / 16 / 4 = u / 64 % 4 := by omega
    have hd2 : u % 16 / 4 = u / 4 % 4 := by omega
    have hd3 : u % 16 % 4 = u % 4 := by omega
    rw [hd1] at h1; rw [hd2, hd3] at h2
    have hup_w : up / 64 % 4 = applyPerm perm (u / 64 % 4) ∧
        up / 16 % 4 = applyPerm perm (u / 16 % 4) ∧
        up / 4 % 4 = applyPerm perm (u / 4 % 4) ∧
        up % 4 = applyPerm perm (u % 4) := by omega
    have hpk := perm_lt hk
    have eq_b {x : Nat} (hx : x < 4) : (applyPerm perm x == applyPerm perm k) = (x == k) := by
      by_cases hxk : x = k
      · subst hxk; simp
      · rw [beq_false_of_ne (mt (applyPerm_inj hp_lt hx hk).mp hxk), beq_false_of_ne hxk]
    unfold chargeVec
    have hget4 (f : Nat → Int) (m : Nat) (hm : m < 4) :
        ((List.range 4).map f).getD m 0 = f m := by
      interval_cases m <;> rfl
    rw [hget4 _ k hk, hget4 _ (applyPerm perm k) hpk,
        hup_w.1, hup_w.2.1, hup_w.2.2.1, hup_w.2.2.2,
        eq_b (by omega), eq_b (by omega), eq_b (by omega), eq_b (by omega)]
  apply hch
  have hlen (u : Nat) : (chargeVec u).length = 4 := rfl
  refine List.ext_getElem (by rw [hlen, hlen]) fun k hk1 hk2 => ?_
  have hk : k < 4 := by rw [hlen] at hk1; exact hk1
  have hgd (u : Nat) : (chargeVec u)[k]'(by rw [hlen]; exact hk) = (chargeVec u).getD k 0 := by
    interval_cases k <;> rfl
  rw [hgd i, hgd j, ch_perm hi hci_eq' k hk, ch_perm hj rfl k hk, horb_chk]

private theorem blk_pos_props (i : Fin 256) :
    let bp := lookupBlkPos i.val
    let blk := blocks55.getD bp.1 []
    bp.1 < 55 ∧ bp.2 < blk.length ∧ blk.getD bp.2 0 = i.val ∧
      chargeVec i.val = chargeVec (blk.getD 0 0) := by
  have hp := of_range_all part_ok i.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  rcases hp with ⟨⟨⟨hb_lt, hr_lt⟩, hget999⟩, hch⟩
  have hget0 : (blocks55.getD (lookupBlkPos i.val).1 []).getD (lookupBlkPos i.val).2 0 = i.val :=
    (getD_eq_of_ne _ _ 999 0 (by have := i.isLt; omega)).trans hget999
  exact ⟨hb_lt, hr_lt, hget0, hch⟩

private theorem blk_item_props {b t : Nat} (hb : b < 55)
    (ht : t < (blocks55.getD b []).length) :
    let idx := (blocks55.getD b []).getD t 0
    blockRepId55.getD b 0 < 6 ∧ idx < 256 ∧ lookupBlkPos idx = (b, t) := by
  have hb0 := of_range_all blk_items_ok hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb0
  have hrep : blockRepId55.getD b 0 < 6 := by
    have hr := hb0.1
    rw [getD_eq_of_ne _ _ 99 0 (by omega)]
    exact hr
  have ht0 := of_range_all hb0.2 ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht0
  have h999 : (blocks55.getD b []).getD t 0 = (blocks55.getD b []).getD t 999 :=
    getD_eq_of_ne _ _ 999 0 (by have := ht0.1; omega)
  dsimp only
  rw [h999]
  exact ⟨hrep, ht0.1, ht0.2⟩

private theorem chol_dot_eq_rowDot (reps : List (List (List Int))) (i j : Fin 256)
    (hblk : (lookupBlkPos i.val).1 = (lookupBlkPos j.val).1) :
    (∑ k : Fin 256, cholEntry reps i.val k.val * cholEntry reps j.val k.val) =
      cholRowDot reps (blockRepId55.getD (lookupBlkPos i.val).1 0)
        (lookupBlkPos i.val).2 (lookupBlkPos j.val).2 := by
  rcases blk_pos_props i with ⟨hb_lt, hri_lt, _, _⟩
  rcases blk_pos_props j with ⟨_, hrj_lt, _, _⟩
  let b := (lookupBlkPos i.val).1
  let ri := (lookupBlkPos i.val).2
  let rj := (lookupBlkPos j.val).2
  have hrj_lt' : rj < (blocks55.getD b []).length := by
    dsimp [rj, b]; rw [hblk]; exact hrj_lt
  unfold cholRowDot
  rw [sumBelow_eq_sum_range]
  have hmin : Nat.min ri rj ≤ ri ∧ Nat.min ri rj ≤ rj ∧
      (Nat.min ri rj = ri ∨ Nat.min ri rj = rj) :=
    ⟨min_le_left ri rj, min_le_right ri rj, (le_total ri rj).imp min_eq_left min_eq_right⟩
  let m := Nat.min ri rj + 1
  have hm_le : m ≤ (blocks55.getD b []).length := by
    have h1 : ri < (blocks55.getD b []).length := hri_lt
    dsimp only [m]; omega
  let emb : Nat → Fin 256 := fun t =>
    if ht : t < (blocks55.getD b []).length then
      ⟨(blocks55.getD b []).getD t 0, (blk_item_props hb_lt ht).2.1⟩
    else ⟨0, by omega⟩
  have hemb_bp {t : Nat} (ht : t < (blocks55.getD b []).length) :
      lookupBlkPos (emb t).val = (b, t) := by
    simp only [emb, dif_pos ht]
    exact (blk_item_props hb_lt ht).2.2
  rw [← Finset.sum_subset (Finset.subset_univ ((Finset.range m).image emb))]
  · rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun t ht => ?_
      have htm : t < m := Finset.mem_range.mp ht
      have ht_len : t < (blocks55.getD b []).length := by omega
      have hbp_k := hemb_bp ht_len
      have hti : ¬ ri < t := by dsimp only [m] at htm; omega
      have htj : ¬ rj < t := by dsimp only [m] at htm; omega
      unfold cholEntry
      dsimp only
      rw [hbp_k, ← hblk]
      change (if (b != b) = true then 0 else if ri < t then 0 else _) *
             (if (b != b) = true then 0 else if rj < t then 0 else _) = _
      simp [hti, htj]
    · intro t1 ht1 t2 ht2 heq
      have h1 : t1 < (blocks55.getD b []).length := by have := Finset.mem_range.mp ht1; omega
      have h2 : t2 < (blocks55.getD b []).length := by have := Finset.mem_range.mp ht2; omega
      have hbp1 := hemb_bp h1
      have hbp2 := hemb_bp h2
      rw [heq] at hbp1
      exact (Prod.mk.inj (hbp1.symm.trans hbp2)).2
  · intro k _ hk_not
    by_cases hkb : (lookupBlkPos k.val).1 = b
    · have hk_ge : m ≤ (lookupBlkPos k.val).2 := by
        by_contra hlt
        apply hk_not
        refine Finset.mem_image.mpr ⟨(lookupBlkPos k.val).2, Finset.mem_range.mpr (by omega), ?_⟩
        rcases blk_pos_props k with ⟨_, hkr_lt, hk_get, _⟩
        have hkr_lt' : (lookupBlkPos k.val).2 < (blocks55.getD b []).length := by
          rw [← hkb]; exact hkr_lt
        ext
        simp only [emb, dif_pos hkr_lt']
        rw [← hkb]
        exact hk_get
      by_cases hik : ri < (lookupBlkPos k.val).2
      · have hzero : cholEntry reps i.val k.val = 0 := by
          unfold cholEntry; dsimp only; rw [hkb]; simp [b, ri, hik]
        rw [hzero, zero_mul]
      · have hjk : rj < (lookupBlkPos k.val).2 := by
          dsimp only [m] at hk_ge; omega
        have hzero : cholEntry reps j.val k.val = 0 := by
          unfold cholEntry; dsimp only
          have hjb : (lookupBlkPos j.val).1 = b := hblk.symm
          rw [hjb, hkb]
          change (if (b != b) = true then 0 else if rj < (lookupBlkPos k.val).2 then 0 else _) = 0
          simp [hjk]
        rw [hzero, mul_zero]
    · have hzero : cholEntry reps i.val k.val = 0 := by
        unfold cholEntry; dsimp only
        have hne : ((lookupBlkPos i.val).1 != (lookupBlkPos k.val).1) = true :=
          bne_iff_ne.mpr (Ne.symm hkb)
        simp [hne]
      rw [hzero, zero_mul]

private theorem scaledIntMat_posSemidef (M_int : Nat → Nat → Int)
    (reps : List (List (List Int)))
    (hZero : ∀ {i j : Nat}, i < 256 → j < 256 → chargeVec i ≠ chargeVec j → M_int i j = 0)
    (hSub : ∀ {b r c : Nat}, b < 55 →
      r < (blocks55.getD b []).length → c < (blocks55.getD b []).length →
      let blk := blocks55.getD b []
      let repBlk := blocks55.getD (repBlockIdx6.getD (blockRepId55.getD b 0) 0) []
      M_int (blk.getD r 0) (blk.getD c 0) = M_int (repBlk.getD r 0) (repBlk.getD c 0))
    (hGersh : checkRep6CholGershgorin M_int reps = true) :
    (Matrix.of fun i j : Fin 256 => (M_int i.val j.val : ℂ)).PosSemidef := by
  let L : CMatrix (Fin 256) := fun i k => (cholEntry reps i.val k.val : ℂ)
  let remInt : Fin 256 → Fin 256 → Int := fun i j =>
    M_int i.val j.val - ∑ k : Fin 256, cholEntry reps i.val k.val * cholEntry reps j.val k.val
  let remReal : Matrix (Fin 256) (Fin 256) ℝ := fun i j => (remInt i j : ℝ)
  have hDiffBlk : ∀ i j : Fin 256, (lookupBlkPos i.val).1 ≠ (lookupBlkPos j.val).1 →
      remInt i j = 0 := by
    intro i j hne
    rcases blk_pos_props i with ⟨hbi, _, _, hchi⟩
    rcases blk_pos_props j with ⟨hbj, _, _, hchj⟩
    have hch_ne : chargeVec i.val ≠ chargeVec j.val := by
      rw [hchi, hchj]
      have hd := of_range_all (of_range_all distinct_charges_ok hbi) hbj
      have hbeq : ((lookupBlkPos i.val).1 == (lookupBlkPos j.val).1) = false := beq_false_of_ne hne
      rw [hbeq] at hd
      simpa [bne_iff_ne] using hd
    have hM0 : M_int i.val j.val = 0 := hZero i.isLt j.isLt hch_ne
    have hL0 : (∑ k : Fin 256, cholEntry reps i.val k.val * cholEntry reps j.val k.val) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hik : (lookupBlkPos i.val).1 = (lookupBlkPos k.val).1
      · have hjk : (lookupBlkPos j.val).1 ≠ (lookupBlkPos k.val).1 := fun h => hne (hik.trans h.symm)
        have hz : cholEntry reps j.val k.val = 0 := by
          unfold cholEntry; simp [bne_iff_ne.mpr hjk]
        rw [hz, mul_zero]
      · have hz : cholEntry reps i.val k.val = 0 := by
          unfold cholEntry; simp [bne_iff_ne.mpr hik]
        rw [hz, zero_mul]
    dsimp [remInt]
    rw [hM0, hL0, sub_zero]
  have hSameBlk : ∀ i j : Fin 256, (lookupBlkPos i.val).1 = (lookupBlkPos j.val).1 →
      let b := (lookupBlkPos i.val).1
      let repId := blockRepId55.getD b 0
      let repBlk := blocks55.getD (repBlockIdx6.getD repId 0) []
      let ri := (lookupBlkPos i.val).2
      let rj := (lookupBlkPos j.val).2
      remInt i j = M_int (repBlk.getD ri 0) (repBlk.getD rj 0) - cholRowDot reps repId ri rj := by
    intro i j hblk
    rcases blk_pos_props i with ⟨hbi, hri, hgeti, _⟩
    rcases blk_pos_props j with ⟨_, hrj, hgetj, _⟩
    dsimp only [remInt]
    rw [chol_dot_eq_rowDot reps i j hblk]
    have hrj' : (lookupBlkPos j.val).2 < (blocks55.getD (lookupBlkPos i.val).1 []).length := by
      rw [hblk]; exact hrj
    have hgetj' : (blocks55.getD (lookupBlkPos i.val).1 []).getD (lookupBlkPos j.val).2 0 = j.val := by
      rw [hblk]; exact hgetj
    have hM := hSub hbi hri hrj'
    dsimp only at hM
    rw [hgeti, hgetj'] at hM
    rw [hM]
  have hSym : ∀ i j : Fin 256, remReal i j = remReal j i := by
    intro i j
    dsimp [remReal]
    norm_cast
    by_cases hblk : (lookupBlkPos i.val).1 = (lookupBlkPos j.val).1
    · rw [hSameBlk i j hblk, hSameBlk j i hblk.symm]
      rcases blk_pos_props i with ⟨hbi, hri, _, _⟩
      rcases blk_pos_props j with ⟨_, hrj, _, _⟩
      set b := (lookupBlkPos i.val).1
      have hrep_lt : blockRepId55.getD b 0 < 6 := (blk_item_props hbi hri).1
      have hlen_eq : (blocks55.getD b []).length =
          (blocks55.getD (repBlockIdx6.getD (blockRepId55.getD b 0) 0) []).length := by
        have hs := of_range_all submat_ok hbi
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        exact hs.1
      have hri_rep : (lookupBlkPos i.val).2 <
          (blocks55.getD (repBlockIdx6.getD (blockRepId55.getD b 0) 0) []).length :=
        hlen_eq ▸ hri
      have hrj_rep : (lookupBlkPos j.val).2 <
          (blocks55.getD (repBlockIdx6.getD (blockRepId55.getD b 0) 0) []).length := by
        rw [← hlen_eq, hblk]; exact hrj
      have hg := of_range_all (of_range_all hGersh hrep_lt) hri_rep
      simp only [Bool.and_eq_true] at hg
      have hsym_c := of_range_all hg.1 hrj_rep
      simp only [beq_iff_eq] at hsym_c
      simpa [b, hblk] using hsym_c
    · rw [hDiffBlk i j hblk, hDiffBlk j i (Ne.symm hblk)]
  have hDom : ∀ i : Fin 256, (∑ j ∈ Finset.univ.erase i, |remReal i j|) ≤ remReal i i := by
    intro i
    rcases blk_pos_props i with ⟨hbi, hri, hgeti, _⟩
    set b := (lookupBlkPos i.val).1
    set ri := (lookupBlkPos i.val).2
    set blk := blocks55.getD b []
    set repId := blockRepId55.getD b 0
    set repBlk := blocks55.getD (repBlockIdx6.getD repId 0) []
    have hrep_lt : repId < 6 := (blk_item_props hbi hri).1
    have hlen_eq : blk.length = repBlk.length := by
      have hs := of_range_all submat_ok hbi
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      exact hs.1
    have hri_rep : ri < repBlk.length := hlen_eq ▸ hri
    have hg := of_range_all (of_range_all hGersh hrep_lt) hri_rep
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    have hdom_int := hg.2
    rw [← hlen_eq, sumBelow_eq_sum_range] at hdom_int
    let emb : Nat → Fin 256 := fun c =>
      if hc : c < blk.length then
        ⟨blk.getD c 0, (blk_item_props hbi hc).2.1⟩
      else ⟨0, by omega⟩
    have hemb_bp {c : Nat} (hc : c < blk.length) : lookupBlkPos (emb c).val = (b, c) := by
      simp only [emb, dif_pos hc]
      exact (blk_item_props hbi hc).2.2
    let S : Finset (Fin 256) := ((Finset.range blk.length).erase ri).image emb
    have hSubS : S ⊆ Finset.univ.erase i := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨c, hc, rfl⟩
      rcases Finset.mem_erase.mp hc with ⟨hc_ne, hc_lt⟩
      have hc_len : c < blk.length := Finset.mem_range.mp hc_lt
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq
      have hbp := hemb_bp hc_len
      rw [heq] at hbp
      exact hc_ne (Prod.mk.inj hbp).2.symm
    have hSumEq : (∑ j ∈ Finset.univ.erase i, |remReal i j|) = ∑ j ∈ S, |remReal i j| := by
      symm
      refine Finset.sum_subset hSubS fun j hj hj_not => ?_
      rcases Finset.mem_erase.mp hj with ⟨hji, _⟩
      by_cases hjb : (lookupBlkPos j.val).1 = b
      · exfalso
        apply hj_not
        rcases blk_pos_props j with ⟨_, hrj, hgetj, _⟩
        have hrj_b : (lookupBlkPos j.val).2 < blk.length := by dsimp [blk]; rw [← hjb]; exact hrj
        have hc_ne : (lookupBlkPos j.val).2 ≠ ri := by
          intro hrc
          apply hji
          ext
          rw [← hgeti]
          have hgetj' : blk.getD (lookupBlkPos j.val).2 0 = j.val := by
            dsimp [blk]; rw [← hjb]; exact hgetj
          rw [← hgetj', hrc]
        refine Finset.mem_image.mpr ⟨(lookupBlkPos j.val).2,
          Finset.mem_erase.mpr ⟨hc_ne, Finset.mem_range.mpr hrj_b⟩, ?_⟩
        ext
        simp only [emb, dif_pos hrj_b]
        dsimp [blk]; rw [← hjb]; exact hgetj
      · dsimp [remReal]
        rw [hDiffBlk i j (Ne.symm hjb)]
        simp
    rw [hSumEq]
    have hImg : (∑ j ∈ S, |remReal i j|) =
        ∑ c ∈ (Finset.range blk.length).erase ri, |remReal i (emb c)| := by
      refine Finset.sum_image fun c1 hc1 c2 hc2 heq => ?_
      have h1 : c1 < blk.length := Finset.mem_range.mp (Finset.mem_erase.mp hc1).2
      have h2 : c2 < blk.length := Finset.mem_range.mp (Finset.mem_erase.mp hc2).2
      have hbp1 := hemb_bp h1
      have hbp2 := hemb_bp h2
      rw [heq] at hbp1
      exact (Prod.mk.inj (hbp1.symm.trans hbp2)).2
    rw [hImg]
    have hRhs : remReal i i =
        ((M_int (repBlk.getD ri 0) (repBlk.getD ri 0) - cholRowDot reps repId ri ri : Int) : ℝ) := by
      dsimp [remReal]
      rw [hSameBlk i i rfl]
    rw [hRhs]
    have hLhs : (∑ c ∈ (Finset.range blk.length).erase ri, |remReal i (emb c)|) =
        ((∑ c ∈ Finset.range blk.length,
          if c == ri then (0 : Int)
          else ((M_int (repBlk.getD ri 0) (repBlk.getD c 0) - cholRowDot reps repId ri c).natAbs : Int) : Int) : ℝ) := by
      push_cast
      rw [← Finset.sum_erase_add (Finset.range blk.length) _ (Finset.mem_range.mpr hri)]
      simp only [beq_self_eq_true, ↓reduceIte, add_zero]
      refine Finset.sum_congr rfl fun c hc => ?_
      rcases Finset.mem_erase.mp hc with ⟨hc_ne, hc_lt⟩
      have hc_len : c < blk.length := Finset.mem_range.mp hc_lt
      have hc_beq : (c == ri) = false := beq_false_of_ne hc_ne
      rw [hc_beq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hbp_c := hemb_bp hc_len
      have hblk_c : (lookupBlkPos i.val).1 = (lookupBlkPos (emb c).val).1 := by
        rw [hbp_c]
      dsimp [remReal]
      rw [hSameBlk i (emb c) hblk_c, hbp_c]
      push_cast
      rfl
    rw [hLhs]
    exact_mod_cast hdom_int
  have hDecomp : (Matrix.of fun i j : Fin 256 => (M_int i.val j.val : ℂ)) =
      L * Lᴴ + remReal.map Complex.ofReal := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.map_apply, L, remReal, remInt]
    simp only [Complex.star_def, ← Complex.ofReal_intCast, Complex.conj_ofReal]
    push_cast
    ring
  rw [hDecomp]
  exact PosSemidef.add (Matrix.posSemidef_self_mul_conjTranspose L)
    (gershgorin_posSemidef remReal hSym hDom)

private theorem posSemidef_div_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CMatrix ι} (hM : M.PosSemidef) {c : ℝ} (hc : 0 < c) :
    (Matrix.of fun i j => M i j / (c : ℂ)).PosSemidef := by
  let S : CMatrix ι := ((1 / Real.sqrt c : ℝ) : ℂ) • (1 : CMatrix ι)
  have hEq : (Matrix.of fun i j => M i j / (c : ℂ)) = S * M * Sᴴ := by
    ext i j
    simp only [S, Matrix.of_apply, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_apply, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    have hsq : ((1 / Real.sqrt c : ℝ) : ℂ) * ((1 / Real.sqrt c : ℝ) : ℂ) = 1 / (c : ℂ) := by
      have hr : (1 / Real.sqrt c) * (1 / Real.sqrt c) = 1 / c := by
        rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (le_of_lt hc)]
      exact_mod_cast hr
    calc
      M i j / (c : ℂ) = (1 / (c : ℂ)) * M i j := by ring
      _ = ((1 / Real.sqrt c : ℝ) : ℂ) * (((1 / Real.sqrt c : ℝ) : ℂ) * M i j) := by
          rw [← mul_assoc, hsq]
  rw [hEq]
  exact hM.mul_mul_conjTranspose_same S

/-- Positive semidefiniteness of the rational SDP dual matrix `Z` (`Z ≥ 0`). -/
theorem zMatrix_posSemidef : zMatrix.PosSemidef := by
  have hInt : (Matrix.of fun i j : Fin 256 => (zScaled i.val j.val : ℂ)).PosSemidef := by
    refine scaledIntMat_posSemidef zScaled zCholReps6 ?_ ?_ z_rep6_chol_gershgorin
    · intro i j hi hj hch
      unfold zScaled
      rw [orbitId_eq_zero_of_charge_ne hi hj hch]
      rfl
    · intro b r c hb hr hc
      have hs := of_range_all submat_ok hb
      simp only [Bool.and_eq_true] at hs
      have hrc := of_range_all (of_range_all hs.2 hr) hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hrc
      exact hrc.1
  have hDiv := posSemidef_div_pos hInt (show (0 : ℝ) < 640000000 by norm_num)
  exact hDiv.submatrix wires4ToFin256

/-- Positive semidefiniteness of `Z - Δ` (`Z ≥ W_0 - W_1`). -/
theorem zMatrix_sub_deltaMatrix_posSemidef : (zMatrix - deltaMatrix).PosSemidef := by
  have hInt : (Matrix.of fun i j : Fin 256 => (zdScaled i.val j.val : ℂ)).PosSemidef := by
    refine scaledIntMat_posSemidef zdScaled zdCholReps6 ?_ ?_ zd_rep6_chol_gershgorin
    · intro i j hi hj hch
      unfold zdScaled zScaled deltaScaled4200
      rw [orbitId_eq_zero_of_charge_ne hi hj hch]
      rfl
    · intro b r c hb hr hc
      have hs := of_range_all submat_ok hb
      simp only [Bool.and_eq_true] at hs
      have hrc := of_range_all (of_range_all hs.2 hr) hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hrc
      dsimp only
      unfold zdScaled
      rw [hrc.1, hrc.2]
  have hDiv := posSemidef_div_pos hInt (show (0 : ℝ) < 13440000000 by norm_num)
  have hSub := hDiv.submatrix wires4ToFin256
  convert hSub using 1
  ext u v
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.of_apply,
    zMatrix, deltaMatrix, zdScaled]
  push_cast
  ring

/-- Auxiliary partial trace `Y = (1 / 4) Tr_{B_I, B_O}(Z)` on `Fin 4`. -/
def zAuxY (ai ao ai' ao' : Fin 4) : ℝ :=
  (1 / 4 : ℝ) * ∑ bi : Fin 4, ∑ bo : Fin 4,
    (zMatrix (ai, ao, bi, bo) (ai', ao', bi, bo)).re

/-- First causal partial-trace condition on `zMatrix`: `Tr_{B_O}(Z) = Y ⊗ I_{B_I}`. -/
theorem zMatrix_causal_trace_one (ai ao bi ai' ao' bi' : Fin 4) :
    (∑ bo : Fin 4, (zMatrix (ai, ao, bi, bo) (ai', ao', bi', bo)).re) =
      if bi = bi' then zAuxY ai ao ai' ao' else 0 := by
  have hc := all_z_causal_traces_ok
  unfold checkZCausalAllAi at hc
  simp only [Bool.and_eq_true] at hc
  have h1 := of_range_all (of_range_all (of_range_all (of_range_all
    (of_range_all (of_range_all hc.1 ai.isLt) ao.isLt) ai'.isLt) ao'.isLt) bi.isLt) bi'.isLt
  simp only [beq_iff_eq] at h1
  have hbo : (∑ bo : Fin 4, zScaled (encode4 ai.val ao.val bi.val bo.val)
      (encode4 ai'.val ao'.val bi'.val bo.val)) =
      sumBelow 4 fun bo => zScaled (encode4 ai.val ao.val bi.val bo)
        (encode4 ai'.val ao'.val bi'.val bo) := by
    rw [sumBelow_eq_sum_range]
    exact Fin.sum_univ_eq_sum_range
      (fun bo => zScaled (encode4 ai.val ao.val bi.val bo) (encode4 ai'.val ao'.val bi'.val bo)) 4
  have hbibo : (∑ x : Fin 4, ∑ bo : Fin 4, zScaled (encode4 ai.val ao.val x.val bo.val)
      (encode4 ai'.val ao'.val x.val bo.val)) =
      sumBelow 16 fun xbo => zScaled (encode4 ai.val ao.val (xbo / 4) (xbo % 4))
        (encode4 ai'.val ao'.val (xbo / 4) (xbo % 4)) := by
    rw [sumBelow_eq_sum_range, ← Finset.sum_product']
    symm
    refine Finset.sum_bij'
      (fun xbo hxbo => (⟨xbo / 4, by have := Finset.mem_range.mp hxbo; omega⟩,
                        ⟨xbo % 4, by have := Finset.mem_range.mp hxbo; omega⟩))
      (fun p _ => p.1.val * 4 + p.2.val) ?_ ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro p _; simp only [Finset.mem_range]; have := p.1.isLt; have := p.2.isLt; omega
    · intro xbo hxbo; dsimp; have := Finset.mem_range.mp hxbo; omega
    · intro p _; ext <;> dsimp <;> (have := p.1.isLt; have := p.2.isLt; omega)
    · intro xbo _; rfl
  have hz_re (u v : Wires4) :
      (zMatrix u v).re = (zScaled (wires4ToFin256 u).val (wires4ToFin256 v).val : ℝ) / 640000000 := by
    dsimp [zMatrix]
    rw [show (640000000 : ℂ) = ((640000000 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [zAuxY, hz_re, wires4ToFin256]
  simp_rw [← Finset.sum_div]
  have h1_int : 4 * (∑ bo : Fin 4, zScaled (encode4 ai.val ao.val bi.val bo.val)
      (encode4 ai'.val ao'.val bi'.val bo.val)) =
      if bi.val = bi'.val then
        ∑ x : Fin 4, ∑ bo : Fin 4, zScaled (encode4 ai.val ao.val x.val bo.val)
          (encode4 ai'.val ao'.val x.val bo.val)
      else 0 := by
    rw [hbo, hbibo]
    exact h1
  by_cases hbi : bi = bi'
  · subst hbi
    simp only [↓reduceIte] at h1_int ⊢
    have h1_r := congrArg (Int.cast (R := ℝ)) h1_int
    push_cast at h1_r
    linarith
  · have hb_ne : bi.val ≠ bi'.val := Fin.val_ne_of_ne hbi
    simp only [hb_ne, ↓reduceIte, hbi] at h1_int ⊢
    have h1_r := congrArg (Int.cast (R := ℝ)) h1_int
    push_cast at h1_r
    linarith

/-- Second causal partial-trace condition on `zMatrix`: `Tr_{A_O}(Y) = (4 / 25) I_{A_I}`. -/
theorem zMatrix_causal_trace_two (ai ai' : Fin 4) :
    (∑ ao : Fin 4, zAuxY ai ao ai' ao) = if ai = ai' then (4 / 25 : ℝ) else 0 := by
  have hc := all_z_causal_traces_ok
  unfold checkZCausalAllAi at hc
  simp only [Bool.and_eq_true] at hc
  have h2 := of_range_all (of_range_all hc.2 ai.isLt) ai'.isLt
  simp only [beq_iff_eq] at h2
  have hsum64 : (∑ ao : Fin 4, ∑ bi : Fin 4, ∑ bo : Fin 4,
      zScaled (encode4 ai.val ao.val bi.val bo.val) (encode4 ai'.val ao.val bi.val bo.val)) =
      sumBelow 64 fun idx => zScaled (encode4 ai.val (idx / 16 % 4) (idx / 4 % 4) (idx % 4))
        (encode4 ai'.val (idx / 16 % 4) (idx / 4 % 4) (idx % 4)) := by
    rw [sumBelow_eq_sum_range, ← Finset.sum_product', ← Finset.sum_product']
    symm
    refine Finset.sum_bij'
      (fun idx _ => ((⟨idx / 16 % 4, by omega⟩, ⟨idx / 4 % 4, by omega⟩), ⟨idx % 4, by omega⟩))
      (fun t _ => (t.1.1.val * 4 + t.1.2.val) * 4 + t.2.val) ?_ ?_ ?_ ?_ ?_
    · intro _ _; simp
    · intro t _; simp only [Finset.mem_range]; have := t.1.1.isLt; have := t.1.2.isLt; have := t.2.isLt; omega
    · intro idx hidx; dsimp; have := Finset.mem_range.mp hidx; omega
    · intro t _; ext <;> dsimp <;> (have := t.1.1.isLt; have := t.1.2.isLt; have := t.2.isLt; omega)
    · intro idx _; rfl
  have hz_re (u v : Wires4) :
      (zMatrix u v).re = (zScaled (wires4ToFin256 u).val (wires4ToFin256 v).val : ℝ) / 640000000 := by
    dsimp [zMatrix]
    rw [show (640000000 : ℂ) = ((640000000 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [zAuxY, hz_re, wires4ToFin256]
  rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_div]
  have h2_int : (∑ ao : Fin 4, ∑ bi : Fin 4, ∑ bo : Fin 4,
      zScaled (encode4 ai.val ao.val bi.val bo.val)
        (encode4 ai'.val ao.val bi.val bo.val)) =
      if ai.val = ai'.val then 409600000 else 0 := by
    rw [hsum64]
    exact h2
  by_cases hai : ai = ai'
  · subst hai
    simp only [↓reduceIte] at h2_int ⊢
    have h2_r := congrArg (Int.cast (R := ℝ)) h2_int
    push_cast at h2_r
    rw [h2_r]
    norm_num
  · have ha_ne : ai.val ≠ ai'.val := Fin.val_ne_of_ne hai
    simp only [ha_ne, ↓reduceIte, hai] at h2_int ⊢
    have h2_r := congrArg (Int.cast (R := ℝ)) h2_int
    push_cast at h2_r
    rw [h2_r]
    norm_num


/-! ## Section 2: Compilation of two-call strategies into causal two-slot testers -/

/-- Unnormalized single-copy Choi matrix `J(Ψ)_{(a_I, a_O), (a'_I, a'_O)}` on `Fin 4`. -/
def choiOneCopy (Ψ : Channel (Fin 4) (Fin 4)) : CMatrix (Fin 4 × Fin 4) :=
  MatrixMap.choi Ψ.map

/-- Kronecker-style two-copy pairing on `Wires4 = (A_I, A_O, B_I, B_O)`. -/
def twoCopyKron (A B : CMatrix (Fin 4 × Fin 4)) : CMatrix Wires4 :=
  fun u v =>
    A (u.1, u.2.1) (v.1, v.2.1) * B (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2)

/-- Unnormalized two-copy Choi matrix `J(Ψ)^{⊗ 2}` on `Wires4`. -/
def choiTwoCopy (Ψ : Channel (Fin 4) (Fin 4)) : CMatrix Wires4 :=
  twoCopyKron (choiOneCopy Ψ) (choiOneCopy Ψ)

private theorem channelKraus_complete_fin4 (Ψ : Channel (Fin 4) (Fin 4)) :
    (∑ r : Fin 4 × Fin 4,
      (ICO.ClassicalDilation.channelKraus Ψ r)ᴴ * ICO.ClassicalDilation.channelKraus Ψ r) = 1 := by
  have h := MatrixMap.krausAdjoint_one_of_tracePreserving (ICO.ClassicalDilation.channelKraus Ψ)
    (by rw [← ICO.ClassicalDilation.channelKraus_map]; exact Ψ.tracePreserving)
  simpa [MatrixMap.krausAdjoint] using h

private theorem oracleMap_channelKraus_entry {N : Type} [Fintype N] [DecidableEq N]
    (Ψ : Channel (Fin 4) (Fin 4)) (Y : CMatrix (Fin 4 × N))
    (ao ao' : Fin 4) (n n' : N) :
    (ICO.AllChannelDilation.oracleMap (M := N) (ICO.ClassicalDilation.channelKraus Ψ) Y)
        (ao, n) (ao', n') =
      ∑ ai : Fin 4, ∑ ai' : Fin 4, Y (ai, n) (ai', n') * choiOneCopy Ψ (ai, ao) (ai', ao') := by
  have hchoi (ai ao ai' ao' : Fin 4) :
      choiOneCopy Ψ (ai, ao) (ai', ao') =
        ∑ r : Fin 4 × Fin 4,
          ICO.ClassicalDilation.channelKraus Ψ r ao ai *
            star (ICO.ClassicalDilation.channelKraus Ψ r ao' ai') := by
    change Ψ.map (Matrix.single ai ai' (1 : ℂ)) ao ao' = _
    rw [ICO.ClassicalDilation.channelKraus_map Ψ]
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single ai']
    · rw [Finset.sum_eq_single ai]
      · simp [Matrix.single]
      · intro x _ hxa
        simp [Matrix.single, hxa.symm]
      · intro h; exact absurd (Finset.mem_univ ai) h
    · intro y _ hya
      have hz : (∑ x : Fin 4, ICO.ClassicalDilation.channelKraus Ψ r ao x *
          Matrix.single ai ai' (1 : ℂ) x y) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [Matrix.single, hya.symm]
      rw [hz, zero_mul]
    · intro h; exact absurd (Finset.mem_univ ai') h
  simp_rw [hchoi, Finset.mul_sum]
  trans (∑ r : Fin 4 × Fin 4, ∑ ai : Fin 4, ∑ ai' : Fin 4,
      Y (ai, n) (ai', n') *
        (ICO.ClassicalDilation.channelKraus Ψ r ao ai *
          star (ICO.ClassicalDilation.channelKraus Ψ r ao' ai')))
  · change (∑ r : Fin 4 × Fin 4,
      (Matrix.kronecker (ICO.ClassicalDilation.channelKraus Ψ r) (1 : CMatrix N) * Y *
        (Matrix.kronecker (ICO.ClassicalDilation.channelKraus Ψ r) (1 : CMatrix N))ᴴ)
        (ao, n) (ao', n')) = _
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
    trans (∑ ai' : Fin 4, ∑ ai : Fin 4,
        Y (ai, n) (ai', n') *
          (ICO.ClassicalDilation.channelKraus Ψ r ao ai *
            star (ICO.ClassicalDilation.channelKraus Ψ r ao' ai')))
    · refine Finset.sum_congr rfl fun ai' _ => ?_
      rw [Finset.sum_eq_single n']
      · simp only [↓reduceIte, mul_one]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ai _ => ?_
        rw [Finset.sum_eq_single n]
        · simp only [↓reduceIte, mul_one]; ring
        · intro m₂ _ hm₂; simp [hm₂.symm]
        · intro h; exact absurd (Finset.mem_univ n) h
      · intro m₁ _ hm₁; simp [hm₁.symm]
      · intro h; exact absurd (Finset.mem_univ n') h
    · rw [Finset.sum_comm]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ai _ => Finset.sum_comm

private theorem oracleChannel_eq_prod_id {N : Type} [Fintype N] [DecidableEq N]
    (Ψ : Channel (Fin 4) (Fin 4)) :
    ICO.AllChannelDilation.oracleChannel (M := N) (ICO.ClassicalDilation.channelKraus Ψ)
      (channelKraus_complete_fin4 Ψ) = Ψ.prod (Channel.idChannel N) := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  ext Y ⟨ao, n⟩ ⟨ao', n'⟩
  change (ICO.AllChannelDilation.oracleMap (M := N) (ICO.ClassicalDilation.channelKraus Ψ) Y)
      (ao, n) (ao', n') =
    (MatrixMap.kron Ψ.map (Channel.idChannel N).map Y) (ao, n) (ao', n')
  rw [oracleMap_channelKraus_entry, MatrixMap.kron_idChannel_apply_slice]
  let S : CMatrix (Fin 4) := fun ai ai' => Y (ai, n) (ai', n')
  rw [MatrixMap.map_eq_sum_single Ψ.map S]
  simp [S, choiOneCopy, MatrixMap.choi, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

private theorem nonempty_output_of_state {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) : Nonempty O := by
  by_contra hEmpty
  haveI : IsEmpty O := not_nonempty_iff.mp hEmpty
  let σ : State O :=
    (tree.channel (Channel.idChannel (Fin 4 × M)) (Channel.idChannel (Fin 4 × M))).applyState ρ
  have htr1 : σ.matrix.trace = 1 := σ.trace_eq_one
  have htr0 : σ.matrix.trace = 0 := by simp [Matrix.trace]
  rw [htr0] at htr1
  exact zero_ne_one htr1

/-- Compile any two-call `BudgetQueryTree.Tree (Fin 4 × M) O 2 B` (with zero extra `Nonempty`
hypotheses on `M`, `O`, or `B`) into a sequential two-query isometric protocol. -/
def compileTreeProtocol {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) :
    ICO.SequentialIsometry.Protocol (Fin 4) B O 2 := by
  classical
  let o₀ : O := Classical.choice (nonempty_output_of_state tree ρ)
  exact
    if hM : Nonempty M then
      ICO.AdaptiveSequentialProtocol.budget (0 : Fin 4) (Classical.choice hM) o₀ tree
    else
      ICO.AdaptiveSequentialProtocol.budget (0 : Fin 4) PUnit.unit o₀
        (Tree.stop (tree.channel (Channel.idChannel (Fin 4 × M)) (Channel.idChannel (Fin 4 × M))) :
          Tree (Fin 4 × PUnit) O 2 B)

private theorem compileTreeProtocol_map {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (Ψ : Channel (Fin 4) (Fin 4)) :
    (compileTreeProtocol tree ρ).map (ICO.ClassicalDilation.channelKraus Ψ) ρ.matrix =
      (tree.channel (Ψ.prod (Channel.idChannel M)) (Ψ.prod (Channel.idChannel M))).map ρ.matrix := by
  classical
  unfold compileTreeProtocol
  split_ifs with hM
  · rw [ICO.AdaptiveSequentialProtocol.budget_map _ _ _ _ _ (channelKraus_complete_fin4 Ψ),
        oracleChannel_eq_prod_id]
  · rw [ICO.AdaptiveSequentialProtocol.budget_map _ _ _ _ _ (channelKraus_complete_fin4 Ψ)]
    haveI : IsEmpty M := not_nonempty_iff.mp hM
    have hEqId : Ψ.prod (Channel.idChannel M) = Channel.idChannel (Fin 4 × M) := by
      apply ICO.BudgetHaarBound.channel_eq_of_map_eq
      ext Y ⟨a, m⟩
      exact isEmptyElim m
    rw [hEqId]
    rfl

/-- Explicit two-slot tester operator on `Wires4` associated to first-call input state `σ₁`,
inter-call isometry `mid`, and Heisenberg-pulled-back final effect `E_F`. -/
def pureTester {M₁ M₂ : Type} [Fintype M₁] [Fintype M₂]
    (σ₁ : CMatrix (Fin 4 × M₁))
    (mid : Matrix (Fin 4 × M₂) (Fin 4 × M₁) ℂ)
    (E_F : CMatrix (Fin 4 × M₂)) : CMatrix Wires4 :=
  fun v u =>
    let ai := u.1; let ao := u.2.1; let bi := u.2.2.1; let bo := u.2.2.2
    let ai' := v.1; let ao' := v.2.1; let bi' := v.2.2.1; let bo' := v.2.2.2
    ∑ m₁ : M₁, ∑ m₁' : M₁, ∑ m₂ : M₂, ∑ m₂' : M₂,
      σ₁ (ai, m₁) (ai', m₁') * mid (bi, m₂) (ao, m₁) *
        star (mid (bi', m₂') (ao', m₁')) * E_F (bo', m₂') (bo, m₂)

private theorem pureTester_posSemidef {M₁ M₂ : Type}
    [Fintype M₁] [DecidableEq M₁] [Fintype M₂] [DecidableEq M₂]
    {σ₁ : CMatrix (Fin 4 × M₁)} (hσ₁ : σ₁.PosSemidef)
    (mid : Matrix (Fin 4 × M₂) (Fin 4 × M₁) ℂ)
    {E_F : CMatrix (Fin 4 × M₂)} (hEF : E_F.PosSemidef) :
    (pureTester σ₁ mid E_F).PosSemidef := by
  let S₁ : CMatrix (Fin 4 × M₁) := psdSqrt σ₁
  let S₂ : CMatrix (Fin 4 × M₂) := psdSqrt E_F
  have hS₁_herm : S₁ᴴ = S₁ := psdSqrt_isHermitian σ₁
  have hS₁_sq : S₁ * S₁ = σ₁ := psdSqrt_mul_self_of_posSemidef hσ₁
  have hS₂_herm : S₂ᴴ = S₂ := psdSqrt_isHermitian E_F
  have hS₂_sq : S₂ * S₂ = E_F := psdSqrt_mul_self_of_posSemidef hEF
  let ψ : (Fin 4 × M₁) × (Fin 4 × M₂) → Wires4 → ℂ := fun xy w =>
    ∑ m₁' : M₁, ∑ m₂' : M₂,
      S₁ xy.1 (w.1, m₁') * star (mid (w.2.2.1, m₂') (w.2.1, m₁')) * S₂ (w.2.2.2, m₂') xy.2
  have hEq : pureTester σ₁ mid E_F =
      ∑ xy : (Fin 4 × M₁) × (Fin 4 × M₂), rankOneMatrix (ψ xy) := by
    ext v u
    simp only [Matrix.sum_apply, rankOneMatrix_apply, ψ, pureTester]
    have hS₁_entry (a a' : Fin 4) (m₁ m₁' : M₁) :
        σ₁ (a, m₁) (a', m₁') =
          ∑ x : Fin 4 × M₁, S₁ x (a', m₁') * star (S₁ x (a, m₁)) := by
      rw [← hS₁_sq]
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hx : star (S₁ x (a, m₁)) = S₁ (a, m₁) x := by
        change (S₁ᴴ) (a, m₁) x = S₁ (a, m₁) x
        rw [hS₁_herm]
      rw [hx, mul_comm]
    have hS₂_entry (b' b : Fin 4) (m₂' m₂ : M₂) :
        E_F (b', m₂') (b, m₂) =
          ∑ y : Fin 4 × M₂, S₂ (b', m₂') y * star (S₂ (b, m₂) y) := by
      rw [← hS₂_sq]
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hy : star (S₂ (b, m₂) y) = S₂ y (b, m₂) := by
        change (S₂ᴴ) y (b, m₂) = S₂ y (b, m₂)
        rw [hS₂_herm]
      rw [hy]
    rw [Fintype.sum_prod_type]
    simp_rw [star_sum, star_mul', star_star, Finset.sum_mul, Finset.mul_sum]
    simp_rw [hS₁_entry, hS₂_entry, Finset.sum_mul, Finset.mul_sum]
    -- Align `(x, y, m₁', m₂', m₁, m₂)` with `(m₁, m₁', m₂, m₂', x, y)` via `Fintype.sum_equiv`:
    let αL := ((Fin 4 × M₁) × (Fin 4 × M₂)) × (M₁ × M₂) × (M₁ × M₂)
    let αR := ((M₁ × M₁) × (M₂ × M₂)) × (Fin 4 × M₁) × (Fin 4 × M₂)
    let e : αL ≃ αR :=
      { toFun := fun ⟨⟨x, y⟩, ⟨m₁', m₂'⟩, ⟨m₁, m₂⟩⟩ => ⟨⟨⟨m₁, m₁'⟩, ⟨m₂, m₂'⟩⟩, ⟨x, y⟩⟩
        invFun := fun ⟨⟨⟨m₁, m₁'⟩, ⟨m₂, m₂'⟩⟩, ⟨x, y⟩⟩ => ⟨⟨x, y⟩, ⟨m₁', m₂'⟩, ⟨m₁, m₂⟩⟩
        left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ => rfl
        right_inv := fun ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩ => rfl }
    have hswap : ∀ (g : (Fin 4 × M₁) → (Fin 4 × M₂) → M₁ → M₂ → M₁ → M₂ → ℂ),
        (∑ x, ∑ y, ∑ m₁', ∑ m₂', ∑ m₁, ∑ m₂, g x y m₁' m₂' m₁ m₂) =
        ∑ m₁, ∑ m₁', ∑ m₂, ∑ m₂', ∑ x, ∑ y, g x y m₁' m₂' m₁ m₂ := by
      intro g
      have he := Fintype.sum_equiv e
        (fun a : αL => g a.1.1 a.1.2 a.2.1.1 a.2.1.2 a.2.2.1 a.2.2.2)
        (fun b : αR => g b.2.1 b.2.2 b.1.1.2 b.1.2.2 b.1.1.1 b.1.2.1)
        (fun _ => rfl)
      dsimp only [αL, αR] at he
      simpa only [Fintype.sum_prod_type] using he
    rw [hswap]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    refine Finset.sum_congr rfl fun m₁' _ => ?_
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    refine Finset.sum_congr rfl fun m₂' _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hEq]
  exact Matrix.posSemidef_sum _ fun xy _ => rankOneMatrix_pos (ψ xy)

private theorem pureTester_add {M₁ M₂ : Type} [Fintype M₁] [Fintype M₂]
    (σ₁ : CMatrix (Fin 4 × M₁))
    (mid : Matrix (Fin 4 × M₂) (Fin 4 × M₁) ℂ)
    (E₁ E₂ : CMatrix (Fin 4 × M₂)) :
    pureTester σ₁ mid E₁ + pureTester σ₁ mid E₂ = pureTester σ₁ mid (E₁ + E₂) := by
  ext v u
  simp only [Matrix.add_apply, pureTester, ← Finset.sum_add_distrib, mul_add]

private theorem trace_choiTwoCopy_pureTester {M₁ M₂ O E : Type}
    [Fintype M₁] [DecidableEq M₁] [Fintype M₂] [DecidableEq M₂]
    [Fintype O] [DecidableEq O] [Fintype E] [DecidableEq E]
    (Ψ : Channel (Fin 4) (Fin 4))
    (σ₁ : CMatrix (Fin 4 × M₁))
    (mid : Matrix (Fin 4 × M₂) (Fin 4 × M₁) ℂ)
    (post : Matrix (O × E) (Fin 4 × M₂) ℂ)
    (F : CMatrix O) :
    (choiTwoCopy Ψ *
      pureTester σ₁ mid (MatrixMap.krausAdjoint (ICO.SequentialIsometry.erasedKraus post) F)).trace =
    ((MatrixMap.ofKraus (ICO.SequentialIsometry.erasedKraus post)
      (ICO.AllChannelDilation.oracleMap (ICO.ClassicalDilation.channelKraus Ψ)
        (mid * ICO.AllChannelDilation.oracleMap (ICO.ClassicalDilation.channelKraus Ψ) σ₁ * midᴴ))) * F).trace := by
  rw [MatrixMap.ofKraus_trace_duality]
  generalize MatrixMap.krausAdjoint (ICO.SequentialIsometry.erasedKraus post) F = E_F
  let σ₂ := mid * ICO.AllChannelDilation.oracleMap (ICO.ClassicalDilation.channelKraus Ψ) σ₁ * midᴴ
  have hσ₂ (bi bi' : Fin 4) (m₂ m₂' : M₂) :
      σ₂ (bi, m₂) (bi', m₂') =
        ∑ ao : Fin 4, ∑ m₁ : M₁, ∑ ao' : Fin 4, ∑ m₁' : M₁,
          ∑ ai : Fin 4, ∑ ai' : Fin 4,
            mid (bi, m₂) (ao, m₁) * (σ₁ (ai, m₁) (ai', m₁') * choiOneCopy Ψ (ai, ao) (ai', ao')) *
              star (mid (bi', m₂') (ao', m₁')) := by
    dsimp only [σ₂]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    trans (∑ ao' : Fin 4, ∑ m₁' : M₁, ∑ ao : Fin 4, ∑ m₁ : M₁,
      ∑ ai : Fin 4, ∑ ai' : Fin 4,
        mid (bi, m₂) (ao, m₁) * (σ₁ (ai, m₁) (ai', m₁') * choiOneCopy Ψ (ai, ao) (ai', ao')) *
          star (mid (bi', m₂') (ao', m₁')))
    · refine Finset.sum_congr rfl fun ao' _ => ?_
      refine Finset.sum_congr rfl fun m₁' _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun ao _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m₁ _ => ?_
      rw [oracleMap_channelKraus_entry Ψ σ₁ ao ao' m₁ m₁', Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ai _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    · let β := (Fin 4 × M₁) × (Fin 4 × M₁)
      let eSwap : β ≃ β := Equiv.prodComm _ _
      have hs := Fintype.sum_equiv eSwap
        (fun p : β => ∑ ai : Fin 4, ∑ ai' : Fin 4,
          mid (bi, m₂) p.2 * (σ₁ (ai, p.2.2) (ai', p.1.2) * choiOneCopy Ψ (ai, p.2.1) (ai', p.1.1)) *
            star (mid (bi', m₂') p.1))
        (fun q : β => ∑ ai : Fin 4, ∑ ai' : Fin 4,
          mid (bi, m₂) q.1 * (σ₁ (ai, q.1.2) (ai', q.2.2) * choiOneCopy Ψ (ai, q.1.1) (ai', q.2.1)) *
            star (mid (bi', m₂') q.2))
        (fun _ => rfl)
      dsimp only [β] at hs
      simpa only [Fintype.sum_prod_type] using hs
  have hRHS : (ICO.AllChannelDilation.oracleMap (ICO.ClassicalDilation.channelKraus Ψ) σ₂ * E_F).trace =
      ∑ bo : Fin 4, ∑ m₂ : M₂, ∑ bo' : Fin 4, ∑ m₂' : M₂,
        ∑ bi : Fin 4, ∑ bi' : Fin 4,
        ∑ ao : Fin 4, ∑ m₁ : M₁, ∑ ao' : Fin 4, ∑ m₁' : M₁,
        ∑ ai : Fin 4, ∑ ai' : Fin 4,
          mid (bi, m₂) (ao, m₁) * (σ₁ (ai, m₁) (ai', m₁') * choiOneCopy Ψ (ai, ao) (ai', ao')) *
            star (mid (bi', m₂') (ao', m₁')) *
            choiOneCopy Ψ (bi, bo) (bi', bo') * E_F (bo', m₂') (bo, m₂) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun bo _ => ?_
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    refine Finset.sum_congr rfl fun bo' _ => ?_
    refine Finset.sum_congr rfl fun m₂' _ => ?_
    rw [oracleMap_channelKraus_entry Ψ σ₂ bo bo' m₂ m₂', Finset.sum_mul]
    refine Finset.sum_congr rfl fun bi _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun bi' _ => ?_
    rw [hσ₂ bi bi' m₂ m₂']
    simp only [Finset.sum_mul]
  have sum4 (g : Wires4 → ℂ) :
      (∑ w : Wires4, g w) =
        ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, g (a, b, c, d) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact Fintype.sum_prod_type _
  have hLHS : (choiTwoCopy Ψ * pureTester σ₁ mid E_F).trace =
      ∑ ai : Fin 4, ∑ ao : Fin 4, ∑ bi : Fin 4, ∑ bo : Fin 4,
      ∑ ai' : Fin 4, ∑ ao' : Fin 4, ∑ bi' : Fin 4, ∑ bo' : Fin 4,
      ∑ m₁ : M₁, ∑ m₁' : M₁, ∑ m₂ : M₂, ∑ m₂' : M₂,
        choiOneCopy Ψ (ai, ao) (ai', ao') * choiOneCopy Ψ (bi, bo) (bi', bo') *
          (σ₁ (ai, m₁) (ai', m₁') * mid (bi, m₂) (ao, m₁) *
            star (mid (bi', m₂') (ao', m₁')) * E_F (bo', m₂') (bo, m₂)) := by
    change (∑ u : Wires4, ∑ v : Wires4, choiTwoCopy Ψ u v * pureTester σ₁ mid E_F v u) = _
    rw [sum4]
    refine Finset.sum_congr rfl fun ai _ => Finset.sum_congr rfl fun ao _ =>
      Finset.sum_congr rfl fun bi _ => Finset.sum_congr rfl fun bo _ => ?_
    rw [sum4]
    refine Finset.sum_congr rfl fun ai' _ => Finset.sum_congr rfl fun ao' _ =>
      Finset.sum_congr rfl fun bi' _ => Finset.sum_congr rfl fun bo' _ => ?_
    dsimp only [choiTwoCopy, twoCopyKron, pureTester]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    exact Finset.mul_sum _ _ _
  change (choiTwoCopy Ψ * pureTester σ₁ mid E_F).trace =
    (ICO.AllChannelDilation.oracleMap (ICO.ClassicalDilation.channelKraus Ψ) σ₂ * E_F).trace
  rw [hLHS, hRHS]
  symm
  have pull_ai : ∀ (f : Fin 4 → M₂ → Fin 4 → M₂ → Fin 4 → Fin 4 → Fin 4 → M₁ → Fin 4 → M₁ → Fin 4 → Fin 4 → ℂ),
      (∑ bo, ∑ m₂, ∑ bo', ∑ m₂', ∑ bi, ∑ bi', ∑ ao, ∑ m₁, ∑ ao', ∑ m₁', ∑ ai, ∑ ai',
        f bo m₂ bo' m₂' bi bi' ao m₁ ao' m₁' ai ai') =
      ∑ ai, ∑ ao, ∑ bi, ∑ bo, ∑ ai', ∑ ao', ∑ bi', ∑ bo', ∑ m₁, ∑ m₁', ∑ m₂, ∑ m₂',
        f bo m₂ bo' m₂' bi bi' ao m₁ ao' m₁' ai ai' := by
    intro f
    let αL := Fin 4 × M₂ × Fin 4 × M₂ × Fin 4 × Fin 4 × Fin 4 × M₁ × Fin 4 × M₁ × Fin 4 × Fin 4
    let αR := Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 × M₁ × M₁ × M₂ × M₂
    let fL : αL → ℂ := fun (bo, m₂, bo', m₂', bi, bi', ao, m₁, ao', m₁', ai, ai') =>
      f bo m₂ bo' m₂' bi bi' ao m₁ ao' m₁' ai ai'
    let fR : αR → ℂ := fun (ai, ao, bi, bo, ai', ao', bi', bo', m₁, m₁', m₂, m₂') =>
      f bo m₂ bo' m₂' bi bi' ao m₁ ao' m₁' ai ai'
    let e : αL ≃ αR :=
      { toFun := fun (bo, m₂, bo', m₂', bi, bi', ao, m₁, ao', m₁', ai, ai') =>
          (ai, ao, bi, bo, ai', ao', bi', bo', m₁, m₁', m₂, m₂')
        invFun := fun (ai, ao, bi, bo, ai', ao', bi', bo', m₁, m₁', m₂, m₂') =>
          (bo, m₂, bo', m₂', bi, bi', ao, m₁, ao', m₁', ai, ai')
        left_inv := fun (_, _, _, _, _, _, _, _, _, _, _, _) => rfl
        right_inv := fun (_, _, _, _, _, _, _, _, _, _, _, _) => rfl }
    have h := Fintype.sum_equiv e fL fR (fun (_, _, _, _, _, _, _, _, _, _, _, _) => rfl)
    have hexpL : (∑ x : αL, fL x) =
        ∑ bo, ∑ m₂, ∑ bo', ∑ m₂', ∑ bi, ∑ bi', ∑ ao, ∑ m₁, ∑ ao', ∑ m₁', ∑ ai, ∑ ai',
          f bo m₂ bo' m₂' bi bi' ao m₁ ao' m₁' ai ai' := by
      dsimp only [αL, fL]
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      exact Fintype.sum_prod_type _
    have hexpR : (∑ y : αR, fR y) =
        ∑ ai, ∑ ao, ∑ bi, ∑ bo, ∑ ai', ∑ ao', ∑ bi', ∑ bo', ∑ m₁, ∑ m₁', ∑ m₂, ∑ m₂',
          f bo m₂ bo' m₂' bi bi' ao m₁ ao' m₁' ai ai' := by
      dsimp only [αR, fR]
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun _ _ => ?_
      exact Fintype.sum_prod_type _
    exact hexpL.symm.trans (h.trans hexpR)
  rw [pull_ai]
  refine Finset.sum_congr rfl fun ai _ => ?_
  refine Finset.sum_congr rfl fun ao _ => ?_
  refine Finset.sum_congr rfl fun bi _ => ?_
  refine Finset.sum_congr rfl fun bo _ => ?_
  refine Finset.sum_congr rfl fun ai' _ => ?_
  refine Finset.sum_congr rfl fun ao' _ => ?_
  refine Finset.sum_congr rfl fun bi' _ => ?_
  refine Finset.sum_congr rfl fun bo' _ => ?_
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  refine Finset.sum_congr rfl fun m₁' _ => ?_
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  refine Finset.sum_congr rfl fun m₂' _ => ?_
  ring

private theorem zMatrix_trace_pureTester_one_re {M₁ M₂ : Type}
    [Fintype M₁] [DecidableEq M₁] [Fintype M₂] [DecidableEq M₂]
    {σ₁ : CMatrix (Fin 4 × M₁)} (hσ₁_tr : σ₁.trace = 1)
    {mid : Matrix (Fin 4 × M₂) (Fin 4 × M₁) ℂ} (hmid : midᴴ * mid = 1) :
    ((zMatrix * pureTester σ₁ mid 1).trace).re = 4 / 25 := by
  let Ξ_c : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ :=
    fun ai' ao' bi' ai ao bi =>
      ∑ m₁ : M₁, ∑ m₁' : M₁, ∑ m₂ : M₂,
        σ₁ (ai, m₁) (ai', m₁') * mid (bi, m₂) (ao, m₁) * star (mid (bi', m₂) (ao', m₁'))
  let Ξ : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
    fun a₁ a₂ a₃ b₁ b₂ b₃ => (Ξ_c a₁ a₂ a₃ b₁ b₂ b₃).re
  let ρ_m : Fin 4 → Fin 4 → ℝ := fun a₁ a₂ => (∑ m₁ : M₁, σ₁ (a₂, m₁) (a₁, m₁)).re
  let trBO_Z : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
    fun ai ao bi ai' ao' bi' =>
      ∑ bo : Fin 4, (zMatrix (ai, ao, bi, bo) (ai', ao', bi', bo)).re
  have hpure_one (v u : Wires4) :
      pureTester σ₁ mid 1 v u =
        if v.2.2.2 = u.2.2.2 then Ξ_c v.1 v.2.1 v.2.2.1 u.1 u.2.1 u.2.2.1 else 0 := by
    simp only [pureTester, Matrix.one_apply, Prod.ext_iff]
    by_cases hbo : v.2.2.2 = u.2.2.2
    · rw [if_pos hbo]
      dsimp only [Ξ_c]
      refine Finset.sum_congr rfl fun m₁ _ => ?_
      refine Finset.sum_congr rfl fun m₁' _ => ?_
      refine Finset.sum_congr rfl fun m₂ _ => ?_
      rw [Finset.sum_eq_single m₂]
      · simp [hbo]
      · intro m₂' _ hm₂'; simp [hm₂']
      · intro h; exact absurd (Finset.mem_univ m₂) h
    · rw [if_neg hbo]
      refine Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₁' _ =>
        Finset.sum_eq_zero fun m₂ _ => Finset.sum_eq_zero fun m₂' _ => ?_
      simp [hbo]
  have hz_im (u v : Wires4) : (zMatrix u v).im = 0 := by
    dsimp [zMatrix]
    rw [show (640000000 : ℂ) = ((640000000 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_im]
  have htr_re : ((zMatrix * pureTester σ₁ mid 1).trace).re =
      ∑ ai : Fin 4, ∑ ao : Fin 4, ∑ bi : Fin 4,
      ∑ ai' : Fin 4, ∑ ao' : Fin 4, ∑ bi' : Fin 4,
        trBO_Z ai ao bi ai' ao' bi' * Ξ ai' ao' bi' ai ao bi := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
    have hmul_re (u v : Wires4) :
        (zMatrix u v * pureTester σ₁ mid 1 v u).re =
          (zMatrix u v).re * (pureTester σ₁ mid 1 v u).re := by
      rw [Complex.mul_re, hz_im u v, zero_mul, sub_zero]
    simp_rw [hmul_re, hpure_one, apply_ite Complex.re, Complex.zero_re]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ai _ => ?_
    refine Finset.sum_congr rfl fun ao _ => ?_
    refine Finset.sum_congr rfl fun bi _ => ?_
    -- Swap `bo` inside `(ai', ao', bi')` and collapse `bo' = bo`:
    trans (∑ bo : Fin 4, ∑ ai' : Fin 4, ∑ ao' : Fin 4, ∑ bi' : Fin 4,
        (zMatrix (ai, ao, bi, bo) (ai', ao', bi', bo)).re * Ξ ai' ao' bi' ai ao bi)
    · refine Finset.sum_congr rfl fun bo _ => ?_
      refine Finset.sum_congr rfl fun ai' _ => ?_
      refine Finset.sum_congr rfl fun ao' _ => ?_
      refine Finset.sum_congr rfl fun bi' _ => ?_
      rw [Finset.sum_eq_single bo]
      · simp [Ξ]
      · intro bo' _ hbo'; simp [hbo']
      · intro h; exact absurd (Finset.mem_univ bo) h
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ai' _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ao' _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun bi' _ => ?_
      rw [← Finset.sum_mul]
  rw [htr_re]
  refine causal_dual_trace_collapse trBO_Z zAuxY Ξ ρ_m (4 / 25)
    zMatrix_causal_trace_one zMatrix_causal_trace_two ?_ ?_
  · intro ai ao ai' ao'
    have hΞ_sum : (∑ bi : Fin 4, Ξ_c ai ao bi ai' ao' bi) =
        if ao = ao' then ∑ m₁ : M₁, σ₁ (ai', m₁) (ai, m₁) else 0 := by
      dsimp only [Ξ_c]
      have hmid_entry (m₁ m₁' : M₁) :
          (∑ bi : Fin 4, ∑ m₂ : M₂,
            mid (bi, m₂) (ao', m₁) * star (mid (bi, m₂) (ao, m₁'))) =
            if ao = ao' ∧ m₁' = m₁ then 1 else 0 := by
        have hm := congrFun (congrFun hmid (ao, m₁')) (ao', m₁)
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
          Matrix.one_apply, Prod.ext_iff] at hm
        rw [← hm]
        refine Finset.sum_congr rfl fun bi _ => Finset.sum_congr rfl fun m₂ _ => ?_
        ring
      trans (∑ m₁ : M₁, ∑ m₁' : M₁,
          σ₁ (ai', m₁) (ai, m₁') *
            ∑ bi : Fin 4, ∑ m₂ : M₂, mid (bi, m₂) (ao', m₁) * star (mid (bi, m₂) (ao, m₁')))
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m₁' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun bi _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m₂ _ => ?_
        ring
      · simp_rw [hmid_entry]
        by_cases hao : ao = ao'
        · subst hao
          simp only [true_and, ↓reduceIte, mul_ite, mul_one, mul_zero]
          refine Finset.sum_congr rfl fun m₁ _ => ?_
          rw [Finset.sum_eq_single m₁]
          · simp
          · intro m₁' _ hm₁'; simp [hm₁']
          · intro h; exact absurd (Finset.mem_univ m₁) h
        · simp [hao]
    have hre := congrArg Complex.re hΞ_sum
    rw [Complex.re_sum] at hre
    by_cases hao : ao = ao'
    · subst hao
      simpa [Ξ, ρ_m] using hre
    · simpa [Ξ, ρ_m, hao] using hre
  · dsimp only [ρ_m]
    rw [← Complex.re_sum]
    have htr : (∑ ai : Fin 4, ∑ m₁ : M₁, σ₁ (ai, m₁) (ai, m₁)) = σ₁.trace := by
      simp [Matrix.trace, Fintype.sum_prod_type]
    rw [htr, hσ₁_tr, Complex.one_re]

private def protocol0Aux {q : ℕ} {C O : Type}
    [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]
    (p : ICO.SequentialIsometry.Protocol (Fin 4) C O q) : CMatrix O → CMatrix C := by
  cases p with
  | stop post _ => exact fun F => MatrixMap.krausAdjoint (ICO.SequentialIsometry.erasedKraus post) F
  | query _ _ _ => exact fun _ => 0

private def protocol1Aux {q : ℕ} {B₁ O : Type}
    [Fintype B₁] [DecidableEq B₁] [Fintype O] [DecidableEq O]
    (p1 : ICO.SequentialIsometry.Protocol (Fin 4) B₁ O q) :
    ∀ {M₁ : Type} [Fintype M₁] [DecidableEq M₁],
      (Fin 4 × M₁ → B₁) → CMatrix (Fin 4 × M₁) → CMatrix O → CMatrix Wires4 := by
  cases p1 with
  | stop _ _ => exact fun _ _ _ => 0
  | query mid _ p0 =>
      exact fun emb σ₁ F => pureTester σ₁ (fun r c => mid r (emb c)) (protocol0Aux p0 F)

private def protocol2Aux {q : ℕ} {B O : Type}
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (p2 : ICO.SequentialIsometry.Protocol (Fin 4) B O q) :
    CMatrix B → CMatrix O → CMatrix Wires4 := by
  cases p2 with
  | stop _ _ => exact fun _ _ => 0
  | query pre _ p1 => exact fun X F => protocol1Aux p1 id (pre * X * preᴴ) F

/-- Level-0 effect pullback of a `Protocol (Fin 4) C O 0`. -/
def protocol0Effect {C O : Type} [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]
    (p0 : ICO.SequentialIsometry.Protocol (Fin 4) C O 0) (F : CMatrix O) : CMatrix C :=
  protocol0Aux p0 F

/-- Level-1 tester extraction of a `Protocol (Fin 4) (Fin 4 × M₁) O 1`. -/
def protocol1Tester {M₁ O : Type} [Fintype M₁] [DecidableEq M₁] [Fintype O] [DecidableEq O]
    (p1 : ICO.SequentialIsometry.Protocol (Fin 4) (Fin 4 × M₁) O 1)
    (σ₁ : CMatrix (Fin 4 × M₁)) (F : CMatrix O) : CMatrix Wires4 :=
  protocol1Aux p1 id σ₁ F

/-- Level-2 tester extraction of a `Protocol (Fin 4) B O 2`. -/
def protocol2Tester {B O : Type} [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (p2 : ICO.SequentialIsometry.Protocol (Fin 4) B O 2)
    (X : CMatrix B) (F : CMatrix O) : CMatrix Wires4 :=
  protocol2Aux p2 X F

@[simp] private theorem protocol0Effect_stop {C O E : Type}
    [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O] [Fintype E] [DecidableEq E]
    (post : Matrix (O × E) C ℂ) (hpost : postᴴ * post = 1) (F : CMatrix O) :
    protocol0Effect (.stop post hpost) F =
      MatrixMap.krausAdjoint (ICO.SequentialIsometry.erasedKraus post) F := rfl

@[simp] private theorem protocol1Tester_query {M₁ M₂ O : Type}
    [Fintype M₁] [DecidableEq M₁] [Fintype M₂] [DecidableEq M₂] [Fintype O] [DecidableEq O]
    (mid : Matrix (Fin 4 × M₂) (Fin 4 × M₁) ℂ) (hmid : midᴴ * mid = 1)
    (p0 : ICO.SequentialIsometry.Protocol (Fin 4) (Fin 4 × M₂) O 0)
    (σ₁ : CMatrix (Fin 4 × M₁)) (F : CMatrix O) :
    protocol1Tester (.query mid hmid p0) σ₁ F = pureTester σ₁ mid (protocol0Effect p0 F) := rfl

@[simp] private theorem protocol2Tester_query {B M₁ O : Type}
    [Fintype B] [DecidableEq B] [Fintype M₁] [DecidableEq M₁] [Fintype O] [DecidableEq O]
    (pre : Matrix (Fin 4 × M₁) B ℂ) (hpre : preᴴ * pre = 1)
    (p1 : ICO.SequentialIsometry.Protocol (Fin 4) (Fin 4 × M₁) O 1)
    (X : CMatrix B) (F : CMatrix O) :
    protocol2Tester (.query pre hpre p1) X F = protocol1Tester p1 (pre * X * preᴴ) F := rfl

/-- Positive semidefinite two-slot tester operator `T_0` (accepting `H_0`) of `(tree, ρ, T)`. -/
def testerAccept {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) : CMatrix Wires4 :=
  protocol2Tester (compileTreeProtocol tree ρ) ρ.matrix T.acceptRhoEffect

/-- Positive semidefinite complementary tester operator `T_1` (rejecting `H_0`) of `(tree, ρ, T)`. -/
def testerReject {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) : CMatrix Wires4 :=
  protocol2Tester (compileTreeProtocol tree ρ) ρ.matrix T.rejectRhoEffect

private theorem protocol0Effect_pos {C O : Type}
    [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]
    (p0 : ICO.SequentialIsometry.Protocol (Fin 4) C O 0)
    {F : CMatrix O} (hF : F.PosSemidef) :
    (protocol0Effect p0 F).PosSemidef := by
  cases p0 with
  | stop post hpost =>
    rw [protocol0Effect_stop]
    exact MatrixMap.krausAdjoint_mapsPositive (ICO.SequentialIsometry.erasedKraus post) F hF

private theorem protocol0Effect_one {C O : Type}
    [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]
    (p0 : ICO.SequentialIsometry.Protocol (Fin 4) C O 0) :
    protocol0Effect p0 1 = 1 := by
  cases p0 with
  | stop post hpost =>
    rw [protocol0Effect_stop]
    ext i j
    have hp := congrFun (congrFun hpost i) j
    simp only [MatrixMap.krausAdjoint, ICO.SequentialIsometry.erasedKraus,
      Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type] at hp ⊢
    rw [← hp, Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_eq_single e]
    · simp
    · intro e' _ he'; rw [if_neg he', mul_zero]
    · intro h; exact absurd (Finset.mem_univ e) h

private theorem protocol0Effect_add {C O : Type}
    [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]
    (p0 : ICO.SequentialIsometry.Protocol (Fin 4) C O 0) (F₁ F₂ : CMatrix O) :
    protocol0Effect p0 F₁ + protocol0Effect p0 F₂ = protocol0Effect p0 (F₁ + F₂) := by
  cases p0 with
  | stop post hpost =>
    rw [protocol0Effect_stop, protocol0Effect_stop, protocol0Effect_stop]
    ext i j
    simp only [MatrixMap.krausAdjoint, Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_mul, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

private theorem protocol2Tester_posSemidef {B O : Type}
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (p2 : ICO.SequentialIsometry.Protocol (Fin 4) B O 2)
    (ρ : State B) {F : CMatrix O} (hF : F.PosSemidef) :
    (protocol2Tester p2 ρ.matrix F).PosSemidef := by
  cases p2 with
  | query pre hpre p1 =>
    cases p1 with
    | query mid hmid p0 =>
      rw [protocol2Tester_query, protocol1Tester_query]
      exact pureTester_posSemidef (ρ.pos.mul_mul_conjTranspose_same pre) mid
        (protocol0Effect_pos p0 hF)

theorem testerAccept_posSemidef {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    (testerAccept tree ρ T).PosSemidef :=
  protocol2Tester_posSemidef (compileTreeProtocol tree ρ) ρ T.acceptRhoEffect_pos

theorem testerReject_posSemidef {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    (testerReject tree ρ T).PosSemidef :=
  protocol2Tester_posSemidef (compileTreeProtocol tree ρ) ρ T.rejectRhoEffect_pos

/-- Causal dual trace collapse: `(zMatrix * (testerAccept + testerReject)).trace.re = 4 / 25`. -/
theorem zMatrix_trace_tester_sum {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    ((zMatrix * (testerAccept tree ρ T + testerReject tree ρ T)).trace).re = 4 / 25 := by
  unfold testerAccept testerReject
  have hsum_eff : T.acceptRhoEffect + T.rejectRhoEffect = 1 := by
    simpa [BinaryHypothesisTest.acceptRhoEffect, BinaryHypothesisTest.rejectRhoEffect,
      Fintype.sum_bool] using T.sum_eq_one
  generalize compileTreeProtocol tree ρ = p2
  cases p2 with
  | query pre hpre p1 =>
    cases p1 with
    | query mid hmid p0 =>
      rw [protocol2Tester_query, protocol2Tester_query,
          protocol1Tester_query, protocol1Tester_query,
          pureTester_add, protocol0Effect_add, hsum_eff, protocol0Effect_one]
      have hσ₁_tr : (pre * ρ.matrix * preᴴ).trace = 1 := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hpre, Matrix.one_mul]
        exact ρ.trace_eq_one
      exact zMatrix_trace_pureTester_one_re hσ₁_tr hmid

/-- Born-Choi trace identity: the operational acceptance probability of `(tree, ρ, T)` on
`Ψ.prod (Channel.idChannel M)` equals `((choiTwoCopy Ψ * testerAccept tree ρ T).trace).re`. -/
theorem acceptance_eq_trace_choiTwoCopy {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O)
    (Ψ : Channel (Fin 4) (Fin 4)) :
    acceptance T tree ρ (Ψ.prod (Channel.idChannel M)) (Ψ.prod (Channel.idChannel M)) =
      ((choiTwoCopy Ψ * testerAccept tree ρ T).trace).re := by
  unfold acceptance ICO.BornAverage.acceptCLM
  change (((tree.channel (Ψ.prod (Channel.idChannel M)) (Ψ.prod (Channel.idChannel M))).map
      ρ.matrix * T.acceptRhoEffect).trace).re = _
  rw [← compileTreeProtocol_map tree ρ Ψ]
  unfold testerAccept
  generalize compileTreeProtocol tree ρ = p2
  cases p2 with
  | query pre hpre p1 =>
    cases p1 with
    | query mid hmid p0 =>
      cases p0 with
      | stop post hpost =>
        rw [protocol2Tester_query, protocol1Tester_query, protocol0Effect_stop]
        dsimp only [ICO.SequentialIsometry.Protocol.map, LinearMap.comp_apply]
        rw [ICO.SequentialIsometry.singleMap_apply, ICO.SequentialIsometry.singleMap_apply,
            ← trace_choiTwoCopy_pureTester]

end

/-! ## Section 3: Exact Haar two-copy moment `W_0` and noise interpolation -/

/-! ### Section 3a: Computable 17-orbit witness tables and kernel `decide` checks -/

def canonX7 : List Nat := [0, 1, 5, 17, 6, 18, 27]

def xToCanon16x16 : List (List (Nat × Nat × Nat × Nat)) := [
  [(0, 0, 0, 0), (1, 0, 0, 0), (1, 2, 0, 0), (1, 3, 0, 0), (1, 0, 2, 0), (2, 0, 0, 0), (4, 0, 0, 0), (4, 1, 0, 0), (1, 2, 2, 0), (4, 0, 2, 0), (2, 2, 0, 0), (4, 4, 0, 0), (1, 3, 2, 0), (4, 1, 2, 0), (4, 4, 2, 0), (2, 3, 0, 0)],
  [(1, 0, 0, 1), (3, 0, 0, 0), (5, 0, 0, 0), (5, 1, 0, 0), (3, 0, 2, 0), (1, 6, 1, 1), (5, 6, 1, 0), (5, 7, 1, 0), (5, 0, 2, 0), (5, 6, 3, 0), (4, 8, 0, 1), (6, 0, 0, 0), (5, 1, 2, 0), (5, 7, 3, 0), (6, 0, 2, 0), (4, 9, 0, 1)],
  [(1, 2, 0, 1), (5, 0, 0, 1), (3, 2, 0, 0), (5, 4, 0, 0), (5, 0, 2, 1), (4, 6, 0, 1), (5, 8, 3, 0), (6, 2, 0, 0), (3, 2, 2, 0), (5, 8, 1, 0), (1, 8, 1, 1), (5, 10, 1, 0), (5, 4, 2, 0), (6, 2, 2, 0), (5, 10, 3, 0), (4, 11, 0, 1)],
  [(1, 3, 0, 1), (5, 1, 0, 1), (5, 4, 0, 1), (3, 3, 0, 0), (5, 1, 2, 1), (4, 7, 0, 1), (6, 3, 0, 0), (5, 9, 3, 0), (5, 4, 2, 1), (6, 3, 2, 0), (4, 10, 0, 1), (5, 11, 3, 0), (3, 3, 2, 0), (5, 9, 1, 0), (5, 11, 1, 0), (1, 9, 1, 1)],
  [(1, 0, 1, 1), (3, 0, 1, 0), (5, 0, 1, 0), (5, 1, 1, 0), (3, 0, 3, 0), (1, 6, 0, 1), (5, 6, 0, 0), (5, 7, 0, 0), (5, 0, 3, 0), (5, 6, 2, 0), (4, 8, 1, 1), (6, 0, 1, 0), (5, 1, 3, 0), (5, 7, 2, 0), (6, 0, 3, 0), (4, 9, 1, 1)],
  [(2, 0, 0, 1), (1, 6, 2, 0), (4, 6, 0, 0), (4, 7, 0, 0), (1, 6, 0, 0), (0, 6, 0, 0), (1, 12, 0, 0), (1, 13, 0, 0), (4, 6, 2, 0), (1, 12, 2, 0), (2, 12, 0, 0), (4, 18, 0, 0), (4, 7, 2, 0), (1, 13, 2, 0), (4, 18, 2, 0), (2, 13, 0, 0)],
  [(4, 0, 0, 1), (5, 6, 2, 1), (5, 8, 3, 1), (6, 3, 0, 1), (5, 6, 0, 1), (1, 12, 0, 1), (3, 12, 0, 0), (5, 18, 0, 0), (5, 8, 1, 1), (3, 12, 2, 0), (1, 14, 1, 1), (5, 20, 1, 0), (6, 3, 2, 1), (5, 18, 2, 0), (5, 20, 3, 0), (4, 21, 0, 1)],
  [(4, 1, 0, 1), (5, 7, 2, 1), (6, 2, 0, 1), (5, 9, 3, 1), (5, 7, 0, 1), (1, 13, 0, 1), (5, 18, 0, 1), (3, 13, 0, 0), (6, 2, 2, 1), (5, 18, 2, 1), (4, 20, 0, 1), (5, 21, 3, 0), (5, 9, 1, 1), (3, 13, 2, 0), (5, 21, 1, 0), (1, 15, 1, 1)],
  [(1, 2, 1, 1), (5, 0, 1, 1), (3, 2, 1, 0), (5, 4, 1, 0), (5, 0, 3, 1), (4, 6, 1, 1), (5, 8, 2, 0), (6, 2, 1, 0), (3, 2, 3, 0), (5, 8, 0, 0), (1, 8, 0, 1), (5, 10, 0, 0), (5, 4, 3, 0), (6, 2, 3, 0), (5, 10, 2, 0), (4, 11, 1, 1)],
  [(4, 0, 1, 1), (5, 6, 3, 1), (5, 8, 2, 1), (6, 3, 1, 1), (5, 6, 1, 1), (1, 12, 1, 1), (3, 12, 1, 0), (5, 18, 1, 0), (5, 8, 0, 1), (3, 12, 3, 0), (1, 14, 0, 1), (5, 20, 0, 0), (6, 3, 3, 1), (5, 18, 3, 0), (5, 20, 2, 0), (4, 21, 1, 1)],
  [(2, 2, 0, 1), (4, 8, 0, 0), (1, 8, 2, 0), (4, 10, 0, 0), (4, 8, 2, 0), (2, 12, 0, 1), (1, 14, 2, 0), (4, 20, 0, 0), (1, 8, 0, 0), (1, 14, 0, 0), (0, 8, 0, 0), (1, 16, 0, 0), (4, 10, 2, 0), (4, 20, 2, 0), (1, 16, 2, 0), (2, 16, 0, 0)],
  [(4, 4, 0, 1), (6, 0, 0, 1), (5, 10, 2, 1), (5, 11, 3, 1), (6, 0, 2, 1), (4, 18, 0, 1), (5, 20, 2, 1), (5, 21, 3, 1), (5, 10, 0, 1), (5, 20, 0, 1), (1, 16, 0, 1), (3, 16, 0, 0), (5, 11, 1, 1), (5, 21, 1, 1), (3, 16, 2, 0), (1, 17, 1, 1)],
  [(1, 3, 1, 1), (5, 1, 1, 1), (5, 4, 1, 1), (3, 3, 1, 0), (5, 1, 3, 1), (4, 7, 1, 1), (6, 3, 1, 0), (5, 9, 2, 0), (5, 4, 3, 1), (6, 3, 3, 0), (4, 10, 1, 1), (5, 11, 2, 0), (3, 3, 3, 0), (5, 9, 0, 0), (5, 11, 0, 0), (1, 9, 0, 1)],
  [(4, 1, 1, 1), (5, 7, 3, 1), (6, 2, 1, 1), (5, 9, 2, 1), (5, 7, 1, 1), (1, 13, 1, 1), (5, 18, 1, 1), (3, 13, 1, 0), (6, 2, 3, 1), (5, 18, 3, 1), (4, 20, 1, 1), (5, 21, 2, 0), (5, 9, 0, 1), (3, 13, 3, 0), (5, 21, 0, 0), (1, 15, 0, 1)],
  [(4, 4, 1, 1), (6, 0, 1, 1), (5, 10, 3, 1), (5, 11, 2, 1), (6, 0, 3, 1), (4, 18, 1, 1), (5, 20, 3, 1), (5, 21, 2, 1), (5, 10, 1, 1), (5, 20, 1, 1), (1, 16, 1, 1), (3, 16, 1, 0), (5, 11, 0, 1), (5, 21, 0, 1), (3, 16, 3, 0), (1, 17, 0, 1)],
  [(2, 3, 0, 1), (4, 9, 0, 0), (4, 11, 0, 0), (1, 9, 2, 0), (4, 9, 2, 0), (2, 13, 0, 1), (4, 21, 0, 0), (1, 15, 2, 0), (4, 11, 2, 0), (4, 21, 2, 0), (2, 16, 0, 1), (1, 17, 2, 0), (1, 9, 0, 0), (1, 15, 0, 0), (1, 17, 0, 0), (0, 9, 0, 0)]
]

def pairByRx7 : List (List (Nat × Nat × Nat × Nat × Nat × Nat)) := [
  [(0, 1, 0, 0, 0, 0)],
  [(1, 2, 0, 0, 0, 0), (4, 2, 0, 0, 2, 0), (16, 3, 0, 0, 0, 0), (64, 3, 0, 0, 1, 0)],
  [(5, 4, 0, 0, 0, 0), (17, 5, 0, 0, 0, 0), (20, 5, 0, 0, 2, 0), (65, 5, 0, 0, 1, 0), (68, 5, 0, 0, 3, 0), (80, 6, 0, 0, 0, 0)],
  [(5, 10, 0, 0, 0, 0), (17, 11, 0, 0, 0, 0), (20, 11, 0, 0, 1, 1), (65, 11, 0, 0, 1, 0), (68, 11, 0, 0, 3, 0), (80, 10, 0, 0, 0, 1)],
  [(6, 7, 0, 0, 0, 0), (9, 7, 0, 0, 2, 0), (18, 8, 0, 0, 0, 0), (24, 8, 0, 0, 2, 0), (33, 8, 2, 2, 0, 0), (36, 8, 2, 2, 2, 0), (66, 8, 0, 0, 1, 0), (72, 8, 0, 0, 3, 0), (96, 9, 0, 0, 0, 0), (129, 8, 2, 2, 1, 0), (132, 8, 2, 2, 3, 0), (144, 9, 0, 0, 1, 0)],
  [(6, 12, 0, 0, 0, 0), (9, 12, 0, 0, 2, 0), (18, 13, 0, 0, 0, 0), (24, 13, 0, 0, 2, 0), (33, 14, 0, 0, 0, 0), (36, 14, 0, 0, 2, 0), (66, 13, 0, 0, 1, 0), (72, 13, 0, 0, 3, 0), (96, 12, 2, 0, 2, 1), (129, 14, 0, 0, 1, 0), (132, 14, 0, 0, 3, 0), (144, 12, 2, 0, 0, 1)],
  [(27, 15, 0, 0, 0, 0), (30, 15, 0, 0, 2, 0), (39, 16, 0, 0, 0, 0), (45, 16, 0, 0, 2, 0), (54, 16, 1, 2, 0, 0), (57, 16, 1, 2, 2, 0), (75, 15, 0, 0, 1, 0), (78, 15, 0, 0, 3, 0), (99, 16, 6, 1, 0, 0), (108, 16, 6, 1, 2, 0), (114, 16, 7, 3, 0, 0), (120, 16, 7, 3, 2, 0), (135, 16, 0, 0, 1, 0), (141, 16, 0, 0, 3, 0), (147, 16, 6, 1, 1, 0), (156, 16, 6, 1, 3, 0), (177, 17, 0, 0, 0, 0), (180, 17, 0, 0, 2, 0), (198, 16, 1, 2, 1, 0), (201, 16, 1, 2, 3, 0), (210, 16, 7, 3, 1, 0), (216, 16, 7, 3, 3, 0), (225, 17, 0, 0, 1, 0), (228, 17, 0, 0, 3, 0)]
]

def reps17List : List (Nat × Nat) := [(0, 0), (1, 1), (1, 16), (5, 5), (5, 17), (5, 80), (6, 6), (6, 18), (6, 96), (17, 5), (17, 17), (18, 6), (18, 18), (18, 33), (27, 27), (27, 39), (27, 177)]

def h4Pairs14List : List (Nat × Nat) := [(0, 1), (0, 5), (0, 6), (0, 17), (0, 18), (0, 27), (1, 5), (1, 6), (1, 18), (1, 39), (5, 0), (5, 7), (5, 19), (5, 27)]

def haarCoeffMat17List : List (List Int) := [
  [4, 48, 0, 12, 0, 0, 48, 0, 0, 0, 24, 0, 96, 0, 24, 0, 0],
  [4, 24, 24, 0, 12, 0, 0, 48, 0, 12, 12, 48, 24, 24, 0, 24, 0],
  [4, 0, 48, 0, 0, 12, 0, 0, 48, 0, 24, 0, 0, 96, 0, 0, 24],
  [-1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [-1, 0, 0, 1, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
  [-1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 8, 0, 0, 0, 0, 0],
  [-1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0],
  [-1, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 4, 0, 0, 0],
  [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 16, 4],
  [0, 2, -2, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0],
  [0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 4, 0, 0, 0, 0],
  [0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 4],
  [1, 0, 0, -1, -4, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, -1, 4, -1, 2, 0, 2, 0, 0, -8, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 1, 0, 4, 0, 0, 0, 0, -4, -4, 0, 0, 0],
  [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, -4]
]

def haarInvMat17List : List (List Int) := [
  [48, 192, 48, -3456, -576, -1152, -1152, -2304, -288, 0, 0, 0, 0, 0, 0, 0, 0],
  [40, 48, -16, 1656, -144, -960, -288, 96, -72, 336, 1344, -1344, 168, 0, 0, 0, 0],
  [-16, 48, 40, 1656, -144, 384, -288, -1248, -72, -336, -1344, 1344, -168, 0, 0, 0, 0],
  [120, -80, 8, -576, 240, -1872, -528, 1296, 120, -4368, 2688, -2688, 336, -1512, -1008, 1008, 504],
  [-20, 88, -20, -576, -264, -24, -24, -552, -132, 0, 0, 0, 0, -1764, 504, -504, -252],
  [8, -80, 120, -576, 240, 816, -528, -1392, 120, 4368, -2688, 2688, -336, -1512, -1008, 1008, 504],
  [60, -40, 4, -2808, 120, 2844, -264, 648, 60, 336, -3696, -1344, 168, 504, 756, 504, 252],
  [-10, 44, -10, -288, -132, -12, -12, 984, -66, 0, 0, 0, 0, 378, 252, 1008, -126],
  [4, -40, 60, 2232, 120, -852, -264, -696, 60, -336, 3696, 1344, -168, 504, 756, 504, 252],
  [-20, 88, -20, -576, 2256, -24, -24, -552, -132, 0, 0, 0, 0, 756, 504, -504, -252],
  [22, 4, 22, -576, -12, -276, 2244, -300, -6, 0, 0, 0, 0, 882, -252, 252, 126],
  [-10, 44, -10, -288, -132, 618, -12, -276, -66, 0, 0, 0, 0, -252, -378, -252, -126],
  [25, 2, -3, 972, -6, -474, -138, -444, -3, 168, 672, 1848, 84, -189, -126, -504, 63],
  [-3, 2, 25, -1548, -6, 198, -138, 1404, -3, -168, -672, -1848, -84, -189, -126, -504, 63],
  [30, -20, 2, -144, 60, -468, -132, 324, 30, 168, 672, -672, -1176, -378, -252, 252, -1134],
  [-5, 22, -5, -144, -66, -6, -6, -138, 597, 0, 0, 0, 0, 189, 126, -126, 567],
  [2, -20, 30, -144, 60, 204, -132, -348, 30, -168, -672, 672, 1176, -378, -252, 252, -1134]
]

def lookupXCanon (x : Nat) : Nat × Nat × Nat × Nat :=
  (xToCanon16x16.getD (x / 16) []).getD (x % 16) (0, 0, 0, 0)

def actWordNat (piIdx s b idx : Nat) : Nat :=
  let perm := perms24.getD piIdx []
  let w0 := applyPerm perm (idx / 64 % 4)
  let w1 := applyPerm perm (idx / 16 % 4)
  let w2 := applyPerm perm (idx / 4 % 4)
  let w3 := applyPerm perm (idx % 4)
  let u0 := if s % 2 == 1 then w1 else w0
  let u1 := if s % 2 == 1 then w0 else w1
  let u2 := if (s / 2) % 2 == 1 then w3 else w2
  let u3 := if (s / 2) % 2 == 1 then w2 else w3
  if b == 1 then encode4 u2 u3 u0 u1 else encode4 u0 u1 u2 u3

def wordProfileNat (idx : Nat) : List Nat :=
  let w0 := idx / 64 % 4; let w1 := idx / 16 % 4
  let w2 := idx / 4 % 4; let w3 := idx % 4
  (List.range 4).map fun a =>
    (if w0 == a then 1 else 0) + (if w1 == a then 1 else 0) +
    (if w2 == a then 1 else 0) + (if w3 == a then 1 else 0)

def findPairInList (jp : Nat) :
    List (Nat × Nat × Nat × Nat × Nat × Nat) → Nat × Nat × Nat × Nat × Nat
  | [] => (0, 0, 0, 0, 0)
  | t :: ts => if t.1 == jp then t.2 else findPairInList jp ts

def lookupPairRx (rx jp : Nat) : Nat × Nat × Nat × Nat × Nat :=
  findPairInList jp (pairByRx7.getD rx [])

def haarOrbitOpt (i j : Nat) : Nat :=
  let xc := lookupXCanon i
  let jp := actWordNat xc.2.1 0 xc.2.2.2 j
  (lookupPairRx xc.1 jp).1

def h4Bit (a b : Nat) : Int :=
  if ((a % 2) * (b % 2) + (a / 2 % 2) * (b / 2 % 2)) % 2 == 1 then -1 else 1

def h4Sign4 (i j : Nat) : Int :=
  h4Bit (i / 64 % 4) (j / 64 % 4) * h4Bit (i / 16 % 4) (j / 16 % 4) *
    h4Bit (i / 4 % 4) (j / 4 % 4) * h4Bit (i % 4) (j % 4)

def applyTraceSigma (r x : Nat) : Nat :=
  let w0 := x / 64 % 4; let w1 := x / 16 % 4; let w2 := x / 4 % 4; let w3 := x % 4
  if r == 0 then encode4 w0 w1 w2 w3
  else if r == 1 then encode4 w2 w1 w0 w3
  else encode4 w2 w3 w0 w1

def diagKInt (i j : Nat) : Int :=
  if i == j && (i / 64 % 4 == i / 16 % 4) && (i / 4 % 4 == i % 4) then 1 else 0

def wCandInt840 (i j : Nat) : Int :=
  let r0 := i / 64 % 4; let r1 := i / 16 % 4; let r2 := i / 4 % 4; let r3 := i % 4
  let col := [j / 64 % 4, j / 16 % 4, j / 4 % 4, j % 4]
  (perms24.map fun p =>
    if r0 == col.getD (applyPerm p 0) 0 &&
       r1 == col.getD (applyPerm p 1) 0 &&
       r2 == col.getD (applyPerm p 2) 0 &&
       r3 == col.getD (applyPerm p 3) 0 then
      weingartenNum13440 p
    else 0).sum

def haarCoeffInt (r k : Nat) : Int :=
  if r < 3 then
    sumBelow 256 fun x => if haarOrbitOpt (applyTraceSigma r x) x == k + 1 then 1 else 0
  else
    let uv := h4Pairs14List.getD (r - 3) (0, 0)
    (sumBelow 256 fun x => if haarOrbitOpt x uv.2 == k + 1 then h4Sign4 uv.1 x else 0) -
      (sumBelow 256 fun y => if haarOrbitOpt uv.1 y == k + 1 then h4Sign4 y uv.2 else 0)

def checkHaarXCanon : Bool :=
  (List.range 7).all (fun rx => canonX7.getD rx 999 < 256) &&
  (List.range 17).all (fun k =>
    let rep := reps17List.getD k (999, 999)
    rep.1 < 256 && rep.2 < 256) &&
  (List.range 14).all (fun m =>
    let uv := h4Pairs14List.getD m (999, 999)
    uv.1 < 256 && uv.2 < 256) &&
  (List.range 256).all fun x =>
    let xc := lookupXCanon x
    xc.1 < 7 && xc.2.1 < 24 && xc.2.2.1 < 4 && xc.2.2.2 < 2 &&
      actWordNat xc.2.1 xc.2.2.1 xc.2.2.2 x == canonX7.getD xc.1 999

def checkHaarPairTable : Bool :=
  (List.range 7).all fun rx =>
    let cx := canonX7.getD rx 0
    (List.range 256).all fun jp =>
      let pr := lookupPairRx rx jp
      if wordProfileNat cx != wordProfileNat jp then pr.1 == 0
      else
        0 < pr.1 && pr.1 ≤ 17 && pr.2.1 < 24 && pr.2.2.1 < 4 && pr.2.2.2.1 < 4 && pr.2.2.2.2 < 2 &&
          let rep := reps17List.getD (pr.1 - 1) (0, 0)
          actWordNat pr.2.1 pr.2.2.1 pr.2.2.2.2 rep.1 == cx &&
          actWordNat pr.2.1 pr.2.2.2.1 pr.2.2.2.2 rep.2 == jp

def checkHaarTraces3 : Bool :=
  (List.range 3).all fun r =>
    let lhs := sumBelow 256 fun x => 840 * diagKInt (applyTraceSigma r x) x
    let rhs := sumBelow 256 fun x => wCandInt840 (applyTraceSigma r x) x
    lhs == rhs

def checkHaarCoeffAndInv17 : Bool :=
  let coeffOk := (List.range 17).all fun r =>
    (List.range 17).all fun k =>
      haarCoeffInt r k == (haarCoeffMat17List.getD r []).getD k 999999
  let invOk := (List.range 17).all fun k0 =>
    (List.range 17).all fun k =>
      let dot := sumBelow 17 fun r =>
        (haarInvMat17List.getD k0 []).getD r 0 * (haarCoeffMat17List.getD r []).getD k 0
      dot == (if k0 == k then 10080 else 0)
  coeffOk && invOk

theorem haar_xcanon_ok : checkHaarXCanon = true := by decide
theorem haar_pair_table_ok : checkHaarPairTable = true := by decide
theorem haar_traces3_ok : checkHaarTraces3 = true := by decide
theorem haar_coeff_and_inv17_ok : checkHaarCoeffAndInv17 = true := by decide

def permWeingartenNum (σ : Equiv.Perm (Fin 4)) : Int :=
  let s0 := (σ 0).val
  let s1 := (σ 1).val
  if (s0 == 0 && s1 == 1) || (s0 == 1 && s1 == 0) then 34
  else if (s0 == 2 && s1 == 3) || (s0 == 3 && s1 == 2) then 6
  else -1

def permToList4 (σ : Equiv.Perm (Fin 4)) : List Nat :=
  [(σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val]

def swap01Perm : Equiv.Perm (Fin 4) := Equiv.swap 0 1
def swap23Perm : Equiv.Perm (Fin 4) := Equiv.swap 2 3
def swap02Perm : Equiv.Perm (Fin 4) := Equiv.swap 0 2
def blockSwapPerm : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem permWeingarten_symmetries :
    ∀ σ : Equiv.Perm (Fin 4),
      permWeingartenNum (swap01Perm * σ) = permWeingartenNum σ ∧
      permWeingartenNum (σ * swap01Perm) = permWeingartenNum σ ∧
      permWeingartenNum (swap23Perm * σ) = permWeingartenNum σ ∧
      permWeingartenNum (σ * swap23Perm) = permWeingartenNum σ ∧
      permWeingartenNum (blockSwapPerm * σ * blockSwapPerm) = permWeingartenNum σ ∧
      permToList4 σ ∈ perms24 ∧
      weingartenNum13440 (permToList4 σ) = permWeingartenNum σ := by decide

theorem perms24_nodup_and_card :
    perms24.Nodup ∧ perms24.length = 24 ∧ Fintype.card (Equiv.Perm (Fin 4)) = 24 := by decide

theorem involutions_sq_one :
    swap01Perm * swap01Perm = 1 ∧ swap23Perm * swap23Perm = 1 ∧
      swap02Perm * swap02Perm = 1 ∧ blockSwapPerm * blockSwapPerm = 1 := by decide

/-! ### Section 3b: `unitaryTwirl 4` commutant proof and two-copy Choi identities -/

noncomputable section

local instance cMatrixContinuousENorm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) :=
  SeminormedAddGroup.toContinuousENorm

def tp4ToFin256 (x : TensorPower (Fin 4) 4) : Fin 256 :=
  wires4ToFin256 (x.1, x.2.1, x.2.2.1, x.2.2.2.1)

def fin256ToTp4 (idx : Fin 256) : TensorPower (Fin 4) 4 :=
  let w := fin256ToWires4 idx
  (w.1, (w.2.1, (w.2.2.1, (w.2.2.2, PUnit.unit))))

def tp4Equiv : TensorPower (Fin 4) 4 ≃ Fin 256 where
  toFun := tp4ToFin256
  invFun := fin256ToTp4
  left_inv x := by
    rcases x with ⟨x0, x1, x2, x3, ⟨⟩⟩
    unfold tp4ToFin256 fin256ToTp4
    dsimp only
    rw [fin256ToWires4_wires4ToFin256]
  right_inv idx := by
    unfold tp4ToFin256 fin256ToTp4
    dsimp only
    exact wires4ToFin256_fin256ToWires4 idx

@[simp] theorem tp4ToFin256_fin256ToTp4 (idx : Fin 256) :
    tp4ToFin256 (fin256ToTp4 idx) = idx :=
  tp4Equiv.right_inv idx

@[simp] theorem fin256ToTp4_tp4ToFin256 (x : TensorPower (Fin 4) 4) :
    fin256ToTp4 (tp4ToFin256 x) = x :=
  tp4Equiv.left_inv x

private theorem fin256ToTp4_encode4 (a0 a1 a2 a3 : Fin 4) :
    fin256ToTp4 ⟨encode4 a0.val a1.val a2.val a3.val, by dsimp [encode4]; omega⟩ =
      (a0, (a1, (a2, (a3, PUnit.unit)))) := by
  have hw : (⟨encode4 a0.val a1.val a2.val a3.val, by dsimp [encode4]; omega⟩ : Fin 256) =
      wires4ToFin256 (a0, a1, a2, a3) := rfl
  rw [hw]
  unfold fin256ToTp4
  rw [fin256ToWires4_wires4ToFin256]
  rfl

@[simp] private theorem tp4_coord0 (x0 x1 x2 x3 : Fin 4) (u : PUnit) :
    tensorPowerEquiv 4 (x0, (x1, (x2, (x3, u)))) 0 = x0 := rfl
@[simp] private theorem tp4_coord1 (x0 x1 x2 x3 : Fin 4) (u : PUnit) :
    tensorPowerEquiv 4 (x0, (x1, (x2, (x3, u)))) 1 = x1 := rfl
@[simp] private theorem tp4_coord2 (x0 x1 x2 x3 : Fin 4) (u : PUnit) :
    tensorPowerEquiv 4 (x0, (x1, (x2, (x3, u)))) 2 = x2 := rfl
@[simp] private theorem tp4_coord3 (x0 x1 x2 x3 : Fin 4) (u : PUnit) :
    tensorPowerEquiv 4 (x0, (x1, (x2, (x3, u)))) 3 = x3 := rfl

private theorem tp4_mk_eq_iff (x0 x1 x2 x3 y0 y1 y2 y3 : Fin 4)
    (u v : TensorPower (Fin 4) 0) :
    ((x0, (x1, (x2, (x3, u)))) : TensorPower (Fin 4) 4) =
      ((y0, (y1, (y2, (y3, v)))) : TensorPower (Fin 4) 4) ↔
      (x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3) := by
  constructor
  · intro h
    rcases Prod.mk.inj h with ⟨rfl, h1⟩
    rcases Prod.mk.inj h1 with ⟨rfl, h2⟩
    rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
    rcases Prod.mk.inj h3 with ⟨rfl, _⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    have hu : u = PUnit.unit := rfl
    have hv : v = PUnit.unit := rfl
    rw [hu, hv]

private theorem integral_cMatrix_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : Matrix.unitaryGroup (Fin 4) ℂ → CMatrix ι}
    (hf : Integrable f (unitaryHaarMeasure (a := Fin 4))) (i j : ι) :
    (∫ U, f U ∂unitaryHaarMeasure (a := Fin 4)) i j =
      ∫ U, f U i j ∂unitaryHaarMeasure (a := Fin 4) := by
  simpa [cMatrixEntryCLM] using
    ((cMatrixEntryCLM (ι := ι) i j).integral_comp_comm hf).symm

private theorem permMat4_apply (σ : Equiv.Perm (Fin 4)) (x y : TensorPower (Fin 4) 4) :
    (permutationMatrix (a := Fin 4) 4 σ : CMatrix (TensorPower (Fin 4) 4)) x y =
      if permEquiv (a := Fin 4) 4 σ x = y then 1 else 0 := by
  simp [permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix]

private theorem permMat4_mul_left (σ : Equiv.Perm (Fin 4))
    (M : CMatrix (TensorPower (Fin 4) 4)) (x y : TensorPower (Fin 4) 4) :
    (permutationMatrix (a := Fin 4) 4 σ * M) x y = M (permEquiv 4 σ x) y := by
  simp only [Matrix.mul_apply, permMat4_apply]
  rw [Finset.sum_eq_single (permEquiv 4 σ x)]
  · simp
  · intro z _ hz; simp [hz.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem permMat4_mul_right_involution {σ : Equiv.Perm (Fin 4)}
    (hσ : σ * σ = 1) (M : CMatrix (TensorPower (Fin 4) 4)) (x y : TensorPower (Fin 4) 4) :
    (M * permutationMatrix (a := Fin 4) 4 σ) x y = M x (permEquiv 4 σ y) := by
  simp only [Matrix.mul_apply, permMat4_apply]
  rw [Finset.sum_eq_single (permEquiv 4 σ y)]
  · have hsq : permEquiv 4 σ (permEquiv 4 σ y) = y := by
      change (σ • (σ • y)) = y
      rw [← mul_smul, hσ, one_smul]
    simp [hsq]
  · intro z _ hz
    have hne : permEquiv 4 σ z ≠ y := by
      intro heq
      apply hz
      rw [← heq]
      change z = (σ • (σ • z))
      rw [← mul_smul, hσ, one_smul]
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Diagonal projector `diagK` on `TensorPower (Fin 4) 4` selecting `(k, k, l, l)`. -/
def diagK : CMatrix (TensorPower (Fin 4) 4) :=
  fun x y => if x = y ∧ x.1 = x.2.1 ∧ x.2.2.1 = x.2.2.2.1 then 1 else 0

private theorem tp4_eq_iff (x z : TensorPower (Fin 4) 4) :
    x = z ↔ x.1 = z.1 ∧ x.2.1 = z.2.1 ∧ x.2.2.1 = z.2.2.1 ∧ x.2.2.2.1 = z.2.2.2.1 := by
  rcases x with ⟨x0, x1, x2, x3, u⟩
  rcases z with ⟨z0, z1, z2, z3, v⟩
  exact tp4_mk_eq_iff x0 x1 x2 x3 z0 z1 z2 z3 u v

private theorem diagK_apply (w z : TensorPower (Fin 4) 4) :
    diagK w z =
      if w.1 = z.1 ∧ w.2.1 = z.2.1 ∧ w.2.2.1 = z.2.2.1 ∧ w.2.2.2.1 = z.2.2.2.1 ∧
         w.1 = w.2.1 ∧ w.2.2.1 = w.2.2.2.1 then 1 else 0 := by
  unfold diagK
  refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
  rw [tp4_eq_iff]
  tauto

/-- Candidate Weingarten sum `wCand` on `TensorPower (Fin 4) 4`. -/
def wCand : CMatrix (TensorPower (Fin 4) 4) :=
  (1 / 840 : ℂ) • ∑ σ : Equiv.Perm (Fin 4),
    (permWeingartenNum σ : ℂ) • permutationMatrix (a := Fin 4) 4 σ

/-- Difference `twirlDiff = unitaryTwirl 4 diagK - wCand` to be proved identically zero. -/
def twirlDiff : CMatrix (TensorPower (Fin 4) 4) :=
  unitaryTwirl (a := Fin 4) 4 diagK - wCand

private theorem wCand_conj_invariant (V : Matrix.unitaryGroup (Fin 4) ℂ) :
    (unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4)) * wCand *
      star (unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4)) = wCand := by
  set V4 : CMatrix (TensorPower (Fin 4) 4) :=
    (unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4))
  have hcomm : V4 * wCand = wCand * V4 := by
    unfold wCand
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul,
        ← permutationMatrix_mul_unitaryTensorPowerMatrix (a := Fin 4) V 4 σ]
  have hunit : V4 * star V4 = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (unitaryTensorPowerMatrix V 4).2
  rw [hcomm, Matrix.mul_assoc, hunit, Matrix.mul_one]

private theorem twirlDiff_conj_invariant (V : Matrix.unitaryGroup (Fin 4) ℂ) :
    (unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4)) * twirlDiff *
      star (unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4)) = twirlDiff := by
  unfold twirlDiff
  rw [Matrix.mul_sub, Matrix.sub_mul,
      unitaryTwirl_conj_invariant (a := Fin 4) 4 diagK V,
      wCand_conj_invariant V]

private theorem twirlDiff_commutes (V : Matrix.unitaryGroup (Fin 4) ℂ) :
    (unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4)) * twirlDiff =
      twirlDiff * (unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4)) :=
  unitaryInvariant_commutes_unitaryTensorPowerMatrix twirlDiff twirlDiff_conj_invariant V

private theorem twirlDiff_eq_zero_of_typeProfile_ne (x y : TensorPower (Fin 4) 4)
    (hne : tensorPowerTypeProfile (a := Fin 4) 4 x ≠ tensorPowerTypeProfile (a := Fin 4) 4 y) :
    twirlDiff x y = 0 := by
  let px : TensorPowerProfile (Fin 4) 4 :=
    ⟨tensorPowerTypeProfile 4 x, tensorPowerTypeProfile_mem_profiles 4 x⟩
  let py : TensorPowerProfile (Fin 4) 4 :=
    ⟨tensorPowerTypeProfile 4 y, tensorPowerTypeProfile_mem_profiles 4 y⟩
  have hpq : px ≠ py := fun h => hne (congrArg Subtype.val h)
  obtain ⟨phase, hphase, hsep⟩ := profilePhaseCharacter_separates hpq
  let V := diagonalPhaseUnitary (a := Fin 4) phase hphase
  have hcomm := congrFun (congrFun (twirlDiff_commutes V) x) y
  have hL : ((unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4)) * twirlDiff) x y =
      profilePhaseCharacter phase px * twirlDiff x y := by
    dsimp only [V]
    simp only [Matrix.mul_apply, unitaryTensorPowerMatrix_diagonalPhase_apply phase hphase 4]
    rw [Finset.sum_eq_single x]
    · simp only [↓reduceIte]
      rw [tensorWordPhase_eq_profilePhaseCharacter_of_typeProfile phase px (x := x) rfl]
    · intro z _ hzx; simp [hzx.symm]
    · intro h; exact absurd (Finset.mem_univ x) h
  have hR : (twirlDiff * (unitaryTensorPowerMatrix V 4 : CMatrix (TensorPower (Fin 4) 4))) x y =
      profilePhaseCharacter phase py * twirlDiff x y := by
    dsimp only [V]
    simp only [Matrix.mul_apply, unitaryTensorPowerMatrix_diagonalPhase_apply phase hphase 4]
    rw [Finset.sum_eq_single y]
    · simp only [↓reduceIte]
      rw [tensorWordPhase_eq_profilePhaseCharacter_of_typeProfile phase py (x := y) rfl, mul_comm]
    · intro z _ hzy; simp [hzy]
    · intro h; exact absurd (Finset.mem_univ y) h
  rw [hL, hR] at hcomm
  have hsub : (profilePhaseCharacter phase px - profilePhaseCharacter phase py) * twirlDiff x y = 0 := by
    rw [sub_mul, hcomm, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hsep)

/-- Map an alphabet permutation `π : Equiv.Perm (Fin 4)` across all 4 slots of `TensorPower (Fin 4) 4`. -/
def mapWord4 (π : Equiv.Perm (Fin 4)) (x : TensorPower (Fin 4) 4) : TensorPower (Fin 4) 4 :=
  (π x.1, (π x.2.1, (π x.2.2.1, (π x.2.2.2.1, PUnit.unit))))

private def alphaPermUnitary (π : Equiv.Perm (Fin 4)) : Matrix.unitaryGroup (Fin 4) ℂ :=
  ⟨fun a c => if a = π.symm c then 1 else 0, by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.one_apply]
    rw [Finset.sum_eq_single (π a)]
    · by_cases hab : a = b
      · subst hab; simp
      · have hba : b ≠ a := Ne.symm hab
        simp [hab, hba]
    · intro c _ hc
      have hne : a ≠ π.symm c := fun h => hc (by rw [h, Equiv.apply_symm_apply])
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h⟩

private theorem unitaryTP4_alphaPerm_apply (π : Equiv.Perm (Fin 4))
    (x z : TensorPower (Fin 4) 4) :
    (unitaryTensorPowerMatrix (alphaPermUnitary π) 4 : CMatrix (TensorPower (Fin 4) 4)) x z =
      if mapWord4 π x = z then 1 else 0 := by
  have halp (a c : Fin 4) :
      (alphaPermUnitary π : CMatrix (Fin 4)) a c = if π a = c then 1 else 0 := by
    change (if a = π.symm c then (1 : ℂ) else 0) = _
    have hiff : (a = π.symm c) ↔ (π a = c) :=
      ⟨fun h => by rw [h, Equiv.apply_symm_apply], fun h => by rw [← h, Equiv.symm_apply_apply]⟩
    by_cases h : π a = c <;> simp [h, hiff]
  have hx0 : tensorPowerEquiv 4 x 0 = x.1 := rfl
  have hx1 : tensorPowerEquiv 4 x 1 = x.2.1 := rfl
  have hx2 : tensorPowerEquiv 4 x 2 = x.2.2.1 := rfl
  have hx3 : tensorPowerEquiv 4 x 3 = x.2.2.2.1 := rfl
  have hz0 : tensorPowerEquiv 4 z 0 = z.1 := rfl
  have hz1 : tensorPowerEquiv 4 z 1 = z.2.1 := rfl
  have hz2 : tensorPowerEquiv 4 z 2 = z.2.2.1 := rfl
  have hz3 : tensorPowerEquiv 4 z 3 = z.2.2.2.1 := rfl
  rw [unitaryTensorPowerMatrix_apply_eq_fin_prod, Fin.prod_univ_four,
      hx0, hx1, hx2, hx3, hz0, hz1, hz2, hz3]
  simp only [halp]
  have hmap : mapWord4 π x = z ↔
      (π x.1 = z.1 ∧ π x.2.1 = z.2.1 ∧ π x.2.2.1 = z.2.2.1 ∧ π x.2.2.2.1 = z.2.2.2.1) :=
    tp4_eq_iff (mapWord4 π x) z
  by_cases hm : mapWord4 π x = z
  · rw [if_pos hm]
    rcases hmap.mp hm with ⟨h0, h1, h2, h3⟩
    dsimp only [mapWord4] at h0 h1 h2 h3
    simp [h0, h1, h2, h3]
  · rw [if_neg hm]
    have hnot : ¬(π x.1 = z.1 ∧ π x.2.1 = z.2.1 ∧ π x.2.2.1 = z.2.2.1 ∧ π x.2.2.2.1 = z.2.2.2.1) :=
      fun h => hm (hmap.mpr h)
    by_cases h0 : π x.1 = z.1 <;> by_cases h1 : π x.2.1 = z.2.1 <;>
      by_cases h2 : π x.2.2.1 = z.2.2.1 <;> by_cases h3 : π x.2.2.2.1 = z.2.2.2.1
    · exact absurd ⟨h0, h1, h2, h3⟩ hnot
    all_goals simp [h0, h1, h2, h3]

private theorem twirlDiff_mapWord4 (π : Equiv.Perm (Fin 4)) (x y : TensorPower (Fin 4) 4) :
    twirlDiff (mapWord4 π x) (mapWord4 π y) = twirlDiff x y := by
  have hinv := congrFun (congrFun (twirlDiff_conj_invariant (alphaPermUnitary π)) x) y
  rw [← hinv]
  simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    unitaryTP4_alphaPerm_apply]
  rw [Finset.sum_eq_single (mapWord4 π y)]
  · simp only [↓reduceIte, star_one, mul_one]
    rw [Finset.sum_eq_single (mapWord4 π x)]
    · simp
    · intro z _ hz; simp [hz.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro z _ hz; simp [hz.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem permEquiv4_coords (σ : Equiv.Perm (Fin 4)) (x : TensorPower (Fin 4) 4) :
    permEquiv (a := Fin 4) 4 σ x =
      (tensorPowerEquiv 4 x (σ⁻¹ 0),
       (tensorPowerEquiv 4 x (σ⁻¹ 1),
        (tensorPowerEquiv 4 x (σ⁻¹ 2),
         (tensorPowerEquiv 4 x (σ⁻¹ 3), PUnit.unit)))) := by
  apply (tensorPowerEquiv 4).injective
  ext t
  rw [tensorPowerEquiv_permEquiv]
  fin_cases t <;> rfl

private theorem diagK_left_swap01 :
    permutationMatrix (a := Fin 4) 4 swap01Perm * diagK = diagK := by
  ext x y
  rw [permMat4_mul_left, permEquiv4_coords]
  have h0 : swap01Perm⁻¹ 0 = 1 := by decide
  have h1 : swap01Perm⁻¹ 1 = 0 := by decide
  have h2 : swap01Perm⁻¹ 2 = 2 := by decide
  have h3 : swap01Perm⁻¹ 3 = 3 := by decide
  rw [h0, h1, h2, h3, diagK_apply, diagK_apply]
  change (if x.2.1 = y.1 ∧ x.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
      x.2.1 = x.1 ∧ x.2.2.1 = x.2.2.2.1 then (1 : ℂ) else 0) =
    if x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
      x.1 = x.2.1 ∧ x.2.2.1 = x.2.2.2.1 then 1 else 0
  refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
  constructor <;> rintro ⟨a, b, c, d, e, f⟩
  · exact ⟨e.symm.trans a, e.trans b, c, d, e.symm, f⟩
  · exact ⟨e.symm.trans a, e.trans b, c, d, e.symm, f⟩

private theorem diagK_left_swap23 :
    permutationMatrix (a := Fin 4) 4 swap23Perm * diagK = diagK := by
  ext x y
  rw [permMat4_mul_left, permEquiv4_coords]
  have h0 : swap23Perm⁻¹ 0 = 0 := by decide
  have h1 : swap23Perm⁻¹ 1 = 1 := by decide
  have h2 : swap23Perm⁻¹ 2 = 3 := by decide
  have h3 : swap23Perm⁻¹ 3 = 2 := by decide
  rw [h0, h1, h2, h3, diagK_apply, diagK_apply]
  change (if x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.2.1 = y.2.2.1 ∧ x.2.2.1 = y.2.2.2.1 ∧
      x.1 = x.2.1 ∧ x.2.2.2.1 = x.2.2.1 then (1 : ℂ) else 0) =
    if x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
      x.1 = x.2.1 ∧ x.2.2.1 = x.2.2.2.1 then 1 else 0
  refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
  constructor <;> rintro ⟨a, b, c, d, e, f⟩
  · exact ⟨a, b, f.symm.trans c, f.trans d, e, f.symm⟩
  · exact ⟨a, b, f.symm.trans c, f.trans d, e, f.symm⟩

private theorem diagK_hermitian : diagKᴴ = diagK := by
  ext x y
  simp only [Matrix.conjTranspose_apply, diagK]
  by_cases hxy : y = x
  · subst hxy; simp
  · have hyx : x ≠ y := Ne.symm hxy
    simp [hxy, hyx]

private theorem permMat4_involution_hermitian {τ : Equiv.Perm (Fin 4)} (hτ : τ * τ = 1) :
    (permutationMatrix (a := Fin 4) 4 τ : CMatrix (TensorPower (Fin 4) 4))ᴴ =
      permutationMatrix (a := Fin 4) 4 τ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, permMat4_apply]
  have hsq (z : TensorPower (Fin 4) 4) :
      permEquiv (a := Fin 4) 4 τ (permEquiv (a := Fin 4) 4 τ z) = z := by
    change (τ • (τ • z)) = z
    rw [← mul_smul, hτ, one_smul]
  have hiff : (permEquiv (a := Fin 4) 4 τ y = x) ↔ (permEquiv (a := Fin 4) 4 τ x = y) :=
    ⟨fun h => by rw [← h, hsq], fun h => by rw [← h, hsq]⟩
  by_cases h : permEquiv (a := Fin 4) 4 τ x = y
  · simp [h, hiff.mpr h]
  · simp [h, mt hiff.mp h]

private theorem diagK_right_swap01 :
    diagK * permutationMatrix (a := Fin 4) 4 swap01Perm = diagK := by
  have h := congrArg Matrix.conjTranspose diagK_left_swap01
  rw [Matrix.conjTranspose_mul, diagK_hermitian,
      permMat4_involution_hermitian involutions_sq_one.1] at h
  exact h

private theorem diagK_right_swap23 :
    diagK * permutationMatrix (a := Fin 4) 4 swap23Perm = diagK := by
  have h := congrArg Matrix.conjTranspose diagK_left_swap23
  rw [Matrix.conjTranspose_mul, diagK_hermitian,
      permMat4_involution_hermitian involutions_sq_one.2.1] at h
  exact h

private theorem diagK_conj_blockSwap :
    permutationMatrix (a := Fin 4) 4 blockSwapPerm * diagK *
      permutationMatrix (a := Fin 4) 4 blockSwapPerm = diagK := by
  ext x y
  rw [permMat4_mul_right_involution involutions_sq_one.2.2.2,
      permMat4_mul_left, permEquiv4_coords, permEquiv4_coords]
  have h0 : blockSwapPerm⁻¹ 0 = 2 := by decide
  have h1 : blockSwapPerm⁻¹ 1 = 3 := by decide
  have h2 : blockSwapPerm⁻¹ 2 = 0 := by decide
  have h3 : blockSwapPerm⁻¹ 3 = 1 := by decide
  rw [h0, h1, h2, h3, diagK_apply, diagK_apply]
  change (if x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧ x.1 = y.1 ∧ x.2.1 = y.2.1 ∧
      x.2.2.1 = x.2.2.2.1 ∧ x.1 = x.2.1 then (1 : ℂ) else 0) =
    if x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ x.2.2.2.1 = y.2.2.2.1 ∧
      x.1 = x.2.1 ∧ x.2.2.1 = x.2.2.2.1 then 1 else 0
  refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
  tauto

private theorem permMat4_commutes_conjTranspose_unitaryTP (U : Matrix.unitaryGroup (Fin 4) ℂ)
    (σ : Equiv.Perm (Fin 4)) (hσ : σ * σ = 1) :
    star (unitaryTensorPowerMatrix U 4 : CMatrix _) * permutationMatrix (a := Fin 4) 4 σ =
      permutationMatrix (a := Fin 4) 4 σ * star (unitaryTensorPowerMatrix U 4 : CMatrix _) := by
  have h := congrArg Matrix.conjTranspose
    (permutationMatrix_mul_unitaryTensorPowerMatrix (a := Fin 4) U 4 σ)
  simp only [Matrix.conjTranspose_mul, permMat4_involution_hermitian hσ] at h
  exact h

private theorem unitaryTwirl_perm_left {τ : Equiv.Perm (Fin 4)}
    (hK : permutationMatrix (a := Fin 4) 4 τ * diagK = diagK) :
    permutationMatrix (a := Fin 4) 4 τ * unitaryTwirl (a := Fin 4) 4 diagK =
      unitaryTwirl (a := Fin 4) 4 diagK := by
  ext x y
  rw [permMat4_mul_left]
  have hf := unitaryTwirl_integrand_integrable (a := Fin 4) 4 diagK
  unfold unitaryTwirl
  rw [integral_cMatrix_entry hf, integral_cMatrix_entry hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [← permMat4_mul_left τ (unitaryTwirlIntegrand (a := Fin 4) 4 diagK U)]
  have hmat : permutationMatrix (a := Fin 4) 4 τ * unitaryTwirlIntegrand (a := Fin 4) 4 diagK U =
      unitaryTwirlIntegrand (a := Fin 4) 4 diagK U := by
    unfold unitaryTwirlIntegrand
    set U4 : CMatrix (TensorPower (Fin 4) 4) :=
      (unitaryTensorPowerMatrix U 4 : CMatrix (TensorPower (Fin 4) 4))
    calc
      permutationMatrix 4 τ * (U4 * diagK * star U4)
          = (permutationMatrix 4 τ * U4) * diagK * star U4 := by simp only [Matrix.mul_assoc]
      _ = U4 * (permutationMatrix 4 τ * diagK) * star U4 := by
          rw [permutationMatrix_mul_unitaryTensorPowerMatrix (a := Fin 4) U 4 τ]
          simp only [Matrix.mul_assoc]; rfl
      _ = U4 * diagK * star U4 := by rw [hK]
  rw [hmat]

private theorem unitaryTwirl_perm_right {τ : Equiv.Perm (Fin 4)} (hτ : τ * τ = 1)
    (hK : diagK * permutationMatrix (a := Fin 4) 4 τ = diagK) :
    unitaryTwirl (a := Fin 4) 4 diagK * permutationMatrix (a := Fin 4) 4 τ =
      unitaryTwirl (a := Fin 4) 4 diagK := by
  ext x y
  rw [permMat4_mul_right_involution hτ]
  have hf := unitaryTwirl_integrand_integrable (a := Fin 4) 4 diagK
  unfold unitaryTwirl
  rw [integral_cMatrix_entry hf, integral_cMatrix_entry hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [← permMat4_mul_right_involution hτ (unitaryTwirlIntegrand (a := Fin 4) 4 diagK U)]
  have hmat : unitaryTwirlIntegrand (a := Fin 4) 4 diagK U * permutationMatrix (a := Fin 4) 4 τ =
      unitaryTwirlIntegrand (a := Fin 4) 4 diagK U := by
    unfold unitaryTwirlIntegrand
    set U4 : CMatrix (TensorPower (Fin 4) 4) :=
      (unitaryTensorPowerMatrix U 4 : CMatrix (TensorPower (Fin 4) 4))
    calc
      (U4 * diagK * star U4) * permutationMatrix 4 τ
          = U4 * diagK * (star U4 * permutationMatrix 4 τ) := by simp only [Matrix.mul_assoc]
      _ = U4 * (diagK * permutationMatrix 4 τ) * star U4 := by
          rw [permMat4_commutes_conjTranspose_unitaryTP U τ hτ]
          simp only [Matrix.mul_assoc]; rfl
      _ = U4 * diagK * star U4 := by rw [hK]
  rw [hmat]

private theorem unitaryTwirl_conj_blockSwap :
    permutationMatrix (a := Fin 4) 4 blockSwapPerm *
      unitaryTwirl (a := Fin 4) 4 diagK *
      permutationMatrix (a := Fin 4) 4 blockSwapPerm =
      unitaryTwirl (a := Fin 4) 4 diagK := by
  have hβ := involutions_sq_one.2.2.2
  have hconj (M : CMatrix (TensorPower (Fin 4) 4)) (x y : TensorPower (Fin 4) 4) :
      M (permEquiv 4 blockSwapPerm x) (permEquiv 4 blockSwapPerm y) =
        (permutationMatrix (a := Fin 4) 4 blockSwapPerm * M *
          permutationMatrix (a := Fin 4) 4 blockSwapPerm) x y := by
    rw [permMat4_mul_right_involution hβ, permMat4_mul_left]
  ext x y
  rw [← hconj]
  have hf := unitaryTwirl_integrand_integrable (a := Fin 4) 4 diagK
  unfold unitaryTwirl
  rw [integral_cMatrix_entry hf, integral_cMatrix_entry hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  dsimp only
  rw [hconj (unitaryTwirlIntegrand (a := Fin 4) 4 diagK U)]
  have hmat : permutationMatrix (a := Fin 4) 4 blockSwapPerm *
      unitaryTwirlIntegrand (a := Fin 4) 4 diagK U *
      permutationMatrix (a := Fin 4) 4 blockSwapPerm =
      unitaryTwirlIntegrand (a := Fin 4) 4 diagK U := by
    unfold unitaryTwirlIntegrand
    calc
      permutationMatrix 4 blockSwapPerm *
          ((unitaryTensorPowerMatrix U 4 : CMatrix _) * diagK *
            star (unitaryTensorPowerMatrix U 4 : CMatrix _)) *
          permutationMatrix 4 blockSwapPerm
          = (unitaryTensorPowerMatrix U 4 : CMatrix _) *
              (permutationMatrix 4 blockSwapPerm * diagK * permutationMatrix 4 blockSwapPerm) *
              star (unitaryTensorPowerMatrix U 4 : CMatrix _) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
                permutationMatrix_mul_unitaryTensorPowerMatrix (a := Fin 4) U 4 blockSwapPerm,
                Matrix.mul_assoc _ _ (permutationMatrix 4 blockSwapPerm),
                permMat4_commutes_conjTranspose_unitaryTP U blockSwapPerm hβ]
            simp only [Matrix.mul_assoc]
      _ = (unitaryTensorPowerMatrix U 4 : CMatrix _) * diagK *
            star (unitaryTensorPowerMatrix U 4 : CMatrix _) := by
            rw [diagK_conj_blockSwap]
  rw [hmat]

private theorem wCand_perm_left {τ : Equiv.Perm (Fin 4)}
    (hnum : ∀ σ : Equiv.Perm (Fin 4), permWeingartenNum (σ * τ) = permWeingartenNum σ) :
    permutationMatrix (a := Fin 4) 4 τ * wCand = wCand := by
  ext x y
  rw [permMat4_mul_left]
  unfold wCand
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, permMat4_apply]
  congr 1
  have hmul (σ : Equiv.Perm (Fin 4)) :
      permEquiv (a := Fin 4) 4 σ (permEquiv (a := Fin 4) 4 τ x) =
        permEquiv (a := Fin 4) 4 (σ * τ) x :=
    (mul_smul σ τ x).symm
  simp_rw [hmul]
  exact Fintype.sum_equiv (Equiv.mulRight τ)
    (fun σ => (permWeingartenNum σ : ℂ) * if permEquiv 4 (σ * τ) x = y then 1 else 0)
    (fun σ' => (permWeingartenNum σ' : ℂ) * if permEquiv 4 σ' x = y then 1 else 0)
    (fun σ => by simp [hnum σ])

private theorem wCand_perm_right {τ : Equiv.Perm (Fin 4)} (hτ : τ * τ = 1)
    (hnum : ∀ σ : Equiv.Perm (Fin 4), permWeingartenNum (τ * σ) = permWeingartenNum σ) :
    wCand * permutationMatrix (a := Fin 4) 4 τ = wCand := by
  ext x y
  rw [permMat4_mul_right_involution hτ]
  unfold wCand
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, permMat4_apply]
  congr 1
  have hiff (σ : Equiv.Perm (Fin 4)) :
      (permEquiv (a := Fin 4) 4 σ x = permEquiv (a := Fin 4) 4 τ y) ↔
        (permEquiv (a := Fin 4) 4 (τ * σ) x = y) := by
    constructor
    · intro h
      change (τ * σ) • x = y
      rw [mul_smul]
      change τ • (permEquiv 4 σ x) = y
      rw [h]
      change (τ • (τ • y)) = y
      rw [← mul_smul, hτ, one_smul]
    · intro h
      rw [← h]
      change permEquiv 4 σ x = (τ • ((τ * σ) • x))
      rw [← mul_smul, ← mul_assoc, hτ, one_mul]
      rfl
  simp_rw [hiff]
  exact Fintype.sum_equiv (Equiv.mulLeft τ)
    (fun σ => (permWeingartenNum σ : ℂ) * if permEquiv 4 (τ * σ) x = y then 1 else 0)
    (fun σ' => (permWeingartenNum σ' : ℂ) * if permEquiv 4 σ' x = y then 1 else 0)
    (fun σ => by simp [hnum σ])

private theorem wCand_conj_blockSwap :
    permutationMatrix (a := Fin 4) 4 blockSwapPerm * wCand *
      permutationMatrix (a := Fin 4) 4 blockSwapPerm = wCand := by
  have hβ := involutions_sq_one.2.2.2
  ext x y
  rw [permMat4_mul_right_involution hβ, permMat4_mul_left]
  unfold wCand
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, permMat4_apply]
  congr 1
  have hiff (σ : Equiv.Perm (Fin 4)) :
      (permEquiv (a := Fin 4) 4 σ (permEquiv (a := Fin 4) 4 blockSwapPerm x) =
        permEquiv (a := Fin 4) 4 blockSwapPerm y) ↔
        (permEquiv (a := Fin 4) 4 (blockSwapPerm * σ * blockSwapPerm) x = y) := by
    constructor
    · intro h
      change (blockSwapPerm * σ * blockSwapPerm) • x = y
      rw [mul_smul, mul_smul]
      change blockSwapPerm • (permEquiv 4 σ (permEquiv 4 blockSwapPerm x)) = y
      rw [h]
      change (blockSwapPerm • (blockSwapPerm • y)) = y
      rw [← mul_smul, hβ, one_smul]
    · intro h
      rw [← h]
      have hsmul (σ' : Equiv.Perm (Fin 4)) (z : TensorPower (Fin 4) 4) :
          permEquiv (a := Fin 4) 4 σ' z = σ' • z := rfl
      simp only [hsmul, ← mul_smul]
      have hgrp : σ * blockSwapPerm = blockSwapPerm * (blockSwapPerm * σ * blockSwapPerm) := by
        rw [← mul_assoc, ← mul_assoc, hβ, one_mul]
      rw [hgrp]
  simp_rw [hiff]
  let e : Equiv.Perm (Fin 4) ≃ Equiv.Perm (Fin 4) :=
    { toFun := fun σ => blockSwapPerm * σ * blockSwapPerm
      invFun := fun σ => blockSwapPerm * σ * blockSwapPerm
      left_inv := fun σ => by
        calc
          blockSwapPerm * (blockSwapPerm * σ * blockSwapPerm) * blockSwapPerm
              = (blockSwapPerm * blockSwapPerm) * σ * (blockSwapPerm * blockSwapPerm) := by group
          _ = σ := by rw [hβ, one_mul, mul_one]
      right_inv := fun σ => by
        calc
          blockSwapPerm * (blockSwapPerm * σ * blockSwapPerm) * blockSwapPerm
              = (blockSwapPerm * blockSwapPerm) * σ * (blockSwapPerm * blockSwapPerm) := by group
          _ = σ := by rw [hβ, one_mul, mul_one] }
  exact Fintype.sum_equiv e
    (fun σ => (permWeingartenNum σ : ℂ) *
      if permEquiv 4 (blockSwapPerm * σ * blockSwapPerm) x = y then 1 else 0)
    (fun σ' => (permWeingartenNum σ' : ℂ) * if permEquiv 4 σ' x = y then 1 else 0)
    (fun σ => by simp [e, (permWeingarten_symmetries σ).2.2.2.2.1])

private theorem twirlDiff_left_swap01 (x y : TensorPower (Fin 4) 4) :
    twirlDiff (permEquiv 4 swap01Perm x) y = twirlDiff x y := by
  rw [← permMat4_mul_left swap01Perm twirlDiff]
  unfold twirlDiff
  rw [Matrix.mul_sub, unitaryTwirl_perm_left diagK_left_swap01,
      wCand_perm_left (fun σ => (permWeingarten_symmetries σ).2.1)]

private theorem twirlDiff_right_swap01 (x y : TensorPower (Fin 4) 4) :
    twirlDiff x (permEquiv 4 swap01Perm y) = twirlDiff x y := by
  rw [← permMat4_mul_right_involution involutions_sq_one.1 twirlDiff]
  unfold twirlDiff
  rw [Matrix.sub_mul, unitaryTwirl_perm_right involutions_sq_one.1 diagK_right_swap01,
      wCand_perm_right involutions_sq_one.1 (fun σ => (permWeingarten_symmetries σ).1)]

private theorem twirlDiff_left_swap23 (x y : TensorPower (Fin 4) 4) :
    twirlDiff (permEquiv 4 swap23Perm x) y = twirlDiff x y := by
  rw [← permMat4_mul_left swap23Perm twirlDiff]
  unfold twirlDiff
  rw [Matrix.mul_sub, unitaryTwirl_perm_left diagK_left_swap23,
      wCand_perm_left (fun σ => (permWeingarten_symmetries σ).2.2.2.1)]

private theorem twirlDiff_right_swap23 (x y : TensorPower (Fin 4) 4) :
    twirlDiff x (permEquiv 4 swap23Perm y) = twirlDiff x y := by
  rw [← permMat4_mul_right_involution involutions_sq_one.2.1 twirlDiff]
  unfold twirlDiff
  rw [Matrix.sub_mul, unitaryTwirl_perm_right involutions_sq_one.2.1 diagK_right_swap23,
      wCand_perm_right involutions_sq_one.2.1 (fun σ => (permWeingarten_symmetries σ).2.2.1)]

private theorem twirlDiff_blockSwap (x y : TensorPower (Fin 4) 4) :
    twirlDiff (permEquiv 4 blockSwapPerm x) (permEquiv 4 blockSwapPerm y) = twirlDiff x y := by
  have hβ := involutions_sq_one.2.2.2
  have hconj : twirlDiff (permEquiv 4 blockSwapPerm x) (permEquiv 4 blockSwapPerm y) =
      (permutationMatrix (a := Fin 4) 4 blockSwapPerm * twirlDiff *
        permutationMatrix (a := Fin 4) 4 blockSwapPerm) x y := by
    rw [permMat4_mul_right_involution hβ, permMat4_mul_left]
  rw [hconj]
  unfold twirlDiff
  rw [Matrix.mul_sub, Matrix.sub_mul, unitaryTwirl_conj_blockSwap, wCand_conj_blockSwap]

private theorem permToList4_inj : Function.Injective permToList4 := by
  intro σ₁ σ₂ h
  unfold permToList4 at h
  simp only [List.cons.injEq, and_true] at h
  ext t
  fin_cases t
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

private theorem univ_image_permToList4 :
    (Finset.univ : Finset (Equiv.Perm (Fin 4))).image permToList4 = perms24.toFinset := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨σ, _, rfl⟩
    exact List.mem_toFinset.mpr (permWeingarten_symmetries σ).2.2.2.2.2.1
  · rw [Finset.card_image_of_injective _ permToList4_inj, Finset.card_univ,
        List.toFinset_card_of_nodup perms24_nodup_and_card.1,
        perms24_nodup_and_card.2.1, perms24_nodup_and_card.2.2]

private theorem sum_perm_eq_perms24_sum (F : List Nat → ℂ) :
    (∑ σ : Equiv.Perm (Fin 4), F (permToList4 σ)) = (perms24.map F).sum := by
  rw [← Finset.sum_image (fun _ _ _ _ h => permToList4_inj h),
      univ_image_permToList4, List.sum_toFinset _ perms24_nodup_and_card.1]

private theorem exists_perm_of_piIdx {piIdx : Nat} (hpi : piIdx < 24) :
    ∃ π : Equiv.Perm (Fin 4), permToList4 π = perms24.getD piIdx [] := by
  have hlen : perms24.length = 24 := perms24_nodup_and_card.2.1
  have hlt : piIdx < perms24.length := hlen ▸ hpi
  have hmem : perms24.getD piIdx [] ∈ perms24.toFinset := by
    have hg : perms24.getD piIdx [] = perms24[piIdx]'hlt := by simp [List.getD, hlt]
    rw [hg]
    exact List.mem_toFinset.mpr (List.getElem_mem hlt)
  rw [← univ_image_permToList4] at hmem
  rcases Finset.mem_image.mp hmem with ⟨π, _, hπ⟩
  exact ⟨π, hπ⟩

private theorem actWordNat_lt_256 {piIdx s b idx : Nat} (hpi : piIdx < 24) :
    actWordNat piIdx s b idx < 256 := by
  obtain ⟨π, hπ⟩ := exists_perm_of_piIdx hpi
  have happ (a : Fin 4) : applyPerm (perms24.getD piIdx []) a.val = (π a).val := by
    unfold applyPerm
    rw [← hπ]
    fin_cases a <;> rfl
  have h0 := happ ⟨idx / 64 % 4, by omega⟩
  have h1 := happ ⟨idx / 16 % 4, by omega⟩
  have h2 := happ ⟨idx / 4 % 4, by omega⟩
  have h3 := happ ⟨idx % 4, by omega⟩
  have := (π ⟨idx / 64 % 4, by omega⟩).isLt
  have := (π ⟨idx / 16 % 4, by omega⟩).isLt
  have := (π ⟨idx / 4 % 4, by omega⟩).isLt
  have := (π ⟨idx % 4, by omega⟩).isLt
  unfold actWordNat
  dsimp only at h0 h1 h2 h3 ⊢
  rw [h0, h1, h2, h3]
  split_ifs <;> dsimp [encode4] <;> omega

private theorem actWordNat_tp4_eq {piIdx s b : Nat} (hpi : piIdx < 24) (idx : Fin 256)
    (π : Equiv.Perm (Fin 4)) (hπ : permToList4 π = perms24.getD piIdx []) :
    fin256ToTp4 ⟨actWordNat piIdx s b idx.val, actWordNat_lt_256 hpi⟩ =
      (let w0 := mapWord4 π (fin256ToTp4 idx)
       let w1 := if s % 2 == 1 then permEquiv 4 swap01Perm w0 else w0
       let w2 := if (s / 2) % 2 == 1 then permEquiv 4 swap23Perm w1 else w1
       if b == 1 then permEquiv 4 blockSwapPerm w2 else w2) := by
  have happ (a : Fin 4) : applyPerm (perms24.getD piIdx []) a.val = (π a).val := by
    unfold applyPerm; rw [← hπ]; fin_cases a <;> rfl
  have hs01 (w : TensorPower (Fin 4) 4) :
      permEquiv 4 swap01Perm w = (w.2.1, (w.1, (w.2.2.1, (w.2.2.2.1, PUnit.unit)))) := by
    rw [permEquiv4_coords]
    have c0 : swap01Perm⁻¹ 0 = 1 := by decide
    have c1 : swap01Perm⁻¹ 1 = 0 := by decide
    have c2 : swap01Perm⁻¹ 2 = 2 := by decide
    have c3 : swap01Perm⁻¹ 3 = 3 := by decide
    rcases w with ⟨a0, a1, a2, a3, ⟨⟩⟩
    rw [c0, c1, c2, c3]; rfl
  have hs23 (w : TensorPower (Fin 4) 4) :
      permEquiv 4 swap23Perm w = (w.1, (w.2.1, (w.2.2.2.1, (w.2.2.1, PUnit.unit)))) := by
    rw [permEquiv4_coords]
    have c0 : swap23Perm⁻¹ 0 = 0 := by decide
    have c1 : swap23Perm⁻¹ 1 = 1 := by decide
    have c2 : swap23Perm⁻¹ 2 = 3 := by decide
    have c3 : swap23Perm⁻¹ 3 = 2 := by decide
    rcases w with ⟨a0, a1, a2, a3, ⟨⟩⟩
    rw [c0, c1, c2, c3]; rfl
  have hblk (w : TensorPower (Fin 4) 4) :
      permEquiv 4 blockSwapPerm w = (w.2.2.1, (w.2.2.2.1, (w.1, (w.2.1, PUnit.unit)))) := by
    rw [permEquiv4_coords]
    have c0 : blockSwapPerm⁻¹ 0 = 2 := by decide
    have c1 : blockSwapPerm⁻¹ 1 = 3 := by decide
    have c2 : blockSwapPerm⁻¹ 2 = 0 := by decide
    have c3 : blockSwapPerm⁻¹ 3 = 1 := by decide
    rcases w with ⟨a0, a1, a2, a3, ⟨⟩⟩
    rw [c0, c1, c2, c3]; rfl
  dsimp only
  have h0 := happ ⟨idx.val / 64 % 4, by omega⟩
  have h1 := happ ⟨idx.val / 16 % 4, by omega⟩
  have h2 := happ ⟨idx.val / 4 % 4, by omega⟩
  have h3 := happ ⟨idx.val % 4, by omega⟩
  have hidx : fin256ToTp4 idx =
      (⟨idx.val / 64 % 4, by omega⟩,
        (⟨idx.val / 16 % 4, by omega⟩,
          (⟨idx.val / 4 % 4, by omega⟩,
            (⟨idx.val % 4, by omega⟩, PUnit.unit)))) := rfl
  rw [hidx]
  by_cases hb1 : (b == 1) = true <;>
    by_cases hs2 : ((s / 2) % 2 == 1) = true <;>
    by_cases hs1 : (s % 2 == 1) = true
  all_goals {
    simp only [hb1, hs2, hs1, ↓reduceIte, Bool.false_eq_true, hs01, hs23, hblk, mapWord4]
    refine Eq.trans ?_ (fin256ToTp4_encode4 _ _ _ _)
    congr 1
    ext
    dsimp only [actWordNat]
    rw [h0, h1, h2, h3]
    simp [hb1, hs2, hs1]
  }

private theorem twirlDiff_actWordNat {piIdx sx sy b : Nat} (hpi : piIdx < 24)
    (i j : Fin 256) :
    twirlDiff (fin256ToTp4 ⟨actWordNat piIdx sx b i.val, actWordNat_lt_256 hpi⟩)
      (fin256ToTp4 ⟨actWordNat piIdx sy b j.val, actWordNat_lt_256 hpi⟩) =
      twirlDiff (fin256ToTp4 i) (fin256ToTp4 j) := by
  obtain ⟨π, hπ⟩ := exists_perm_of_piIdx hpi
  rw [actWordNat_tp4_eq hpi i π hπ, actWordNat_tp4_eq hpi j π hπ]
  dsimp only
  have step_b (u v : TensorPower (Fin 4) 4) :
      twirlDiff (if b == 1 then permEquiv 4 blockSwapPerm u else u)
        (if b == 1 then permEquiv 4 blockSwapPerm v else v) = twirlDiff u v := by
    by_cases hb1 : (b == 1) = true
    · simp [hb1, twirlDiff_blockSwap]
    · simp [hb1]
  rw [step_b]
  have step_s23 (u v : TensorPower (Fin 4) 4) :
      twirlDiff (if (sx / 2) % 2 == 1 then permEquiv 4 swap23Perm u else u)
        (if (sy / 2) % 2 == 1 then permEquiv 4 swap23Perm v else v) = twirlDiff u v := by
    by_cases hx : ((sx / 2) % 2 == 1) = true <;> by_cases hy : ((sy / 2) % 2 == 1) = true <;>
      simp [hx, hy, twirlDiff_left_swap23, twirlDiff_right_swap23]
  rw [step_s23]
  have step_s01 (u v : TensorPower (Fin 4) 4) :
      twirlDiff (if sx % 2 == 1 then permEquiv 4 swap01Perm u else u)
        (if sy % 2 == 1 then permEquiv 4 swap01Perm v else v) = twirlDiff u v := by
    by_cases hx : (sx % 2 == 1) = true <;> by_cases hy : (sy % 2 == 1) = true <;>
      simp [hx, hy, twirlDiff_left_swap01, twirlDiff_right_swap01]
  rw [step_s01, twirlDiff_mapWord4]

private theorem wordProfileNat_eq_of_typeProfile_eq (x y : Fin 256)
    (heq : tensorPowerTypeProfile (a := Fin 4) 4 (fin256ToTp4 x) =
      tensorPowerTypeProfile (a := Fin 4) 4 (fin256ToTp4 y)) :
    wordProfileNat x.val = wordProfileNat y.val := by
  have hcoord (idx : Fin 256) (a : Fin 4) :
      tensorPowerTypeProfile (a := Fin 4) 4 (fin256ToTp4 idx) a =
        (if idx.val / 64 % 4 == a.val then 1 else 0) +
        (if idx.val / 16 % 4 == a.val then 1 else 0) +
        (if idx.val / 4 % 4 == a.val then 1 else 0) +
        (if idx.val % 4 == a.val then 1 else 0) := by
    dsimp only [fin256ToTp4, fin256ToWires4]
    rw [tensorPowerTypeProfile_succ, tensorPowerTypeProfile_succ,
        tensorPowerTypeProfile_succ, tensorPowerTypeProfile_succ]
    have h0 : tensorPowerTypeProfile (a := Fin 4) 0 PUnit.unit a = 0 := by
      unfold tensorPowerTypeProfile
      rw [Fintype.card_subtype]
      simp
    rw [h0, add_zero]
    have eq_fin (n : Nat) (hn : n < 4) : ((⟨n, hn⟩ : Fin 4) = a) ↔ ((n == a.val) = true) := by
      rw [Fin.ext_iff, beq_iff_eq]
    simp only [eq_fin]
    omega
  unfold wordProfileNat
  refine List.map_congr_left fun k hk => ?_
  have hk4 : k < 4 := List.mem_range.mp hk
  have ha := congrFun heq ⟨k, hk4⟩
  rw [hcoord x ⟨k, hk4⟩, hcoord y ⟨k, hk4⟩] at ha
  exact ha

private theorem wordProfileNat_actWordNat_eq_iff {piIdx s1 s2 b : Nat} (hpi : piIdx < 24)
    (i j : Fin 256) :
    (wordProfileNat (actWordNat piIdx s1 b i.val) =
      wordProfileNat (actWordNat piIdx s2 b j.val)) ↔
      wordProfileNat i.val = wordProfileNat j.val := by
  obtain ⟨π, hπ⟩ := exists_perm_of_piIdx hpi
  have happ (a : Fin 4) : applyPerm (perms24.getD piIdx []) a.val = (π a).val := by
    unfold applyPerm; rw [← hπ]; fin_cases a <;> rfl
  have hprof (s : Nat) (idx : Fin 256) (a : Fin 4) :
      (wordProfileNat (actWordNat piIdx s b idx.val)).getD (π a).val 0 =
        (wordProfileNat idx.val).getD a.val 0 := by
    have hget4 (f : Nat → Nat) (m : Nat) (hm : m < 4) :
        ((List.range 4).map f).getD m 0 = f m := by interval_cases m <;> rfl
    have h0 := happ ⟨idx.val / 64 % 4, by omega⟩
    have h1 := happ ⟨idx.val / 16 % 4, by omega⟩
    have h2 := happ ⟨idx.val / 4 % 4, by omega⟩
    have h3 := happ ⟨idx.val % 4, by omega⟩
    have := (π ⟨idx.val / 64 % 4, by omega⟩).isLt
    have := (π ⟨idx.val / 16 % 4, by omega⟩).isLt
    have := (π ⟨idx.val / 4 % 4, by omega⟩).isLt
    have := (π ⟨idx.val % 4, by omega⟩).isLt
    have beq_pi (m : Nat) (hm : m < 4) :
        ((π ⟨m, hm⟩).val == (π a).val) = (m == a.val) := by
      by_cases hma : (⟨m, hm⟩ : Fin 4) = a
      · have hval : m = a.val := congrArg Fin.val hma
        rw [hma, hval]; simp
      · have hne1 : (π ⟨m, hm⟩).val ≠ (π a).val :=
          Fin.val_ne_of_ne (π.injective.ne hma)
        have hne2 : m ≠ a.val := Fin.val_ne_of_ne hma
        simp [hne1, hne2]
    have hact_eq : actWordNat piIdx s b idx.val =
        (let a0 := (π ⟨idx.val / 64 % 4, by omega⟩).val
         let a1 := (π ⟨idx.val / 16 % 4, by omega⟩).val
         let a2 := (π ⟨idx.val / 4 % 4, by omega⟩).val
         let a3 := (π ⟨idx.val % 4, by omega⟩).val
         let u0 := if s % 2 == 1 then a1 else a0
         let u1 := if s % 2 == 1 then a0 else a1
         let u2 := if (s / 2) % 2 == 1 then a3 else a2
         let u3 := if (s / 2) % 2 == 1 then a2 else a3
         if b == 1 then encode4 u2 u3 u0 u1 else encode4 u0 u1 u2 u3) := by
      dsimp only [actWordNat]
      dsimp only at h0 h1 h2 h3
      rw [h0, h1, h2, h3]
    rw [hact_eq]
    unfold wordProfileNat
    rw [hget4 _ (π a).val (π a).isLt, hget4 _ a.val a.isLt]
    have enc4_d0 {u0 u1 u2 u3 : Nat} (_ : u0 < 4) (_ : u1 < 4) (_ : u2 < 4) (_ : u3 < 4) :
        encode4 u0 u1 u2 u3 / 64 % 4 = u0 := by dsimp [encode4]; omega
    have enc4_d1 {u0 u1 u2 u3 : Nat} (_ : u0 < 4) (_ : u1 < 4) (_ : u2 < 4) (_ : u3 < 4) :
        encode4 u0 u1 u2 u3 / 16 % 4 = u1 := by dsimp [encode4]; omega
    have enc4_d2 {u0 u1 u2 u3 : Nat} (_ : u0 < 4) (_ : u1 < 4) (_ : u2 < 4) (_ : u3 < 4) :
        encode4 u0 u1 u2 u3 / 4 % 4 = u2 := by dsimp [encode4]; omega
    have enc4_d3 {u0 u1 u2 u3 : Nat} (_ : u0 < 4) (_ : u1 < 4) (_ : u2 < 4) (_ : u3 < 4) :
        encode4 u0 u1 u2 u3 % 4 = u3 := by dsimp [encode4]; omega
    by_cases hb1 : (b == 1) = true <;>
      by_cases hs2 : ((s / 2) % 2 == 1) = true <;>
      by_cases hs1 : (s % 2 == 1) = true
    all_goals {
      simp only [hb1, hs2, hs1, ↓reduceIte, Bool.false_eq_true]
      rw [enc4_d0 (by omega) (by omega) (by omega) (by omega),
          enc4_d1 (by omega) (by omega) (by omega) (by omega),
          enc4_d2 (by omega) (by omega) (by omega) (by omega),
          enc4_d3 (by omega) (by omega) (by omega) (by omega)]
      simp only [beq_pi]
      try ring
    }
  have hlen (n : Nat) : (wordProfileNat n).length = 4 := rfl
  have hg (n k : Nat) (hk : k < 4) :
      (wordProfileNat n)[k]'(by rw [hlen]; exact hk) = (wordProfileNat n).getD k 0 := by
    match k, hk with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  constructor
  · intro heq
    refine List.ext_getElem (by rw [hlen, hlen]) fun k hk1 _ => ?_
    rw [hg _ k hk1, hg _ k hk1, ← hprof s1 i ⟨k, hk1⟩, ← hprof s2 j ⟨k, hk1⟩, heq]
  · intro heq
    refine List.ext_getElem (by rw [hlen, hlen]) fun k hk1 _ => ?_
    let a : Fin 4 := π.symm ⟨k, hk1⟩
    have hpa : (π a).val = k := by simp [a]
    rw [hg _ k hk1, hg _ k hk1, ← hpa, hprof s1 i a, hprof s2 j a, heq]

/-- Vector of values of `twirlDiff` on the 17 orbit representatives `reps17List`. -/
def orbitVec (k : Fin 17) : ℂ :=
  let rep := reps17List.getD k.val (0, 0)
  have hxc := haar_xcanon_ok
  have hk_lt : rep.1 < 256 ∧ rep.2 < 256 := by
    unfold checkHaarXCanon at hxc
    simp only [Bool.and_eq_true] at hxc
    have hk0 := of_range_all hxc.1.1.2 k.isLt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk0
    have hneq : reps17List.getD k.val (999, 999) ≠ (999, 999) := by
      intro h; rw [h] at hk0; omega
    have heq := getD_eq_of_ne reps17List k.val (999, 999) (0, 0) hneq
    dsimp [rep]; rw [heq]; exact hk0
  twirlDiff (fin256ToTp4 ⟨rep.1, hk_lt.1⟩) (fin256ToTp4 ⟨rep.2, hk_lt.2⟩)

private theorem twirlDiff_entry_eq_sum (i j : Fin 256) :
    twirlDiff (fin256ToTp4 i) (fin256ToTp4 j) =
      ∑ k : Fin 17, (if haarOrbitOpt i.val j.val == k.val + 1 then (1 : ℂ) else 0) * orbitVec k := by
  have hxc := haar_xcanon_ok
  unfold checkHaarXCanon at hxc
  simp only [Bool.and_eq_true] at hxc
  have hxi := of_range_all hxc.2 i.isLt
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hxi
  rcases hxi with ⟨⟨⟨⟨hrx_lt, hpi1_lt⟩, hsx1_lt⟩, hb1_lt⟩, hact_i⟩
  let xc := lookupXCanon i.val
  have hcx_lt999 : canonX7.getD xc.1 999 < 256 := by
    simpa only [decide_eq_true_eq] using of_range_all hxc.1.1.1 hrx_lt
  have hcx_eq999 : canonX7.getD xc.1 0 = canonX7.getD xc.1 999 :=
    getD_eq_of_ne _ _ 999 0 (by omega)
  let cx := canonX7.getD xc.1 0
  have hcx_lt : cx < 256 := by
    dsimp only [cx]; rw [hcx_eq999]; exact hcx_lt999
  have hact_i0 : actWordNat xc.2.1 xc.2.2.1 xc.2.2.2 i.val = cx := by
    dsimp only [cx, xc]; rw [hcx_eq999]; exact hact_i
  let jp := actWordNat xc.2.1 0 xc.2.2.2 j.val
  have hjp_lt : jp < 256 := actWordNat_lt_256 hpi1_lt
  have hpt := of_range_all (of_range_all haar_pair_table_ok hrx_lt) hjp_lt
  let pr := lookupPairRx xc.1 jp
  have horb_def : haarOrbitOpt i.val j.val = pr.1 := rfl
  rw [horb_def]
  have hprof_iff : (wordProfileNat cx = wordProfileNat jp) ↔
      (wordProfileNat i.val = wordProfileNat j.val) := by
    dsimp only [cx, jp, xc] at hact_i0 ⊢
    rw [← hact_i0]
    exact wordProfileNat_actWordNat_eq_iff hpi1_lt i j
  by_cases hprof : wordProfileNat i.val = wordProfileNat j.val
  · have hcx_jp : (wordProfileNat cx != wordProfileNat jp) = false :=
      bne_eq_false_iff_eq.mpr (hprof_iff.mpr hprof)
    dsimp only at hpt
    rw [hcx_jp] at hpt
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hpt
    rcases hpt with ⟨⟨⟨⟨⟨⟨hopt_pos, hopt_le⟩, hpi2_lt⟩, hsx2_lt⟩, hsy2_lt⟩, hb2_lt⟩, hrep1, hrep2⟩
    have hpr_bounds : 0 < pr.1 ∧ pr.1 ≤ 17 := ⟨hopt_pos, hopt_le⟩
    let k0 : Fin 17 := ⟨pr.1 - 1, by omega⟩
    have hsum_k0 : (∑ k : Fin 17,
        (if pr.1 == k.val + 1 then (1 : ℂ) else 0) * orbitVec k) = orbitVec k0 := by
      rw [Finset.sum_eq_single k0]
      · have hk0_eq : (pr.1 == k0.val + 1) = true := beq_iff_eq.mpr (by dsimp [k0]; omega)
        simp [hk0_eq]
      · intro k _ hk_ne
        have hne : pr.1 ≠ k.val + 1 := by
          intro h; apply hk_ne; ext; dsimp [k0]; omega
        simp [beq_false_of_ne hne]
      · intro h; exact absurd (Finset.mem_univ k0) h
    rw [hsum_k0]
    have hstep1 := twirlDiff_actWordNat (sx := xc.2.2.1) (sy := 0) (b := xc.2.2.2) hpi1_lt i j
    have hcx_fin : (⟨actWordNat xc.2.1 xc.2.2.1 xc.2.2.2 i.val, actWordNat_lt_256 hpi1_lt⟩ : Fin 256) =
        ⟨cx, hcx_lt⟩ := Fin.ext hact_i0
    rw [hcx_fin] at hstep1
    rw [← hstep1]
    unfold orbitVec
    dsimp only [k0]
    let rep := reps17List.getD (pr.1 - 1) (0, 0)
    have hrep_lt : rep.1 < 256 ∧ rep.2 < 256 := by
      have hk0_chk := of_range_all hxc.1.1.2 (show pr.1 - 1 < 17 by omega)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk0_chk
      have hneq : reps17List.getD (pr.1 - 1) (999, 999) ≠ (999, 999) := by
        intro h; rw [h] at hk0_chk; omega
      have heq := getD_eq_of_ne reps17List (pr.1 - 1) (999, 999) (0, 0) hneq
      dsimp [rep]; rw [heq]; exact hk0_chk
    have hstep2 := twirlDiff_actWordNat (sx := pr.2.2.1) (sy := pr.2.2.2.1) (b := pr.2.2.2.2)
      hpi2_lt ⟨rep.1, hrep_lt.1⟩ ⟨rep.2, hrep_lt.2⟩
    have hr1_fin : (⟨actWordNat pr.2.1 pr.2.2.1 pr.2.2.2.2 rep.1, actWordNat_lt_256 hpi2_lt⟩ : Fin 256) =
        ⟨cx, hcx_lt⟩ := Fin.ext hrep1
    have hr2_fin : (⟨actWordNat pr.2.1 pr.2.2.2.1 pr.2.2.2.2 rep.2, actWordNat_lt_256 hpi2_lt⟩ : Fin 256) =
        ⟨jp, hjp_lt⟩ := Fin.ext hrep2
    rw [hr1_fin, hr2_fin] at hstep2
    exact hstep2
  · have hcx_jp : (wordProfileNat cx != wordProfileNat jp) = true :=
      bne_iff_ne.mpr (mt hprof_iff.mp hprof)
    dsimp only at hpt
    rw [hcx_jp] at hpt
    simp only [↓reduceIte, beq_iff_eq] at hpt
    rw [hpt]
    have hrhs0 : (∑ k : Fin 17, (if (0 : Nat) == k.val + 1 then (1 : ℂ) else 0) * orbitVec k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have hne : (0 : Nat) ≠ k.val + 1 := by omega
      simp [beq_false_of_ne hne]
    rw [hrhs0]
    exact twirlDiff_eq_zero_of_typeProfile_ne _ _
      (mt (wordProfileNat_eq_of_typeProfile_eq i j) hprof)

private def traceSigmaPerm : Fin 3 → Equiv.Perm (Fin 4)
  | 0 => 1
  | 1 => swap02Perm
  | 2 => blockSwapPerm

private theorem traceSigmaPerm_sq (r : Fin 3) :
    traceSigmaPerm r * traceSigmaPerm r = 1 := by
  fin_cases r
  · simp [traceSigmaPerm]
  · exact involutions_sq_one.2.2.1
  · exact involutions_sq_one.2.2.2

private theorem applyTraceSigma_lt_256 (r x : Nat) : applyTraceSigma r x < 256 := by
  unfold applyTraceSigma
  split_ifs <;> dsimp [encode4] <;> omega

private theorem permEquiv_traceSigma_eq (r : Fin 3) (x : Fin 256) :
    permEquiv (a := Fin 4) 4 (traceSigmaPerm r) (fin256ToTp4 x) =
      fin256ToTp4 ⟨applyTraceSigma r.val x.val, applyTraceSigma_lt_256 r.val x.val⟩ := by
  rw [permEquiv4_coords]
  fin_cases r
  · dsimp only [traceSigmaPerm]
    dsimp [applyTraceSigma, fin256ToTp4, fin256ToWires4]
    exact (fin256ToTp4_encode4 _ _ _ _).symm
  · have c0 : swap02Perm⁻¹ 0 = 2 := by decide
    have c1 : swap02Perm⁻¹ 1 = 1 := by decide
    have c2 : swap02Perm⁻¹ 2 = 0 := by decide
    have c3 : swap02Perm⁻¹ 3 = 3 := by decide
    dsimp only [traceSigmaPerm]
    rw [c0, c1, c2, c3]
    dsimp [applyTraceSigma, fin256ToTp4, fin256ToWires4]
    exact (fin256ToTp4_encode4 _ _ _ _).symm
  · have c0 : blockSwapPerm⁻¹ 0 = 2 := by decide
    have c1 : blockSwapPerm⁻¹ 1 = 3 := by decide
    have c2 : blockSwapPerm⁻¹ 2 = 0 := by decide
    have c3 : blockSwapPerm⁻¹ 3 = 1 := by decide
    dsimp only [traceSigmaPerm]
    rw [c0, c1, c2, c3]
    dsimp [applyTraceSigma, fin256ToTp4, fin256ToWires4]
    exact (fin256ToTp4_encode4 _ _ _ _).symm

private theorem diagK_fin256_eq (i j : Fin 256) :
    diagK (fin256ToTp4 i) (fin256ToTp4 j) = (diagKInt i.val j.val : ℂ) := by
  have hij_iff : (fin256ToTp4 i = fin256ToTp4 j) ↔ (i.val == j.val) = true := by
    constructor
    · intro h
      have hi := congrArg tp4ToFin256 h
      rw [tp4ToFin256_fin256ToTp4, tp4ToFin256_fin256ToTp4] at hi
      exact beq_iff_eq.mpr (congrArg Fin.val hi)
    · intro h
      have hij : i = j := Fin.ext (beq_iff_eq.mp h)
      rw [hij]
  have h1 : ((fin256ToTp4 i).1 = (fin256ToTp4 i).2.1) ↔
      (i.val / 64 % 4 == i.val / 16 % 4) = true := by
    dsimp only [fin256ToTp4, fin256ToWires4]
    rw [Fin.ext_iff, beq_iff_eq]
  have h2 : ((fin256ToTp4 i).2.2.1 = (fin256ToTp4 i).2.2.2.1) ↔
      (i.val / 4 % 4 == i.val % 4) = true := by
    dsimp only [fin256ToTp4, fin256ToWires4]
    rw [Fin.ext_iff, beq_iff_eq]
  unfold diagK diagKInt
  by_cases hc : ((i.val == j.val) && (i.val / 64 % 4 == i.val / 16 % 4) &&
      (i.val / 4 % 4 == i.val % 4)) = true
  · have hc' := hc
    simp only [Bool.and_eq_true] at hc'
    have hprop : fin256ToTp4 i = fin256ToTp4 j ∧
        (fin256ToTp4 i).1 = (fin256ToTp4 i).2.1 ∧
        (fin256ToTp4 i).2.2.1 = (fin256ToTp4 i).2.2.2.1 :=
      ⟨hij_iff.mpr hc'.1.1, h1.mpr hc'.1.2, h2.mpr hc'.2⟩
    rw [if_pos hprop, if_pos hc]
    norm_num
  · have hnot : ¬(fin256ToTp4 i = fin256ToTp4 j ∧
        (fin256ToTp4 i).1 = (fin256ToTp4 i).2.1 ∧
        (fin256ToTp4 i).2.2.1 = (fin256ToTp4 i).2.2.2.1) := by
      rintro ⟨a, b, c⟩
      apply hc
      simp [hij_iff.mp a, h1.mp b, h2.mp c]
    rw [if_neg hnot, if_neg hc]
    norm_num

private theorem wCand_fin256_eq (i j : Fin 256) :
    wCand (fin256ToTp4 i) (fin256ToTp4 j) = (wCandInt840 i.val j.val : ℂ) / 840 := by
  unfold wCand wCandInt840
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, permMat4_apply]
  have hcond (σ : Equiv.Perm (Fin 4)) :
      (permEquiv (a := Fin 4) 4 σ (fin256ToTp4 i) = fin256ToTp4 j) ↔
        ((i.val / 64 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
            (applyPerm (permToList4 σ) 0) 0 &&
          i.val / 16 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
            (applyPerm (permToList4 σ) 1) 0 &&
          i.val / 4 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
            (applyPerm (permToList4 σ) 2) 0 &&
          i.val % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
            (applyPerm (permToList4 σ) 3) 0) = true) := by
    rw [← (tensorPowerEquiv 4).injective.eq_iff]
    have hp (t : Fin 4) :
        tensorPowerEquiv 4 (permEquiv 4 σ (fin256ToTp4 i)) t =
          tensorPowerEquiv 4 (fin256ToTp4 i) (σ⁻¹ t) := by
      rw [tensorPowerEquiv_permEquiv]
    have hlhs : (tensorPowerEquiv 4 (permEquiv 4 σ (fin256ToTp4 i)) =
        tensorPowerEquiv 4 (fin256ToTp4 j)) ↔
        (∀ s : Fin 4, tensorPowerEquiv 4 (fin256ToTp4 i) s =
          tensorPowerEquiv 4 (fin256ToTp4 j) (σ s)) := by
      constructor
      · intro h s
        have hs := congrFun h (σ s)
        have hinv : σ⁻¹ (σ s) = s := σ.symm_apply_apply s
        rw [hp (σ s), hinv] at hs
        exact hs
      · intro h
        funext t
        have hinv : σ (σ⁻¹ t) = t := σ.apply_symm_apply t
        rw [hp t, h (σ⁻¹ t), hinv]
    have h4 : (∀ s : Fin 4, tensorPowerEquiv 4 (fin256ToTp4 i) s =
        tensorPowerEquiv 4 (fin256ToTp4 j) (σ s)) ↔
        (tensorPowerEquiv 4 (fin256ToTp4 i) 0 = tensorPowerEquiv 4 (fin256ToTp4 j) (σ 0) ∧
         tensorPowerEquiv 4 (fin256ToTp4 i) 1 = tensorPowerEquiv 4 (fin256ToTp4 j) (σ 1) ∧
         tensorPowerEquiv 4 (fin256ToTp4 i) 2 = tensorPowerEquiv 4 (fin256ToTp4 j) (σ 2) ∧
         tensorPowerEquiv 4 (fin256ToTp4 i) 3 = tensorPowerEquiv 4 (fin256ToTp4 j) (σ 3)) :=
      ⟨fun h => ⟨h 0, h 1, h 2, h 3⟩, fun ⟨h0, h1, h2, h3⟩ s => by fin_cases s <;> assumption⟩
    rw [hlhs, h4]
    have hcol (t : Fin 4) :
        [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm (permToList4 σ) t.val) 0 =
          (tensorPowerEquiv 4 (fin256ToTp4 j) (σ t)).val := by
      have hap : applyPerm (permToList4 σ) t.val = (σ t).val := by
        fin_cases t <;> rfl
      rw [hap]
      generalize σ t = s
      fin_cases s <;> rfl
    have hcol0 : [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
        (applyPerm (permToList4 σ) 0) 0 = (tensorPowerEquiv 4 (fin256ToTp4 j) (σ 0)).val := hcol 0
    have hcol1 : [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
        (applyPerm (permToList4 σ) 1) 0 = (tensorPowerEquiv 4 (fin256ToTp4 j) (σ 1)).val := hcol 1
    have hcol2 : [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
        (applyPerm (permToList4 σ) 2) 0 = (tensorPowerEquiv 4 (fin256ToTp4 j) (σ 2)).val := hcol 2
    have hcol3 : [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
        (applyPerm (permToList4 σ) 3) 0 = (tensorPowerEquiv 4 (fin256ToTp4 j) (σ 3)).val := hcol 3
    rw [hcol0, hcol1, hcol2, hcol3]
    simp only [Bool.and_eq_true, beq_iff_eq, Fin.ext_iff]
    dsimp [fin256ToTp4, fin256ToWires4]
    tauto
  let F : List Nat → ℂ := fun p =>
    if (i.val / 64 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm p 0) 0 &&
        i.val / 16 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm p 1) 0 &&
        i.val / 4 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm p 2) 0 &&
        i.val % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm p 3) 0) = true then
      (weingartenNum13440 p : ℂ)
    else 0
  have hterm (σ : Equiv.Perm (Fin 4)) :
      (permWeingartenNum σ : ℂ) *
        (if permEquiv 4 σ (fin256ToTp4 i) = fin256ToTp4 j then (1 : ℂ) else 0) =
        F (permToList4 σ) := by
    dsimp only [F]
    rw [← (permWeingarten_symmetries σ).2.2.2.2.2.2]
    by_cases h : permEquiv 4 σ (fin256ToTp4 i) = fin256ToTp4 j
    · rw [if_pos h, if_pos ((hcond σ).mp h), mul_one]
    · rw [if_neg h, if_neg (mt (hcond σ).mpr h), mul_zero]
  simp_rw [hterm]
  rw [sum_perm_eq_perms24_sum F]
  have hcast : ((perms24.map fun p =>
      if (i.val / 64 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
            (applyPerm p 0) 0 &&
          i.val / 16 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
            (applyPerm p 1) 0 &&
          i.val / 4 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
            (applyPerm p 2) 0 &&
          i.val % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
            (applyPerm p 3) 0) then
        weingartenNum13440 p
      else 0).sum : ℂ) = (perms24.map F).sum := by
    rw [Int.cast_list_sum, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    dsimp [F]
    cases hc : (i.val / 64 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm p 0) 0 &&
        i.val / 16 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm p 1) 0 &&
        i.val / 4 % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm p 2) 0 &&
        i.val % 4 == [j.val / 64 % 4, j.val / 16 % 4, j.val / 4 % 4, j.val % 4].getD
          (applyPerm p 3) 0) <;> simp
  rw [hcast]
  ring

private theorem twirlDiff_trace_eq_zero (r : Fin 3) :
    (permutationMatrix (a := Fin 4) 4 (traceSigmaPerm r) * twirlDiff).trace = 0 := by
  set σ := traceSigmaPerm r
  set Pσ := permutationMatrix (a := Fin 4) 4 σ
  have htwirl_tr : (Pσ * unitaryTwirl (a := Fin 4) 4 diagK).trace = (Pσ * diagK).trace := by
    have hf := unitaryTwirl_integrand_integrable (a := Fin 4) 4 diagK
    simp only [Matrix.trace, Matrix.diag_apply, Pσ, permMat4_mul_left]
    unfold unitaryTwirl
    simp_rw [integral_cMatrix_entry hf]
    have hint_w (w : TensorPower (Fin 4) 4) :
        Integrable (fun U => unitaryTwirlIntegrand (a := Fin 4) 4 diagK U (permEquiv 4 σ w) w)
          (unitaryHaarMeasure (a := Fin 4)) :=
      (cMatrixEntryCLM (ι := TensorPower (Fin 4) 4) (permEquiv 4 σ w) w).integrable_comp hf
    rw [← MeasureTheory.integral_finsetSum _ fun w _ => hint_w w]
    have hpt (U : Matrix.unitaryGroup (Fin 4) ℂ) :
        (∑ w : TensorPower (Fin 4) 4,
          unitaryTwirlIntegrand (a := Fin 4) 4 diagK U (permEquiv 4 σ w) w) =
        ∑ w : TensorPower (Fin 4) 4, diagK (permEquiv 4 σ w) w := by
      have htrP (M : CMatrix (TensorPower (Fin 4) 4)) :
          (∑ w : TensorPower (Fin 4) 4, M (permEquiv 4 σ w) w) = (Pσ * M).trace := by
        simp only [Matrix.trace, Matrix.diag_apply, Pσ, permMat4_mul_left]
      rw [htrP, htrP]
      unfold unitaryTwirlIntegrand
      set U4 : CMatrix (TensorPower (Fin 4) 4) :=
        (unitaryTensorPowerMatrix U 4 : CMatrix (TensorPower (Fin 4) 4))
      have hcomm : Pσ * U4 = U4 * Pσ :=
        permutationMatrix_mul_unitaryTensorPowerMatrix (a := Fin 4) U 4 σ
      have hU4_star : star U4 * U4 = 1 :=
        (Matrix.mem_unitaryGroup_iff'.mp (unitaryTensorPowerMatrix U 4).2)
      calc
        (Pσ * (U4 * diagK * star U4)).trace
            = ((Pσ * U4) * (diagK * star U4)).trace := by simp only [Matrix.mul_assoc]
        _ = (U4 * (Pσ * diagK * star U4)).trace := by rw [hcomm]; simp only [Matrix.mul_assoc]
        _ = ((Pσ * diagK * star U4) * U4).trace := Matrix.trace_mul_comm _ _
        _ = (Pσ * diagK * (star U4 * U4)).trace := by simp only [Matrix.mul_assoc]
        _ = (Pσ * diagK).trace := by rw [hU4_star, Matrix.mul_one]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const]
    simp [probReal_univ]
  unfold twirlDiff
  rw [Matrix.mul_sub, Matrix.trace_sub, htwirl_tr, sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag_apply, Pσ, permMat4_mul_left]
  rw [← tp4Equiv.symm.sum_comp, ← tp4Equiv.symm.sum_comp]
  change (∑ x : Fin 256, diagK (permEquiv 4 (traceSigmaPerm r) (fin256ToTp4 x)) (fin256ToTp4 x)) =
      ∑ x : Fin 256, wCand (permEquiv 4 (traceSigmaPerm r) (fin256ToTp4 x)) (fin256ToTp4 x)
  simp_rw [permEquiv_traceSigma_eq r, diagK_fin256_eq, wCand_fin256_eq, ← Finset.sum_div]
  have ht3 := of_range_all haar_traces3_ok r.isLt
  simp only [beq_iff_eq] at ht3
  rw [sumBelow_eq_sum_range, sumBelow_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at ht3
  have ht3_c : ((840 : ℂ) * ∑ x : Fin 256, (diagKInt (applyTraceSigma r.val x.val) x.val : ℂ)) =
      ∑ x : Fin 256, (wCandInt840 (applyTraceSigma r.val x.val) x.val : ℂ) := by
    have h := congrArg (Int.cast (R := ℂ)) ht3
    push_cast at h
    rw [Finset.mul_sum]
    exact h
  rw [← ht3_c]
  ring

private def hadamard4U : Matrix.unitaryGroup (Fin 4) ℂ :=
  ⟨fun a b => (1 / 2 : ℂ) * (h4Bit a.val b.val : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_apply, h4Bit, map_ofNat] <;> norm_num⟩

private def hadamard4SignTp : CMatrix (TensorPower (Fin 4) 4) :=
  fun x y => (h4Sign4 (tp4ToFin256 x).val (tp4ToFin256 y).val : ℂ)

private theorem hadamard4SignTp_commutes_twirlDiff :
    hadamard4SignTp * twirlDiff = twirlDiff * hadamard4SignTp := by
  have hrel : (unitaryTensorPowerMatrix hadamard4U 4 : CMatrix _) =
      (1 / 16 : ℂ) • hadamard4SignTp := by
    ext x y
    rw [unitaryTensorPowerMatrix_apply_eq_fin_prod, Fin.prod_univ_four]
    rcases x with ⟨x0, x1, x2, x3, ⟨⟩⟩
    rcases y with ⟨y0, y1, y2, y3, ⟨⟩⟩
    simp only [tp4_coord0, tp4_coord1, tp4_coord2, tp4_coord3, hadamard4U,
      Matrix.smul_apply, smul_eq_mul, hadamard4SignTp, tp4ToFin256, wires4ToFin256, h4Sign4]
    have enc_div (a0 a1 a2 a3 : Fin 4) :
        encode4 a0.val a1.val a2.val a3.val / 64 % 4 = a0.val ∧
        encode4 a0.val a1.val a2.val a3.val / 16 % 4 = a1.val ∧
        encode4 a0.val a1.val a2.val a3.val / 4 % 4 = a2.val ∧
        encode4 a0.val a1.val a2.val a3.val % 4 = a3.val := by dsimp [encode4]; omega
    rcases enc_div x0 x1 x2 x3 with ⟨ex0, ex1, ex2, ex3⟩
    rcases enc_div y0 y1 y2 y3 with ⟨ey0, ey1, ey2, ey3⟩
    rw [ex0, ex1, ex2, ex3, ey0, ey1, ey2, ey3]
    push_cast
    ring
  have hcomm := twirlDiff_commutes hadamard4U
  rw [hrel, Matrix.smul_mul, Matrix.mul_smul] at hcomm
  have h16 := congrArg (fun M => (16 : ℂ) • M) hcomm
  dsimp only at h16
  rw [smul_smul, smul_smul] at h16
  norm_num at h16
  exact h16

private theorem haar_linear_eq_zero (r : Fin 17) :
    (∑ k : Fin 17, (haarCoeffInt r.val k.val : ℂ) * orbitVec k) = 0 := by
  by_cases hr3 : r.val < 3
  · let r3 : Fin 3 := ⟨r.val, hr3⟩
    have htr := twirlDiff_trace_eq_zero r3
    simp only [Matrix.trace, Matrix.diag_apply, permMat4_mul_left] at htr
    rw [← tp4Equiv.symm.sum_comp] at htr
    change (∑ x : Fin 256, twirlDiff (permEquiv 4 (traceSigmaPerm r3) (fin256ToTp4 x))
        (fin256ToTp4 x)) = 0 at htr
    simp_rw [permEquiv_traceSigma_eq r3, twirlDiff_entry_eq_sum] at htr
    rw [Finset.sum_comm] at htr
    rw [← htr]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    unfold haarCoeffInt
    rw [if_pos hr3, sumBelow_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    push_cast
    rfl
  · have hm_lt : r.val - 3 < 14 := by omega
    have hxc := haar_xcanon_ok
    unfold checkHaarXCanon at hxc
    simp only [Bool.and_eq_true] at hxc
    have huv_chk := of_range_all hxc.1.2 hm_lt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at huv_chk
    let uv := h4Pairs14List.getD (r.val - 3) (0, 0)
    have huv_lt : uv.1 < 256 ∧ uv.2 < 256 := by
      have hneq : h4Pairs14List.getD (r.val - 3) (999, 999) ≠ (999, 999) := by
        intro h; rw [h] at huv_chk; omega
      have heq := getD_eq_of_ne h4Pairs14List (r.val - 3) (999, 999) (0, 0) hneq
      dsimp [uv]; rw [heq]; exact huv_chk
    let u : Fin 256 := ⟨uv.1, huv_lt.1⟩
    let v : Fin 256 := ⟨uv.2, huv_lt.2⟩
    have hcomm := congrFun (congrFun hadamard4SignTp_commutes_twirlDiff
      (fin256ToTp4 u)) (fin256ToTp4 v)
    have hdiff : (hadamard4SignTp * twirlDiff) (fin256ToTp4 u) (fin256ToTp4 v) -
        (twirlDiff * hadamard4SignTp) (fin256ToTp4 u) (fin256ToTp4 v) = 0 :=
      sub_eq_zero.mpr hcomm
    simp only [Matrix.mul_apply] at hdiff
    rw [← tp4Equiv.symm.sum_comp, ← tp4Equiv.symm.sum_comp] at hdiff
    change (∑ x : Fin 256, hadamard4SignTp (fin256ToTp4 u) (fin256ToTp4 x) *
          twirlDiff (fin256ToTp4 x) (fin256ToTp4 v)) -
        (∑ x : Fin 256, twirlDiff (fin256ToTp4 u) (fin256ToTp4 x) *
          hadamard4SignTp (fin256ToTp4 x) (fin256ToTp4 v)) = 0 at hdiff
    have hh4 (a b : Fin 256) :
        hadamard4SignTp (fin256ToTp4 a) (fin256ToTp4 b) = (h4Sign4 a.val b.val : ℂ) := by
      simp [hadamard4SignTp]
    simp_rw [hh4, twirlDiff_entry_eq_sum, Finset.mul_sum, Finset.sum_mul] at hdiff
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Fin 256)),
        ← Finset.sum_sub_distrib] at hdiff
    rw [← hdiff]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold haarCoeffInt
    rw [if_neg hr3]
    dsimp only
    rw [sumBelow_eq_sum_range, sumBelow_eq_sum_range,
        ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    push_cast
    rw [sub_mul, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    · refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> ring

/-- Exact fourth-moment Haar twirl identity `unitaryTwirl 4 diagK = wCand` on `Fin 4`. -/
theorem unitaryTwirl_diagK_eq_wCand :
    unitaryTwirl (a := Fin 4) 4 diagK = wCand := by
  suffices hzero : twirlDiff = 0 by
    exact sub_eq_zero.mp hzero
  have horb0 : ∀ k0 : Fin 17, orbitVec k0 = 0 := by
    intro k0
    have hci := haar_coeff_and_inv17_ok
    unfold checkHaarCoeffAndInv17 at hci
    simp only [Bool.and_eq_true] at hci
    have hcoeff_eq (r k : Fin 17) :
        haarCoeffInt r.val k.val = (haarCoeffMat17List.getD r.val []).getD k.val 0 := by
      have hc := of_range_all (of_range_all hci.1 r.isLt) k.isLt
      simp only [beq_iff_eq] at hc
      have hneq : (haarCoeffMat17List.getD r.val []).getD k.val 999999 ≠ 999999 := by
        fin_cases r <;> fin_cases k <;> decide
      exact hc.trans (getD_eq_of_ne _ _ 999999 0 hneq).symm
    have hsum0 : (∑ r : Fin 17,
        ((haarInvMat17List.getD k0.val []).getD r.val 0 : ℂ) *
          ∑ k : Fin 17, (haarCoeffInt r.val k.val : ℂ) * orbitVec k) = 0 := by
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [haar_linear_eq_zero r, mul_zero]
    simp_rw [Finset.mul_sum, ← mul_assoc] at hsum0
    rw [Finset.sum_comm] at hsum0
    have hsum_lhs : (∑ k : Fin 17,
        ∑ r : Fin 17,
          ((haarInvMat17List.getD k0.val []).getD r.val 0 : ℂ) *
            (haarCoeffInt r.val k.val : ℂ) * orbitVec k) =
        (10080 : ℂ) * orbitVec k0 := by
      trans (∑ k : Fin 17, (if k0 = k then (10080 : ℂ) else 0) * orbitVec k)
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_mul]
        congr 1
        have hinv := of_range_all (of_range_all hci.2 k0.isLt) k.isLt
        simp only [beq_iff_eq] at hinv
        rw [sumBelow_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hinv
        simp_rw [hcoeff_eq]
        have hinv_c := congrArg (Int.cast (R := ℂ)) hinv
        push_cast at hinv_c
        rw [hinv_c]
        by_cases hk : k0 = k
        · subst hk; simp
        · simp [hk, Fin.val_ne_of_ne hk]
      · rw [Finset.sum_eq_single k0]
        · simp
        · intro k _ hk; simp [hk.symm]
        · intro h; exact absurd (Finset.mem_univ k0) h
    rw [hsum_lhs] at hsum0
    exact (mul_eq_zero.mp hsum0).resolve_left (by norm_num)
  ext x y
  rw [← fin256ToTp4_tp4ToFin256 x, ← fin256ToTp4_tp4ToFin256 y]
  rw [twirlDiff_entry_eq_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [horb0 k, mul_zero]

/-! ### Section 3c: Physical channels `Δ_U`, `Λ`, `E_{p,U}`, `M_p` and their Choi integrals -/

private theorem posSemidef_smul_real_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : CMatrix ι} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (((c : ℝ) : ℂ) • M).PosSemidef := by
  let S : CMatrix ι := (Real.sqrt c : ℂ) • (1 : CMatrix ι)
  have hEq : (((c : ℝ) : ℂ) • M) = S * M * Sᴴ := by
    ext i j
    simp only [S, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_apply, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    have hsq : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = (c : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt hc
    rw [← mul_assoc, hsq]
  rw [hEq]
  exact hM.mul_mul_conjTranspose_same S

/-- Convex combination `(1 - p) Φ₀ + p Φ₁` of two channels on `Fin 4` (`0 ≤ p ≤ 1`). -/
def convexChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Φ₀ Φ₁ : Channel (Fin 4) (Fin 4)) : Channel (Fin 4) (Fin 4) where
  map := ((1 - p : ℝ) : ℂ) • Φ₀.map + (p : ℂ) • Φ₁.map
  completelyPositive := by
    change (MatrixMap.choi (((1 - p : ℝ) : ℂ) • Φ₀.map + (p : ℂ) • Φ₁.map)).PosSemidef
    have hchoi : MatrixMap.choi (((1 - p : ℝ) : ℂ) • Φ₀.map + (p : ℂ) • Φ₁.map) =
        ((1 - p : ℝ) : ℂ) • MatrixMap.choi Φ₀.map + (p : ℂ) • MatrixMap.choi Φ₁.map := by
      ext ij kl
      simp [MatrixMap.choi, LinearMap.add_apply, LinearMap.smul_apply]
    rw [hchoi]
    exact PosSemidef.add
      (posSemidef_smul_real_nonneg Φ₀.completelyPositive (by linarith))
      (posSemidef_smul_real_nonneg Φ₁.completelyPositive hp0)
  tracePreserving := by
    intro X
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Matrix.trace_add, Matrix.trace_smul,
      Φ₀.tracePreserving X, Φ₁.tracePreserving X, smul_eq_mul]
    push_cast
    ring
  mapsPositive := by
    apply MatrixMap.isCompletelyPositive_mapsPositive
    change (MatrixMap.choi (((1 - p : ℝ) : ℂ) • Φ₀.map + (p : ℂ) • Φ₁.map)).PosSemidef
    have hchoi : MatrixMap.choi (((1 - p : ℝ) : ℂ) • Φ₀.map + (p : ℂ) • Φ₁.map) =
        ((1 - p : ℝ) : ℂ) • MatrixMap.choi Φ₀.map + (p : ℂ) • MatrixMap.choi Φ₁.map := by
      ext ij kl
      simp [MatrixMap.choi, LinearMap.add_apply, LinearMap.smul_apply]
    rw [hchoi]
    exact PosSemidef.add
      (posSemidef_smul_real_nonneg Φ₀.completelyPositive (by linarith))
      (posSemidef_smul_real_nonneg Φ₁.completelyPositive hp0)

/-- Rank-one dephasing channel `Δ_U` in the orthonormal basis given by `U ∈ U(4)`. -/
def dephasingChannel (U : Matrix.unitaryGroup (Fin 4) ℂ) : Channel (Fin 4) (Fin 4) where
  map := MatrixMap.ofKraus (basisProjection (U : CMatrix (Fin 4)))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using
      hidden_basis_kraus_complete (U : CMatrix (Fin 4)) U.property.1 U.property.2)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

/-- Compatibility with `ICO.BudgetContinuity.hidden`: `(dephasingChannel U).prod id = hidden U`. -/
theorem dephasingChannel_prod_id_eq_hidden {M : Type} [Fintype M] [DecidableEq M]
    (U : Matrix.unitaryGroup (Fin 4) ℂ) :
    (dephasingChannel U).prod (Channel.idChannel M) =
      ICO.BudgetContinuity.hidden (A := Fin 4) (M := M) U := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  ext Y ⟨ao, m⟩ ⟨ao', m'⟩
  change (MatrixMap.kron (dephasingChannel U).map (Channel.idChannel M).map Y) (ao, m) (ao', m') =
    (ICO.AllChannelDilation.oracleMap (basisProjection (U : CMatrix (Fin 4))) Y) (ao, m) (ao', m')
  rw [MatrixMap.kron_idChannel_apply_slice]
  dsimp [dephasingChannel, ICO.AllChannelDilation.oracleMap, MatrixMap.ofKraus]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  symm
  refine Finset.sum_congr rfl fun a₁ _ => ?_
  rw [Finset.sum_eq_single m']
  · simp only [↓reduceIte, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun a₂ _ => ?_
    rw [Finset.sum_eq_single m]
    · simp
    · intro m₂ _ hm₂; simp [hm₂.symm]
    · intro h; exact absurd (Finset.mem_univ m) h
  · intro m₁ _ hm₁; simp [hm₁.symm]
  · intro h; exact absurd (Finset.mem_univ m') h

/-- Depolarizing model channel `Λ = (id + 4 Ω) / 5 = (1 / 5) id + (4 / 5) Ω` on `Fin 4`. -/
def modelChannel : Channel (Fin 4) (Fin 4) :=
  convexChannel (4 / 5) (by norm_num) (by norm_num)
    (Channel.idChannel (Fin 4)) (ICO.RecordingDepolarizing.depolarizing (α := Fin 4))

/-- Noise-interpolated rank-one dephasing channel `E_{p,U} = (1 - p) id + p Δ_U`. -/
def noisyDephasingChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (U : Matrix.unitaryGroup (Fin 4) ℂ) : Channel (Fin 4) (Fin 4) :=
  convexChannel p hp0 hp1 (Channel.idChannel (Fin 4)) (dephasingChannel U)

/-- Noise-interpolated depolarizing model channel `M_p = (1 - p) id + p Λ`. -/
def noisyModelChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Channel (Fin 4) (Fin 4) :=
  convexChannel p hp0 hp1 (Channel.idChannel (Fin 4)) modelChannel

private theorem choiOneCopy_modelChannel_entry (ai ao ai' ao' : Fin 4) :
    choiOneCopy modelChannel (ai, ao) (ai', ao') =
      (jLambdaScaled5 (ai.val * 4 + ao.val) (ai'.val * 4 + ao'.val) : ℂ) / 5 := by
  change modelChannel.map (Matrix.single ai ai' (1 : ℂ)) ao ao' = _
  dsimp [modelChannel, convexChannel]
  simp only [ICO.RecordingDepolarizing.depolarizing_entry, Fintype.card_fin]
  have hid : (Channel.idChannel (Fin 4)).map (Matrix.single ai ai' (1 : ℂ)) ao ao' =
      if ai = ao ∧ ai' = ao' then 1 else 0 := by
    change (MatrixMap.ofKraus (fun (_ : Unit) => (1 : CMatrix (Fin 4)))
      (Matrix.single ai ai' (1 : ℂ))) ao ao' = _
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Fintype.univ_punit,
      Finset.sum_singleton, Matrix.single]
    by_cases h1 : ai = ao <;> by_cases h2 : ai' = ao' <;> simp [h1, h2]
  have htr : (Matrix.single ai ai' (1 : ℂ)).trace = if ai = ai' then 1 else 0 := by
    by_cases h : ai = ai'
    · subst h; simp [Matrix.trace, Matrix.diag_apply, Matrix.single]
    · simp [Matrix.trace, Matrix.diag_apply, Matrix.single, h, Ne.symm h]
  rw [hid, htr]
  unfold jLambdaScaled5
  have hd1 : (ai.val * 4 + ao.val) / 4 % 4 = ai.val := by omega
  have hd2 : (ai.val * 4 + ao.val) % 4 = ao.val := by omega
  have hd3 : (ai'.val * 4 + ao'.val) / 4 % 4 = ai'.val := by omega
  have hd4 : (ai'.val * 4 + ao'.val) % 4 = ao'.val := by omega
  rw [hd1, hd2, hd3, hd4]
  fin_cases ai <;> fin_cases ao <;> fin_cases ai' <;> fin_cases ao' <;> norm_num

/-- Two-copy Choi matrix of `modelChannel` equals `w1Matrix`. -/
theorem choiTwoCopy_modelChannel :
    choiTwoCopy modelChannel = w1Matrix := by
  ext ⟨ai, ao, bi, bo⟩ ⟨ai', ao', bi', bo'⟩
  simp only [choiTwoCopy, twoCopyKron, choiOneCopy_modelChannel_entry, w1Matrix,
    w1Scaled4200, wires4ToFin256]
  have hu : encode4 ai.val ao.val bi.val bo.val / 16 = ai.val * 4 + ao.val ∧
      encode4 ai.val ao.val bi.val bo.val % 16 = bi.val * 4 + bo.val := by dsimp [encode4]; omega
  have hv : encode4 ai'.val ao'.val bi'.val bo'.val / 16 = ai'.val * 4 + ao'.val ∧
      encode4 ai'.val ao'.val bi'.val bo'.val % 16 = bi'.val * 4 + bo'.val := by dsimp [encode4]; omega
  rw [hu.1, hu.2, hv.1, hv.2]
  push_cast
  ring

private theorem choiOneCopy_dephasing_entry (U : Matrix.unitaryGroup (Fin 4) ℂ)
    (ai ao ai' ao' : Fin 4) :
    choiOneCopy (dephasingChannel U) (ai, ao) (ai', ao') =
      ∑ k : Fin 4,
        ((U : CMatrix (Fin 4)) ai' k * (U : CMatrix (Fin 4)) ao k) *
          star ((U : CMatrix (Fin 4)) ai k * (U : CMatrix (Fin 4)) ao' k) := by
  change (dephasingChannel U).map (Matrix.single ai ai' (1 : ℂ)) ao ao' = _
  dsimp [dephasingChannel, MatrixMap.ofKraus]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hbp (x y : Fin 4) :
      basisProjection (U : CMatrix (Fin 4)) k x y =
        (U : CMatrix (Fin 4)) x k * star ((U : CMatrix (Fin 4)) y k) := by
    unfold basisProjection
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single k]
      · simp [Matrix.single]
      · intro z _ hzk; simp [Matrix.single, hzk.symm]
      · intro h; exact absurd (Finset.mem_univ k) h
    · intro z _ hzk
      have hz0 : (∑ w : Fin 4, (U : CMatrix (Fin 4)) x w * Matrix.single k k (1 : ℂ) w z) = 0 :=
        Finset.sum_eq_zero fun w _ => by simp [Matrix.single, hzk.symm]
      rw [hz0, zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [basisProjection_hermitian]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single ai']
  · rw [Finset.sum_eq_single ai]
    · have hs1 : Matrix.single ai ai' (1 : ℂ) ai ai' = 1 := by simp [Matrix.single]
      rw [hs1, mul_one, hbp, hbp]
      simp only [Complex.star_def, map_mul]
      ring
    · intro x _ hxa; simp [Matrix.single, hxa.symm]
    · intro h; exact absurd (Finset.mem_univ ai) h
  · intro y _ hya
    have hz0 : (∑ x : Fin 4, basisProjection (U : CMatrix (Fin 4)) k ao x *
        Matrix.single ai ai' (1 : ℂ) x y) = 0 :=
      Finset.sum_eq_zero fun x _ => by simp [Matrix.single, hya.symm]
    rw [hz0, zero_mul]
  · intro h; exact absurd (Finset.mem_univ ai') h

private theorem choiOneCopy_dephasing_continuous :
    Continuous fun U : Matrix.unitaryGroup (Fin 4) ℂ => choiOneCopy (dephasingChannel U) := by
  refine continuous_pi fun ⟨ai, ao⟩ => continuous_pi fun ⟨ai', ao'⟩ => ?_
  simp_rw [choiOneCopy_dephasing_entry]
  refine continuous_finsetSum _ fun k _ => ?_
  have hentry (x y : Fin 4) :
      Continuous fun U : Matrix.unitaryGroup (Fin 4) ℂ => (U : CMatrix (Fin 4)) x y :=
    (continuous_apply y).comp ((continuous_apply x).comp continuous_subtype_val)
  exact ((hentry ai' k).mul (hentry ao k)).mul (Continuous.star ((hentry ai k).mul (hentry ao' k)))

/-- Single-copy Haar identity: `∫ U, J(Δ_U) ∂unitaryHaarMeasure = J(Λ)`. -/
theorem integral_choiOneCopy_dephasing :
    (∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
      choiOneCopy (dephasingChannel U) ∂unitaryHaarMeasure (a := Fin 4)) =
    choiOneCopy modelChannel := by
  have hf : Integrable (fun U => choiOneCopy (dephasingChannel U))
      (unitaryHaarMeasure (a := Fin 4)) :=
    choiOneCopy_dephasing_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  ext ⟨ai, ao⟩ ⟨ai', ao'⟩
  rw [integral_cMatrix_entry hf, choiOneCopy_modelChannel_entry]
  simp_rw [choiOneCopy_dephasing_entry]
  have hentry_cont (k : Fin 4) : Continuous fun U : Matrix.unitaryGroup (Fin 4) ℂ =>
      ((U : CMatrix (Fin 4)) ai' k * (U : CMatrix (Fin 4)) ao k) *
        star ((U : CMatrix (Fin 4)) ai k * (U : CMatrix (Fin 4)) ao' k) := by
    have he (x y : Fin 4) :
        Continuous fun U : Matrix.unitaryGroup (Fin 4) ℂ => (U : CMatrix (Fin 4)) x y :=
      (continuous_apply y).comp ((continuous_apply x).comp continuous_subtype_val)
    exact ((he ai' k).mul (he ao k)).mul (Continuous.star ((he ai k).mul (he ao' k)))
  rw [MeasureTheory.integral_finsetSum _ fun k _ =>
    (hentry_cont k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  change (∑ k : Fin 4, ICO.HaarMoments.fourthMoment ai' ao k k ai ao' k k) = _
  simp_rw [ICO.HaarMoments.fourthMoment_delta, Fintype.card_fin]
  have hkk (k : Fin 4) : ICO.HaarMoments.delta k k = 1 := by simp [ICO.HaarMoments.delta]
  simp_rw [hkk]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  unfold jLambdaScaled5 ICO.HaarMoments.delta
  have hd1 : (ai.val * 4 + ao.val) / 4 % 4 = ai.val := by omega
  have hd2 : (ai.val * 4 + ao.val) % 4 = ao.val := by omega
  have hd3 : (ai'.val * 4 + ao'.val) / 4 % 4 = ai'.val := by omega
  have hd4 : (ai'.val * 4 + ao'.val) % 4 = ao'.val := by omega
  rw [hd1, hd2, hd3, hd4]
  fin_cases ai <;> fin_cases ao <;> fin_cases ai' <;> fin_cases ao' <;> norm_num

private theorem choiTwoCopy_dephasing_continuous :
    Continuous fun U : Matrix.unitaryGroup (Fin 4) ℂ =>
      choiTwoCopy (dephasingChannel U) := by
  refine continuous_pi fun u => continuous_pi fun v => ?_
  have hc := choiOneCopy_dephasing_continuous
  exact (((continuous_apply (v.1, v.2.1)).comp ((continuous_apply (u.1, u.2.1)).comp hc)).mul
    ((continuous_apply (v.2.2.1, v.2.2.2)).comp ((continuous_apply (u.2.2.1, u.2.2.2)).comp hc)))

private theorem choiTwoCopy_dephasing_integrable :
    Integrable (fun U : Matrix.unitaryGroup (Fin 4) ℂ => choiTwoCopy (dephasingChannel U))
      (unitaryHaarMeasure (a := Fin 4)) :=
  choiTwoCopy_dephasing_continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Two-copy Haar identity: `∫ U, J(Δ_U)^{⊗ 2} ∂unitaryHaarMeasure = w0Matrix`. -/
theorem integral_choiTwoCopy_dephasing :
    (∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
      choiTwoCopy (dephasingChannel U) ∂unitaryHaarMeasure (a := Fin 4)) =
    w0Matrix := by
  have hf := choiTwoCopy_dephasing_integrable
  ext ⟨ai, ao, bi, bo⟩ ⟨ai', ao', bi', bo'⟩
  rw [integral_cMatrix_entry hf]
  let rWord : TensorPower (Fin 4) 4 := (ai', (ao, (bi', (bo, PUnit.unit))))
  let cWord : TensorPower (Fin 4) 4 := (ai, (ao', (bi, (bo', PUnit.unit))))
  have hpt (U : Matrix.unitaryGroup (Fin 4) ℂ) :
      choiTwoCopy (dephasingChannel U) (ai, ao, bi, bo) (ai', ao', bi', bo') =
        unitaryTwirlIntegrand (a := Fin 4) 4 diagK U rWord cWord := by
    simp only [choiTwoCopy, twoCopyKron, choiOneCopy_dephasing_entry,
      unitaryTwirlIntegrand, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, diagK]
    -- Collapse `y = x` and `x = (k, (k, (l, (l, ()))))` on the RHS:
    symm
    trans (∑ x : TensorPower (Fin 4) 4,
        if x.1 = x.2.1 ∧ x.2.2.1 = x.2.2.2.1 then
          (unitaryTensorPowerMatrix U 4 : CMatrix _) rWord x *
            star ((unitaryTensorPowerMatrix U 4 : CMatrix _) cWord x)
        else 0)
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single x]
      · by_cases hx : x.1 = x.2.1 ∧ x.2.2.1 = x.2.2.2.1 <;> simp [hx]
      · intro y _ hyx; simp [hyx]
      · intro h; exact absurd (Finset.mem_univ x) h
    · rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_product']
      let embKL : Fin 4 × Fin 4 → TensorPower (Fin 4) 4 :=
        fun kl => (kl.1, (kl.1, (kl.2, (kl.2, PUnit.unit))))
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image embKL))]
      · rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun ⟨k, l⟩ _ => ?_
          dsimp only [embKL]
          simp only [and_self, ↓reduceIte, unitaryTensorPowerMatrix_apply_eq_fin_prod,
            Fin.prod_univ_four, tp4_coord0, tp4_coord1, tp4_coord2, tp4_coord3, rWord, cWord,
            star_mul']
          ring
        · rintro ⟨k₁, l₁⟩ _ ⟨k₂, l₂⟩ _ heq
          dsimp [embKL] at heq
          rcases Prod.mk.inj heq with ⟨rfl, h2⟩
          rcases Prod.mk.inj (Prod.mk.inj h2).2 with ⟨rfl, _⟩
          rfl
      · intro x _ hx_not
        by_cases hx : x.1 = x.2.1 ∧ x.2.2.1 = x.2.2.2.1
        · exfalso
          apply hx_not
          refine Finset.mem_image.mpr ⟨(x.1, x.2.2.1), Finset.mem_univ _, ?_⟩
          rcases x with ⟨x0, x1, x2, x3, ⟨⟩⟩
          dsimp at hx
          rcases hx with ⟨rfl, rfl⟩
          rfl
        · simp [hx]
  simp_rw [hpt]
  have htw := unitaryTwirl_integrand_integrable (a := Fin 4) 4 diagK
  rw [← integral_cMatrix_entry htw rWord cWord]
  change unitaryTwirl (a := Fin 4) 4 diagK rWord cWord = _
  rw [unitaryTwirl_diagK_eq_wCand]
  have hr_eq : rWord = fin256ToTp4 (wires4ToFin256 (ai', ao, bi', bo)) :=
    (fin256ToTp4_encode4 ai' ao bi' bo).symm
  have hc_eq : cWord = fin256ToTp4 (wires4ToFin256 (ai, ao', bi, bo')) :=
    (fin256ToTp4_encode4 ai ao' bi bo').symm
  rw [hr_eq, hc_eq, wCand_fin256_eq]
  unfold w0Matrix wCandInt840
  rw [w0Scaled4200_no_sum_guard]
  dsimp only [wires4ToFin256]
  have enc_div (a0 a1 a2 a3 : Fin 4) :
      encode4 a0.val a1.val a2.val a3.val / 64 % 4 = a0.val ∧
      encode4 a0.val a1.val a2.val a3.val / 16 % 4 = a1.val ∧
      encode4 a0.val a1.val a2.val a3.val / 4 % 4 = a2.val ∧
      encode4 a0.val a1.val a2.val a3.val % 4 = a3.val := by dsimp [encode4]; omega
  rcases enc_div ai' ao bi' bo with ⟨er0, er1, er2, er3⟩
  rcases enc_div ai ao' bi bo' with ⟨ec0, ec1, ec2, ec3⟩
  rcases enc_div ai ao bi bo with ⟨eu0, eu1, eu2, eu3⟩
  rcases enc_div ai' ao' bi' bo' with ⟨ev0, ev1, ev2, ev3⟩
  rw [er0, er1, er2, er3, ec0, ec1, ec2, ec3, eu0, eu1, eu2, eu3, ev0, ev1, ev2, ev3]
  push_cast
  ring

private theorem choiTwoCopy_noisyDephasing_continuous (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Continuous fun U : Matrix.unitaryGroup (Fin 4) ℂ =>
      choiTwoCopy (noisyDephasingChannel p hp0 hp1 U) := by
  have hc1 : Continuous fun U : Matrix.unitaryGroup (Fin 4) ℂ =>
      choiOneCopy (noisyDephasingChannel p hp0 hp1 U) := by
    refine continuous_pi fun ij => continuous_pi fun kl => ?_
    have heq (U : Matrix.unitaryGroup (Fin 4) ℂ) :
        choiOneCopy (noisyDephasingChannel p hp0 hp1 U) ij kl =
          ((1 - p : ℝ) : ℂ) * choiOneCopy (Channel.idChannel (Fin 4)) ij kl +
            (p : ℂ) * choiOneCopy (dephasingChannel U) ij kl := by
      simp [choiOneCopy, noisyDephasingChannel, convexChannel, MatrixMap.choi]
    simp_rw [heq]
    exact continuous_const.add (continuous_const.mul
      ((continuous_apply kl).comp ((continuous_apply ij).comp choiOneCopy_dephasing_continuous)))
  refine continuous_pi fun u => continuous_pi fun v => ?_
  exact (((continuous_apply (v.1, v.2.1)).comp ((continuous_apply (u.1, u.2.1)).comp hc1)).mul
    ((continuous_apply (v.2.2.1, v.2.2.2)).comp ((continuous_apply (u.2.2.1, u.2.2.2)).comp hc1)))

/-- Noise-interpolated two-copy Choi difference: the `(1 - p)^2` and `(1 - p) p` terms cancel
identically by `integral_choiOneCopy_dephasing`, leaving `p^2 • deltaMatrix`. -/
theorem integral_choiTwoCopy_noisy_diff (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
      choiTwoCopy (noisyDephasingChannel p hp0 hp1 U) ∂unitaryHaarMeasure (a := Fin 4)) -
      choiTwoCopy (noisyModelChannel p hp0 hp1) =
    ((p ^ 2 : ℝ) : ℂ) • deltaMatrix := by
  have hf_noisy : Integrable (fun U => choiTwoCopy (noisyDephasingChannel p hp0 hp1 U))
      (unitaryHaarMeasure (a := Fin 4)) :=
    (choiTwoCopy_noisyDephasing_continuous p hp0 hp1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hf1 : Integrable (fun U => choiOneCopy (dephasingChannel U))
      (unitaryHaarMeasure (a := Fin 4)) :=
    choiOneCopy_dephasing_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hf2 := choiTwoCopy_dephasing_integrable
  ext u v
  rw [Matrix.sub_apply, integral_cMatrix_entry hf_noisy, Matrix.smul_apply, smul_eq_mul]
  set Jid := choiOneCopy (Channel.idChannel (Fin 4))
  set Jmod := choiOneCopy modelChannel
  have hchoi_conv (Φ₀ Φ₁ : Channel (Fin 4) (Fin 4)) (ab cd : Fin 4 × Fin 4) :
      choiOneCopy (convexChannel p hp0 hp1 Φ₀ Φ₁) ab cd =
        ((1 - p : ℝ) : ℂ) * choiOneCopy Φ₀ ab cd + (p : ℂ) * choiOneCopy Φ₁ ab cd := by
    simp [choiOneCopy, convexChannel, MatrixMap.choi]
  have hexp_U (U : Matrix.unitaryGroup (Fin 4) ℂ) :
      choiTwoCopy (noisyDephasingChannel p hp0 hp1 U) u v =
        (((1 - p) ^ 2 : ℝ) : ℂ) * (Jid (u.1, u.2.1) (v.1, v.2.1) * Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2)) +
        (((1 - p) * p : ℝ) : ℂ) * Jid (u.1, u.2.1) (v.1, v.2.1) *
          choiOneCopy (dephasingChannel U) (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2) +
        (((1 - p) * p : ℝ) : ℂ) * choiOneCopy (dephasingChannel U) (u.1, u.2.1) (v.1, v.2.1) *
          Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2) +
        ((p ^ 2 : ℝ) : ℂ) * choiTwoCopy (dephasingChannel U) u v := by
    simp only [choiTwoCopy, twoCopyKron, noisyDephasingChannel, hchoi_conv, Jid]
    push_cast
    ring
  have hexp_M :
      choiTwoCopy (noisyModelChannel p hp0 hp1) u v =
        (((1 - p) ^ 2 : ℝ) : ℂ) * (Jid (u.1, u.2.1) (v.1, v.2.1) * Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2)) +
        (((1 - p) * p : ℝ) : ℂ) * Jid (u.1, u.2.1) (v.1, v.2.1) *
          Jmod (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2) +
        (((1 - p) * p : ℝ) : ℂ) * Jmod (u.1, u.2.1) (v.1, v.2.1) *
          Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2) +
        ((p ^ 2 : ℝ) : ℂ) * choiTwoCopy modelChannel u v := by
    simp only [choiTwoCopy, twoCopyKron, noisyModelChannel, hchoi_conv, Jid, Jmod]
    push_cast
    ring
  simp_rw [hexp_U]
  have hi_b : Integrable (fun U => choiOneCopy (dephasingChannel U) (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2))
      (unitaryHaarMeasure (a := Fin 4)) :=
    (cMatrixEntryCLM (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2)).integrable_comp hf1
  have hi_a : Integrable (fun U => choiOneCopy (dephasingChannel U) (u.1, u.2.1) (v.1, v.2.1))
      (unitaryHaarMeasure (a := Fin 4)) :=
    (cMatrixEntryCLM (u.1, u.2.1) (v.1, v.2.1)).integrable_comp hf1
  have hi_2 : Integrable (fun U => choiTwoCopy (dephasingChannel U) u v)
      (unitaryHaarMeasure (a := Fin 4)) :=
    (cMatrixEntryCLM u v).integrable_comp hf2
  have h1 : Integrable (fun _ => (((1 - p) ^ 2 : ℝ) : ℂ) *
      (Jid (u.1, u.2.1) (v.1, v.2.1) * Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2)))
      (unitaryHaarMeasure (a := Fin 4)) :=
    integrable_const _
  have h2 : Integrable (fun U => (((1 - p) * p : ℝ) : ℂ) * Jid (u.1, u.2.1) (v.1, v.2.1) *
      choiOneCopy (dephasingChannel U) (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2))
      (unitaryHaarMeasure (a := Fin 4)) :=
    hi_b.const_mul _
  have h3 : Integrable (fun U => (((1 - p) * p : ℝ) : ℂ) *
      choiOneCopy (dephasingChannel U) (u.1, u.2.1) (v.1, v.2.1) *
      Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2)) (unitaryHaarMeasure (a := Fin 4)) :=
    (hi_a.const_mul _).mul_const _
  have h4 : Integrable (fun U => ((p ^ 2 : ℝ) : ℂ) * choiTwoCopy (dephasingChannel U) u v)
      (unitaryHaarMeasure (a := Fin 4)) :=
    hi_2.const_mul _
  have h12 : Integrable (fun U =>
      (((1 - p) ^ 2 : ℝ) : ℂ) * (Jid (u.1, u.2.1) (v.1, v.2.1) * Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2)) +
      (((1 - p) * p : ℝ) : ℂ) * Jid (u.1, u.2.1) (v.1, v.2.1) *
        choiOneCopy (dephasingChannel U) (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2))
      (unitaryHaarMeasure (a := Fin 4)) :=
    h1.add h2
  have h123 : Integrable (fun U =>
      (((1 - p) ^ 2 : ℝ) : ℂ) * (Jid (u.1, u.2.1) (v.1, v.2.1) * Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2)) +
      (((1 - p) * p : ℝ) : ℂ) * Jid (u.1, u.2.1) (v.1, v.2.1) *
        choiOneCopy (dephasingChannel U) (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2) +
      (((1 - p) * p : ℝ) : ℂ) * choiOneCopy (dephasingChannel U) (u.1, u.2.1) (v.1, v.2.1) *
        Jid (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2))
      (unitaryHaarMeasure (a := Fin 4)) :=
    h12.add h3
  rw [integral_add h123 h4,
      integral_add h12 h3,
      integral_add h1 h2,
      integral_const,
      integral_const_mul,
      integral_mul_const,
      integral_const_mul,
      integral_const_mul]
  simp only [probReal_univ, one_smul]
  rw [← integral_cMatrix_entry hf1 (u.2.2.1, u.2.2.2) (v.2.2.1, v.2.2.2),
      ← integral_cMatrix_entry hf1 (u.1, u.2.1) (v.1, v.2.1),
      ← integral_cMatrix_entry hf2 u v,
      integral_choiOneCopy_dephasing,
      integral_choiTwoCopy_dephasing,
      hexp_M, choiTwoCopy_modelChannel,
      ← w0Matrix_sub_w1Matrix_eq_deltaMatrix]
  simp only [Matrix.sub_apply, Jmod]
  ring


/-! ## Section 4: Unconditional operational proof of Proposition `prop:two-call` -/

private theorem choiTwoCopy_trace_tester_sum {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O)
    (Ψ : Channel (Fin 4) (Fin 4)) :
    ((choiTwoCopy Ψ * (testerAccept tree ρ T + testerReject tree ρ T)).trace).re = 1 := by
  have hsum_eff : T.acceptRhoEffect + T.rejectRhoEffect = 1 := by
    simpa [BinaryHypothesisTest.acceptRhoEffect, BinaryHypothesisTest.rejectRhoEffect,
      Fintype.sum_bool] using T.sum_eq_one
  have htr_one :
      (((tree.channel (Ψ.prod (Channel.idChannel M)) (Ψ.prod (Channel.idChannel M))).map
        ρ.matrix).trace).re = 1 := by
    rw [(tree.channel (Ψ.prod (Channel.idChannel M)) (Ψ.prod (Channel.idChannel M))).tracePreserving
        ρ.matrix, ρ.trace_eq_one, Complex.one_re]
  rw [← htr_one, ← compileTreeProtocol_map tree ρ Ψ]
  unfold testerAccept testerReject
  generalize compileTreeProtocol tree ρ = p2
  cases p2 with
  | query pre hpre p1 =>
    cases p1 with
    | query mid hmid p0 =>
      cases p0 with
      | stop post hpost =>
        rw [protocol2Tester_query, protocol2Tester_query,
            protocol1Tester_query, protocol1Tester_query,
            pureTester_add, protocol0Effect_add, hsum_eff, protocol0Effect_stop]
        dsimp only [ICO.SequentialIsometry.Protocol.map, LinearMap.comp_apply]
        rw [ICO.SequentialIsometry.singleMap_apply, ICO.SequentialIsometry.singleMap_apply,
            trace_choiTwoCopy_pureTester, Matrix.mul_one]

private theorem integral_trace_mul_re {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → CMatrix Wires4) (hf : Integrable f μ) (S : CMatrix Wires4) :
    ∫ x, ((f x * S).trace).re ∂μ = (((∫ x, f x ∂μ) * S).trace).re := by
  have htr (A : CMatrix Wires4) :
      ((A * S).trace).re = ∑ u : Wires4, ∑ v : Wires4, (A u v * S v u).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  simp_rw [htr]
  have h_c (u v : Wires4) : Integrable (fun x => f x u v * S v u) μ :=
    ((cMatrixEntryCLM u v).integrable_comp hf).mul_const (S v u)
  have hint_uv (u v : Wires4) : Integrable (fun x => (f x u v * S v u).re) μ :=
    Complex.reCLM.integrable_comp (h_c u v)
  have hint_u (u : Wires4) : Integrable (fun x => ∑ v : Wires4, (f x u v * S v u).re) μ :=
    MeasureTheory.integrable_finsetSum _ fun v _ => hint_uv u v
  rw [MeasureTheory.integral_finsetSum _ fun u _ => hint_u u]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun v _ => hint_uv u v]
  refine Finset.sum_congr rfl fun v _ => ?_
  change ∫ x, Complex.reCLM (f x u v * S v u) ∂μ =
    Complex.reCLM ((∫ x, f x ∂μ) u v * S v u)
  have hentry : (∫ x, f x ∂μ) u v = ∫ x, f x u v ∂μ :=
    ((cMatrixEntryCLM u v).integral_comp_comm hf).symm
  rw [Complex.reCLM.integral_comp_comm (h_c u v), integral_mul_const, hentry]

private theorem deltaMatrix_trace_tester_sum {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    ((deltaMatrix * (testerAccept tree ρ T + testerReject tree ρ T)).trace).re = 0 := by
  let S := testerAccept tree ρ T + testerReject tree ρ T
  have hf := choiTwoCopy_dephasing_integrable
  have hw0 : ((w0Matrix * S).trace).re = 1 := by
    rw [← integral_choiTwoCopy_dephasing, ← integral_trace_mul_re _ hf S]
    have hconst (U : Matrix.unitaryGroup (Fin 4) ℂ) :
        ((choiTwoCopy (dephasingChannel U) * S).trace).re = 1 :=
      choiTwoCopy_trace_tester_sum tree ρ T (dephasingChannel U)
    simp_rw [hconst]
    simp [integral_const, probReal_univ]
  have hw1 : ((w1Matrix * S).trace).re = 1 := by
    rw [← choiTwoCopy_modelChannel]
    exact choiTwoCopy_trace_tester_sum tree ρ T modelChannel
  change ((deltaMatrix * S).trace).re = 0
  rw [← w0Matrix_sub_w1Matrix_eq_deltaMatrix, Matrix.sub_mul, Matrix.trace_sub,
      Complex.sub_re, hw0, hw1, sub_self]

/-- Unconditional SDP dual bound on the two-slot tester trace pairing:
`|Tr(Δ T_0)| ≤ 4 / 25` for every two-call `Tree (Fin 4 × M) O 2 B`, state `ρ`, and test `T`. -/
theorem trace_deltaMatrix_testerAccept_abs_le {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    |((deltaMatrix * testerAccept tree ρ T).trace).re| ≤ 4 / 25 := by
  have h_acc : 0 ≤ (((zMatrix - deltaMatrix) * testerAccept tree ρ T).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg zMatrix_sub_deltaMatrix_posSemidef
      (testerAccept_posSemidef tree ρ T)
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at h_acc
  have h_rej : 0 ≤ (((zMatrix - deltaMatrix) * testerReject tree ρ T).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg zMatrix_sub_deltaMatrix_posSemidef
      (testerReject_posSemidef tree ρ T)
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at h_rej
  have h_z_acc : 0 ≤ ((zMatrix * testerAccept tree ρ T).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg zMatrix_posSemidef
      (testerAccept_posSemidef tree ρ T)
  have h_z_rej : 0 ≤ ((zMatrix * testerReject tree ρ T).trace).re :=
    cMatrix_trace_mul_posSemidef_re_nonneg zMatrix_posSemidef
      (testerReject_posSemidef tree ρ T)
  have h_z_sum := zMatrix_trace_tester_sum tree ρ T
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at h_z_sum
  have h_d_sum := deltaMatrix_trace_tester_sum tree ρ T
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at h_d_sum
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Exact operational acceptance-difference identity for noise rate `p`:
the Haar-averaged acceptance minus the model acceptance equals `p^2 * Re(Tr(Δ T_0))`. -/
theorem acceptance_noisy_haar_sub_model_eq {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    (∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
      acceptance T tree ρ
        ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
        ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
      ∂unitaryHaarMeasure (a := Fin 4)) -
    acceptance T tree ρ
      ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M))
      ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M)) =
    p ^ 2 * ((deltaMatrix * testerAccept tree ρ T).trace).re := by
  let Tacc := testerAccept tree ρ T
  have hf_noisy : Integrable (fun U => choiTwoCopy (noisyDephasingChannel p hp0 hp1 U))
      (unitaryHaarMeasure (a := Fin 4)) :=
    (choiTwoCopy_noisyDephasing_continuous p hp0 hp1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hU (U : Matrix.unitaryGroup (Fin 4) ℂ) :
      acceptance T tree ρ
        ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
        ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M)) =
      ((choiTwoCopy (noisyDephasingChannel p hp0 hp1 U) * Tacc).trace).re :=
    acceptance_eq_trace_choiTwoCopy tree ρ T (noisyDephasingChannel p hp0 hp1 U)
  have hM :
      acceptance T tree ρ
        ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M))
        ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M)) =
      ((choiTwoCopy (noisyModelChannel p hp0 hp1) * Tacc).trace).re :=
    acceptance_eq_trace_choiTwoCopy tree ρ T (noisyModelChannel p hp0 hp1)
  simp_rw [hU, hM]
  rw [integral_trace_mul_re _ hf_noisy Tacc,
      ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul,
      integral_choiTwoCopy_noisy_diff p hp0 hp1,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- Unconditional noise-interpolated Proposition `prop:two-call` (`0 ≤ p ≤ 1`):
Every two-call ordinary strategy `tree : Tree (Fin 4 × M) O 2 B` attempting to distinguish
`E_{p,U} = (1 - p) id + p Δ_U` (for Haar-random `U ∈ U(4)`) from `M_p = (1 - p) id + p Λ`
has acceptance gap bounded in magnitude by `(4 / 25) * p^2` and balanced-prior success
probability at most `1 / 2 + (2 / 25) * p^2` (strictly below the one-switch-use success
`1 / 2 + (3 / 20) * p^2` whenever `0 < p`). -/
theorem two_call_noisy_haar_vs_model_upper_bound {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    |(∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
        acceptance T tree ρ
          ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
          ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
        ∂unitaryHaarMeasure (a := Fin 4)) -
      acceptance T tree ρ
        ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M))
        ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M))| ≤
      (4 / 25 : ℝ) * p ^ 2 ∧
    (1 / 2 : ℝ) *
      (∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
        acceptance T tree ρ
          ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
          ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
        ∂unitaryHaarMeasure (a := Fin 4)) +
    (1 / 2 : ℝ) *
      (1 - acceptance T tree ρ
        ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M))
        ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M))) ≤
      1 / 2 + (2 / 25 : ℝ) * p ^ 2 ∧
    (0 < p → 1 / 2 + (2 / 25 : ℝ) * p ^ 2 < 1 / 2 + (3 / 20 : ℝ) * p ^ 2) := by
  have hdiff := acceptance_noisy_haar_sub_model_eq p hp0 hp1 tree ρ T
  have htr := trace_deltaMatrix_testerAccept_abs_le tree ρ T
  have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
  have habs :
      |(∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
          acceptance T tree ρ
            ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
            ((noisyDephasingChannel p hp0 hp1 U).prod (Channel.idChannel M))
          ∂unitaryHaarMeasure (a := Fin 4)) -
        acceptance T tree ρ
          ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M))
          ((noisyModelChannel p hp0 hp1).prod (Channel.idChannel M))| ≤
        (4 / 25 : ℝ) * p ^ 2 := by
    rw [hdiff, abs_mul, abs_of_nonneg hp2, mul_comm (p ^ 2)]
    exact mul_le_mul_of_nonneg_right htr hp2
  have hupper := (abs_le.mp habs).2
  refine ⟨habs, by linarith, fun hp_pos => ?_⟩
  have hp2_pos : 0 < p ^ 2 := sq_pos_of_pos hp_pos
  linarith

theorem noisyDephasingChannel_one (U : Matrix.unitaryGroup (Fin 4) ℂ) :
    noisyDephasingChannel 1 (by norm_num) (by norm_num) U = dephasingChannel U := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  ext X i j
  simp [noisyDephasingChannel, convexChannel]

theorem noisyModelChannel_one :
    noisyModelChannel 1 (by norm_num) (by norm_num) = modelChannel := by
  apply ICO.BudgetHaarBound.channel_eq_of_map_eq
  ext X i j
  simp [noisyModelChannel, convexChannel]

/-- Unconditional Proposition `prop:two-call` (`p = 1`):
At `d = 4`, every ordinary strategy using an unknown channel on `Fin 4` at most twice
(with arbitrary finite ancilla register `M`, initial state `ρ : State B`, and binary
measurement `T : BinaryHypothesisTest O`) succeeds in distinguishing Haar-random
rank-one dephasing `Δ_U` from the depolarizing model `Λ = (id + 4 Ω) / 5` under the
balanced prior with probability at most `29 / 50`, whereas one use of the quantum switch
succeeds with probability `13 / 20` (`gap = 7 / 100`, cf. `two_call_switch_success`). -/
theorem two_call_haar_vs_model_upper_bound {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    |(∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
        acceptance T tree ρ
          ((dephasingChannel U).prod (Channel.idChannel M))
          ((dephasingChannel U).prod (Channel.idChannel M))
        ∂unitaryHaarMeasure (a := Fin 4)) -
      acceptance T tree ρ
        (modelChannel.prod (Channel.idChannel M))
        (modelChannel.prod (Channel.idChannel M))| ≤
      4 / 25 ∧
    (1 / 2 : ℝ) *
      (∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
        acceptance T tree ρ
          ((dephasingChannel U).prod (Channel.idChannel M))
          ((dephasingChannel U).prod (Channel.idChannel M))
        ∂unitaryHaarMeasure (a := Fin 4)) +
    (1 / 2 : ℝ) *
      (1 - acceptance T tree ρ
        (modelChannel.prod (Channel.idChannel M))
        (modelChannel.prod (Channel.idChannel M))) ≤
      29 / 50 ∧
    (29 / 50 : ℝ) < 13 / 20 ∧
    (13 / 20 : ℝ) - 29 / 50 = 7 / 100 := by
  have h1 := two_call_noisy_haar_vs_model_upper_bound 1 (by norm_num) (by norm_num) tree ρ T
  simp_rw [noisyDephasingChannel_one, noisyModelChannel_one] at h1
  rcases h1 with ⟨habs, hbal, _⟩
  refine ⟨by linarith, by linarith, by norm_num, by norm_num⟩

/-- Unconditional Proposition `prop:two-call` phrased directly with
`ICO.BudgetContinuity.hidden (A := Fin 4) (M := M) U`. -/
theorem two_call_hidden_vs_model_upper_bound {M O B : Type}
    [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (tree : Tree (Fin 4 × M) O 2 B) (ρ : State B) (T : BinaryHypothesisTest O) :
    |(∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
        acceptance T tree ρ
          (ICO.BudgetContinuity.hidden (A := Fin 4) (M := M) U)
          (ICO.BudgetContinuity.hidden (A := Fin 4) (M := M) U)
        ∂unitaryHaarMeasure (a := Fin 4)) -
      acceptance T tree ρ
        (modelChannel.prod (Channel.idChannel M))
        (modelChannel.prod (Channel.idChannel M))| ≤
      4 / 25 ∧
    (1 / 2 : ℝ) *
      (∫ U : Matrix.unitaryGroup (Fin 4) ℂ,
        acceptance T tree ρ
          (ICO.BudgetContinuity.hidden (A := Fin 4) (M := M) U)
          (ICO.BudgetContinuity.hidden (A := Fin 4) (M := M) U)
        ∂unitaryHaarMeasure (a := Fin 4)) +
    (1 / 2 : ℝ) *
      (1 - acceptance T tree ρ
        (modelChannel.prod (Channel.idChannel M))
        (modelChannel.prod (Channel.idChannel M))) ≤
      29 / 50 ∧
    (29 / 50 : ℝ) < 13 / 20 ∧
    (13 / 20 : ℝ) - 29 / 50 = 7 / 100 := by
  simpa only [← dephasingChannel_prod_id_eq_hidden] using
    two_call_haar_vs_model_upper_bound tree ρ T

#print axioms zMatrix_posSemidef
#print axioms zMatrix_sub_deltaMatrix_posSemidef
#print axioms unitaryTwirl_diagK_eq_wCand
#print axioms integral_choiTwoCopy_dephasing
#print axioms integral_choiTwoCopy_noisy_diff
#print axioms trace_deltaMatrix_testerAccept_abs_le
#print axioms two_call_noisy_haar_vs_model_upper_bound
#print axioms two_call_haar_vs_model_upper_bound
#print axioms two_call_hidden_vs_model_upper_bound

end

end ICO.TwoCallOperational
