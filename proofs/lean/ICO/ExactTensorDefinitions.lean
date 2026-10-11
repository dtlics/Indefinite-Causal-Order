import Std

/-!
# Exact tensor certificate for the diluted qubit switch

All coefficients are integers.  Tensor factors are ordered
`P, A_I, A_O, B_I, B_O, F_c, F_t`, with the first factor the most significant
binary digit.  `basisEntry` is precisely the integer matrix E in P3.
`choiCoefficient` is the coefficient of one symmetric coordinate X_ab in E X Eᵀ.

The three causal/gauge row functions are defined by actual finite partial traces
and normalized trace-and-replace operations; they are not free certificate input.
The supplied sparse row combinations are DATA only.  The declarations below
prove their coefficient identities by kernel reduction (`decide`, never
`native_decide`).  This file alone does not formalize quantum-channel semantics,
the support/rank argument, or arbitrary-query polarization.
-/

namespace ICO.ExactTensorCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A finite sum evaluated by structural recursion. -/
def sumBelow (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | m + 1 => sumBelow m f + f m

/-- Integer 0/1 indicator. -/
def ind (p : Bool) : Int := if p then 1 else 0

/-- Column k and row i of the 128-by-25 integer support matrix. -/
def basisEntry (i k : Nat) : Int :=
  let p := i / 64 % 2
  let ai := i / 32 % 2
  let ao := i / 16 % 2
  let bi := i / 8 % 2
  let bo := i / 4 % 2
  let c := i / 2 % 2
  let t := i % 2
  if k < 16 then
    ind (p == t && k == 8 * ai + 4 * ao + 2 * bi + bo)
  else if k < 20 then
    ind (p == ai && ao == t && k == 16 + 2 * bi + bo)
  else if k < 24 then
    ind (p == bi && bo == t && k == 20 + 2 * ai + ao)
  else if k == 24 then
    ind ((c == 0 && p == ai && ao == bi && bo == t) ||
         (c == 1 && p == bi && bo == ai && ao == t))
  else 0

/-- Symmetric-coordinate coefficient; the diagonal is counted only once. -/
def choiCoefficient (a b i j : Nat) : Int :=
  basisEntry i a * basisEntry j b +
    if a == b then 0 else basisEntry i b * basisEntry j a

/-- Swap the A and B input/output tensor-factor pairs. -/
def swapSlots (i : Nat) : Nat :=
  (i / 64 % 2) * 64 + (i / 8 % 2) * 32 + (i / 4 % 2) * 16 +
  (i / 32 % 2) * 8 + (i / 16 % 2) * 4 + i % 4

/-- First causal trace row: 2 Tr_F C - (Tr_BO,F C) tensor I_BO. -/
def causalOne (C : Nat → Nat → Int) (k : Nat) : Int :=
  let i := k / 32
  let j := k % 32
  2 * sumBelow 4 (fun f => C (4 * i + f) (4 * j + f)) -
    if i % 2 == j % 2 then
      sumBelow 8 (fun h => C (8 * (i / 2) + h) (8 * (j / 2) + h))
    else 0

/-- Second causal trace row after eliminating the intermediate comb matrices. -/
def causalTwo (C : Nat → Nat → Int) (k : Nat) : Int :=
  let i := k / 8
  let j := k % 8
  2 * sumBelow 16 (fun h => C (16 * i + h) (16 * j + h)) -
    if i % 2 == j % 2 then
      sumBelow 32 (fun h => C (32 * (i / 2) + h) (32 * (j / 2) + h))
    else 0

def causalRow (C : Nat → Nat → Int) (k : Nat) : Int :=
  if k < 1024 then causalOne C k else causalTwo C (k - 1024)

def rowAB (k a b : Nat) : Int :=
  causalRow (choiCoefficient a b) k

def rowBA (k a b : Nat) : Int :=
  causalRow (fun i j => choiCoefficient a b (swapSlots i) (swapSlots j)) k

/-- Unnormalized trace-and-replace on a consecutive block of binary factors.
`unit` is the weight of the least significant replaced factor and `size` the
block dimension.  Equality of the output indices is enforced before tracing.
-/
def traceReplace (unit size : Nat) (C : Nat → Nat → Int) (i j : Nat) : Int :=
  if i / unit % size == j / unit % size then
    sumBelow size (fun h =>
      C (i / (unit * size) * (unit * size) + h * unit + i % unit)
        (j / (unit * size) * (unit * size) + h * unit + j % unit))
  else 0

/-- Four times Lambda_A = Id - _AO + _AI,AO, without rational coefficients. -/
def projectA4 (C : Nat → Nat → Int) (i j : Nat) : Int :=
  4 * C i j - 2 * traceReplace 16 2 C i j + traceReplace 16 4 C i j

/-- Four times Lambda_B = Id - _BO + _BI,BO. -/
def projectB4 (C : Nat → Nat → Int) (i j : Nat) : Int :=
  4 * C i j - 2 * traceReplace 4 2 C i j + traceReplace 4 4 C i j

/-- A row of 16 Lambda_A Lambda_B applied to the symmetric Choi coefficient. -/
def rowGauge16 (k a b : Nat) : Int :=
  projectA4 (projectB4 (choiCoefficient a b)) (k % 128) (k / 128)

/-- The published sparse functional f, in symmetric-coordinate convention. -/
def witness (a b : Nat) : Int :=
  if a == 0 && b == 3 then 2
  else if a == 0 && b == 16 then -4
  else if a == 0 && b == 19 then 6
  else if a == 2 && b == 18 then -2
  else if a == 3 && b == 6 then -2
  else if a == 3 && b == 19 then -2
  else if a == 3 && b == 24 then -2
  else if a == 4 && b == 7 then -2
  else if a == 6 && b == 19 then -2
  else if a == 24 && b == 24 then 1
  else 0

/-- Sparse integer linear combination of rows. -/
def combine (data : List (Nat × Int)) (row : Nat → Nat → Nat → Int)
    (a b : Nat) : Int :=
  (data.map (fun kc => kc.2 * row kc.1 a b)).sum

def abScale : Int := 2

def abRows : List (Nat × Int) := [
  (927, 3),
  (33, 1),
  (36, 1),
  (288, 1),
  (1036, -1),
  (543, 3),
  (603, 1),
  (480, -3),
  (135, -1),
  (795, 1),
  (102, -2),
  (153, -1),
  (75, -1),
  (306, -1),
  (264, -1),
  (630, 1),
  (531, 1),
  (399, -3),
  (246, 1),
  (564, -1),
  (252, -3),
  (378, 1),
  (792, 1),
  (528, 1),
  (432, -3),
  (444, -3),
  (537, -1),
  (267, -1),
  (498, 3),
  (510, 3)
]

def abIdentity (a b : Nat) : Prop :=
  combine abRows rowAB a b = abScale * witness a b

def baScale : Int := 4

def baRows : List (Nat × Int) := [
  (1027, -1),
  (1078, -1),
  (1063, 1),
  (927, -5),
  (96, 4),
  (36, 1),
  (288, 1),
  (1036, -1),
  (1042, 1),
  (543, -3),
  (108, 4),
  (603, 1),
  (924, -2),
  (858, 1),
  (480, 3),
  (795, -1),
  (636, -4),
  (102, -1),
  (153, -1),
  (75, -1),
  (159, 2),
  (306, -1),
  (264, -2),
  (396, 2),
  (726, 1),
  (630, 1),
  (531, -4),
  (45, -4),
  (399, 5),
  (300, -2),
  (864, -1),
  (60, 3),
  (246, 1),
  (564, -1),
  (252, 1),
  (378, 1),
  (792, 2),
  (198, -1),
  (114, -4),
  (432, 8),
  (126, -5),
  (444, 2),
  (537, -1),
  (267, 1),
  (330, -1),
  (498, -4),
  (510, -6)
]

def baIdentity (a b : Nat) : Prop :=
  combine baRows rowBA a b = baScale * witness a b

def gaugeScale : Int := 18897408

def gaugeRows : List (Nat × Int) := [
  (125, -2457792),
  (2, 727200),
  (16127, 3111696),
  (113, -4474368),
  (77, 352584),
  (528, 1124712),
  (14589, 3747024),
  (3110, 580779),
  (9981, -1409184),
  (1560, -2362176),
  (4912, 3069846),
  (1584, -2474292),
  (55, 97110),
  (285, 2797578),
  (9969, 2474292),
  (629, 1409184),
  (2141, -533304),
  (664, -893484),
  (4977, -3069846),
  (12413, 12798),
  (9597, 2268018),
  (4386, 3226176),
  (1032, -3226176),
  (14061, -1068048),
  (15867, 4179744),
  (13674, -574144),
  (2709, -1819520),
  (688, 290796),
  (1555, -1935300),
  (2528, 2473968),
  (12255, -727200),
  (15093, -3089376),
  (9976, 797430),
  (1806, -2158128),
  (6192, -953568),
  (7160, 2112),
  (14193, -290796),
  (714, -1364640),
  (4984, -3069846),
  (13433, 1590624),
  (2117, -897624),
  (3789, -818880),
  (3309, 681264),
  (593, -227088),
  (15741, 2725056),
  (7776, -410454),
  (13029, 3226176),
  (7754, -224226),
  (6209, 5883552),
  (11739, -3226176),
  (1601, 2009592),
  (1009, 1295280),
  (1565, -89472),
  (14202, -2672070),
  (4857, -1192968),
  (4033, 5719086),
  (6204, -3747024),
  (1080, -1409184),
  (3870, -1430928),
  (6849, -1699686),
  (3364, -580779),
  (666, 893484),
  (3044, 1476432),
  (8643, -727200),
  (6708, 2135808),
  (1018, 413622),
  (2212, 3069846),
  (11364, 114096),
  (1656, 3500046),
  (3665, -1828872),
  (7745, 2457792),
  (6882, -1007712),
  (5089, -3590496)
]

def gaugeIdentity (a b : Nat) : Prop :=
  combine gaugeRows rowGauge16 a b = gaugeScale * witness a b

end ICO.ExactTensorCertificates
