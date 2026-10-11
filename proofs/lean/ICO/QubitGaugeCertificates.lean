import ICO.UnitaryTestDefinitions

/-! Exact finite data for the CPTP spanning family I/2 and (I+Pauli⊗Pauli)/2.
All identities in this file are checked in the kernel over integer pairs. -/
namespace ICO.QubitGaugeCertificates
open ICO.UnitaryTestCertificates ICO.ExactTensorCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def gpStar (a : GPair) : GPair := (a.1,-a.2)
def pauliEntry (p i j : Nat) : GPair :=
  if p == 0 then (if i == j then (1,0) else (0,0))
  else if p == 1 then (if i == j then (0,0) else (1,0))
  else if p == 2 then (if i == j then (0,0) else if i == 0 then (0,-1) else (0,1))
  else if i == j then (if i == 0 then (1,0) else (-1,0)) else (0,0)

def basisEntry (k i j : Nat) : GPair :=
  if k == 0 then (if i == j then (1,0) else (0,0))
  else gpMul (pauliEntry ((k-1)/3) (i/2) (j/2))
    (pauliEntry ((k-1)%3+1) (i%2) (j%2))

def twiceChannel (k i j : Nat) : GPair :=
  if k == 0 then basisEntry 0 i j else gpAdd (basisEntry 0 i j) (basisEntry k i j)

def lambdaCoeff (i j a b : Nat) : Int :=
  4 * (if i == a && j == b then 1 else 0) -
  2 * (if i%2 == j%2 && i/2 == a/2 && j/2 == b/2 && a%2 == b%2 then 1 else 0) +
  (if i == j && a == b then 1 else 0)

theorem basis_hermitian : ∀ (k : Fin 13) (i j : Fin 4),
    gpStar (basisEntry k.val j.val i.val) = basisEntry k.val i.val j.val := by
  decide +kernel

theorem basis_involution : ∀ (k : Fin 13) (i j : Fin 4),
    gpSum 4 (fun a => gpMul (basisEntry k.val i.val a) (basisEntry k.val a j.val)) =
      if i = j then (1,0) else (0,0) := by
  decide +kernel

theorem channel_trace : ∀ (k : Fin 13) (i j : Fin 2),
    gpSum 2 (fun a => twiceChannel k.val (2*i.val+a) (2*j.val+a)) =
      if i = j then (2,0) else (0,0) := by
  decide +kernel

theorem lambda_expansion : ∀ (i j a b : Fin 4),
    gpSum 13 (fun k => gpMul (basisEntry k i.val j.val) (basisEntry k b.val a.val)) =
      (lambdaCoeff i.val j.val a.val b.val, 0) := by
  decide +kernel

end ICO.QubitGaugeCertificates
