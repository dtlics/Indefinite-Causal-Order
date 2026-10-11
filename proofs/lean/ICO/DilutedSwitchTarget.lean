import ICO.QubitCircuitLink
import ICO.ExactSeparation

namespace ICO.DilutedSwitchTarget
open ICO.QubitCircuitLink ICO.QubitCircuitMatrix ICO.QubitLink
open ICO.ExactTensorCertificates ICO.ExactSeparation ICO.PositiveSupport
open Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
noncomputable section

def basisVector (a : Fin 25) : Fin 128 → ℂ := fun i => basisEntry i.val a.val

def targetChoi (lambda mu : ℝ) : Matrix (Fin 128) (Fin 128) ℂ :=
  ∑ a : Fin 25, (targetEntry lambda mu a.val a.val : ℂ) • rankOne (basisVector a)

def columnScale (U V : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 25) : ℂ :=
  if a.val < 16 then U (QubitLink.bit a.val 4) (QubitLink.bit a.val 8) *
    V (QubitLink.bit a.val 1) (QubitLink.bit a.val 2)
  else if a.val < 20 then V (QubitLink.bit a.val 1) (QubitLink.bit a.val 2)
  else if a.val < 24 then U (QubitLink.bit a.val 1) (QubitLink.bit a.val 2)
  else 1

def columnGroup (a : Fin 25) : Fin 4 :=
  if a.val < 16 then ⟨0, by decide⟩ else if a.val < 20 then ⟨1, by decide⟩ else if a.val < 24 then ⟨2, by decide⟩ else ⟨3, by decide⟩

theorem basis_encoded (a : Fin 25) (p ai ao bi bo : Fin 2) (f : Fin 4) :
    basisVector a (encode6 (((((p,ai),ao),bi),bo),f)) =
      (if a.val < 16 then ind (p.val == f.val%2 && a.val == 8*ai.val+4*ao.val+2*bi.val+bo.val)
      else if a.val < 20 then ind (p.val == ai.val && ao.val == f.val%2 && a.val == 16+2*bi.val+bo.val)
      else if a.val < 24 then ind (p.val == bi.val && bo.val == f.val%2 && a.val == 20+2*ai.val+ao.val)
      else if a.val == 24 then ind ((f.val/2 == 0 && p.val == ai.val && ao.val == bi.val && bo.val == f.val%2) ||
        (f.val/2 == 1 && p.val == bi.val && bo.val == ai.val && ao.val == f.val%2)) else 0 : Int) := by
  have hp : (encode6 (((((p,ai),ao),bi),bo),f)).val/64%2 = p.val := by dsimp [encode6]; omega
  have hai : (encode6 (((((p,ai),ao),bi),bo),f)).val/32%2 = ai.val := by dsimp [encode6]; omega
  have hao : (encode6 (((((p,ai),ao),bi),bo),f)).val/16%2 = ao.val := by dsimp [encode6]; omega
  have hbi : (encode6 (((((p,ai),ao),bi),bo),f)).val/8%2 = bi.val := by dsimp [encode6]; omega
  have hbo : (encode6 (((((p,ai),ao),bi),bo),f)).val/4%2 = bo.val := by dsimp [encode6]; omega
  have hc : (encode6 (((((p,ai),ao),bi),bo),f)).val/2%2 = f.val/2 := by dsimp [encode6]; omega
  have ht : (encode6 (((((p,ai),ao),bi),bo),f)).val%2 = f.val%2 := by dsimp [encode6]; omega
  simp only [basisVector, basisEntry, hp, hai, hao, hbi, hbo, hc, ht]

/-- Actual tensor-defined E columns link to the four physical switch vectors. -/
theorem linked_basis (U V : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 25) :
    linkMatrix U V *ᵥ basisVector a = columnScale U V a • outputVector U V (columnGroup a) := by
  funext o
  obtain ⟨⟨p,f⟩,rfl⟩ := (finProdFinEquiv (m := 2) (n := 4)).surjective o
  rw [link_sum]
  simp only [basis_encoded]
  fin_cases a <;> fin_cases p <;> fin_cases f <;>
    norm_num [ind, columnScale, columnGroup, outputVector, Fin.val_natCast,
      QubitLink.bit, Fin.sum_univ_two, finProdFinEquiv, Matrix.mul_apply,
      Pi.smul_apply, smul_eq_mul] <;> ring <;> norm_num [Fin.val_natCast]

theorem rankOne_scale {I : Type*} (s : ℂ) (v : I → ℂ) :
    rankOne (s • v) = (s * star s) • rankOne v := by
  ext i j
  simp [rankOne, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem linked_target_columns (lambda mu : ℝ) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    linkMatrix U V * targetChoi lambda mu * (linkMatrix U V)ᴴ =
      ∑ a : Fin 25, ((targetEntry lambda mu a.val a.val : ℂ) *
        (columnScale U V a * star (columnScale U V a))) •
          rankOne (outputVector U V (columnGroup a)) := by
  unfold targetChoi
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.mul_smul, Matrix.smul_mul, ← rankOne_mulVec, linked_basis, rankOne_scale, smul_smul]

def frobeniusMass (U : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, U i j * star (U i j)

#print axioms linked_basis
#print axioms linked_target_columns
end
end ICO.DilutedSwitchTarget


