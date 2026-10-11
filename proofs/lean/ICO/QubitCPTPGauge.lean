import ICO.QubitGaugeCertificates
import ICO.QubitLink
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace ICO.QubitCPTPGauge
open ICO.UnitaryTestCertificates ICO.QubitUnitaryTests ICO.QubitLink
open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

abbrev SlotMatrix := Matrix (Fin 4) (Fin 4) ℂ
def pauliBasis (k : Fin 13) : SlotMatrix :=
  fun i j => pairComplex (ICO.QubitGaugeCertificates.basisEntry k.val i.val j.val)

def channelChoi (k : Fin 13) : SlotMatrix :=
  fun i j => (1/2 : ℂ) * pairComplex (ICO.QubitGaugeCertificates.twiceChannel k.val i.val j.val)

def traceOutput (J : SlotMatrix) (i j : Fin 2) : ℂ :=
  ∑ a : Fin 2, J ⟨2*i.val+a.val, by omega⟩ ⟨2*j.val+a.val, by omega⟩

def IsChannelChoi (J : SlotMatrix) : Prop :=
  J.PosSemidef ∧ ∀ i j : Fin 2, traceOutput J i j = if i = j then 1 else 0

theorem pairComplex_star (a : GPair) :
    pairComplex (ICO.QubitGaugeCertificates.gpStar a) = star (pairComplex a) := by
  simp [pairComplex, ICO.QubitGaugeCertificates.gpStar]

theorem pauliBasis_hermitian (k : Fin 13) : (pauliBasis k).IsHermitian := by
  ext i j
  have h := congrArg pairComplex (ICO.QubitGaugeCertificates.basis_hermitian k i j)
  simpa [pairComplex_star, pauliBasis, Matrix.conjTranspose_apply] using h

theorem pauliBasis_square (k : Fin 13) : pauliBasis k * pauliBasis k = 1 := by
  ext i j
  have h := congrArg pairComplex (ICO.QubitGaugeCertificates.basis_involution k i j)
  rw [pairComplex_sum] at h
  simp only [pairComplex_mul] at h
  simpa [pauliBasis, Matrix.mul_apply, Matrix.one_apply, apply_ite, pairComplex] using h

theorem pauliBasis_zero : pauliBasis 0 = 1 := by
  ext i j
  simp [pauliBasis, ICO.QubitGaugeCertificates.basisEntry, pairComplex,
    Matrix.one_apply, Fin.val_inj]
  split_ifs <;> simp

theorem channelChoi_zero : channelChoi 0 = (1/2 : ℂ) • (1 : SlotMatrix) := by
  ext i j
  simp [channelChoi, ICO.QubitGaugeCertificates.twiceChannel,
    ICO.QubitGaugeCertificates.basisEntry, pairComplex, Matrix.one_apply,
    Fin.val_inj]
  split_ifs <;> simp

theorem channelChoi_nonzero (k : Fin 13) (hk : k ≠ 0) :
    channelChoi k = (1/2 : ℂ) • (1 + pauliBasis k) := by
  have hv : k.val ≠ 0 := fun h => hk (Fin.ext h)
  ext i j
  simp [channelChoi, ICO.QubitGaugeCertificates.twiceChannel, hv,
    pairComplex_add]
  change pairComplex (ICO.QubitGaugeCertificates.basisEntry 0 i.val j.val) +
    pauliBasis k i j = (1 : SlotMatrix) i j + pauliBasis k i j
  rw [show pairComplex (ICO.QubitGaugeCertificates.basisEntry 0 i.val j.val) =
    pauliBasis 0 i j from rfl, pauliBasis_zero]

theorem channelChoi_hermitian (k : Fin 13) : (channelChoi k).IsHermitian := by
  by_cases hk : k = 0
  · subst k
    rw [channelChoi_zero]
    simp only [IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    congr 1
    norm_num
  · rw [channelChoi_nonzero k hk]
    simp only [IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, (pauliBasis_hermitian k).eq]
    congr 1
    norm_num

theorem channelChoi_psd (k : Fin 13) : (channelChoi k).PosSemidef := by
  by_cases hk : k = 0
  · subst k
    rw [channelChoi_zero]
    have heq : (1/2 : ℂ) • (1 : SlotMatrix) = Matrix.diagonal (fun _ => (1/2 : ℂ)) := by
      ext i j
      simp [Matrix.one_apply, Matrix.diagonal_apply]
    rw [heq, Matrix.posSemidef_diagonal_iff]
    intro i
    norm_num [Complex.le_def]
  · have hid : channelChoi k * channelChoi k = channelChoi k := by
      rw [channelChoi_nonzero k hk, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
        Matrix.mul_one, pauliBasis_square]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
        Matrix.one_mul, Matrix.one_apply]
      ring
    have hp := Matrix.posSemidef_conjTranspose_mul_self (channelChoi k)
    rwa [(channelChoi_hermitian k).eq, hid] at hp

theorem channelChoi_trace (k : Fin 13) (i j : Fin 2) :
    traceOutput (channelChoi k) i j = if i = j then 1 else 0 := by
  have h := congrArg pairComplex (ICO.QubitGaugeCertificates.channel_trace k i j)
  rw [pairComplex_sum] at h
  unfold traceOutput channelChoi
  rw [← Finset.mul_sum, h]
  split_ifs <;> norm_num [pairComplex]

theorem channelChoi_valid (k : Fin 13) : IsChannelChoi (channelChoi k) :=
  ⟨channelChoi_psd k, channelChoi_trace k⟩

theorem pauliBasis_as_channels (k : Fin 13) :
    pauliBasis k = if k = 0 then (2 : ℂ) • channelChoi 0
      else (2 : ℂ) • channelChoi k - (2 : ℂ) • channelChoi 0 := by
  by_cases hk : k = 0
  · subst k
    simp [channelChoi_zero, pauliBasis_zero, smul_smul]
  · rw [if_neg hk, channelChoi_nonzero k hk, channelChoi_zero]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
    ring

theorem linear_vanishes_on_basis {W : Type*} [AddCommGroup W] [Module ℂ W]
    (L : SlotMatrix →ₗ[ℂ] W) (h : ∀ k, L (channelChoi k) = 0) (k : Fin 13) :
    L (pauliBasis k) = 0 := by
  rw [pauliBasis_as_channels]
  split_ifs <;> simp [h]

/-- Finite CPTP tests suffice for any bilinear observation of two qubit slots. -/
theorem bilinear_vanishes_on_basis {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F : SlotMatrix →ₗ[ℂ] SlotMatrix →ₗ[ℂ] W)
    (h : ∀ A B, IsChannelChoi A → IsChannelChoi B → F A B = 0)
    (k l : Fin 13) : F (pauliBasis k) (pauliBasis l) = 0 := by
  apply linear_vanishes_on_basis (F (pauliBasis k))
  intro j
  let L : SlotMatrix →ₗ[ℂ] W := (LinearMap.applyₗ (channelChoi j)).comp F
  change L (pauliBasis k) = 0
  apply linear_vanishes_on_basis L
  intro i
  exact h _ _ (channelChoi_valid i) (channelChoi_valid j)

def pairing (A X : SlotMatrix) : ℂ := ∑ a, ∑ b, A b a * X a b

def lambdaFour (X : SlotMatrix) (i j : Fin 4) : ℂ :=
  4*X i j - 2*(if i.val%2 = j.val%2 then
    ∑ a : Fin 2, X ⟨2*(i.val/2)+a.val, by omega⟩ ⟨2*(j.val/2)+a.val, by omega⟩
    else 0) + if i = j then Matrix.trace X else 0

theorem lambdaFour_coefficients (X : SlotMatrix) (i j : Fin 4) :
    lambdaFour X i j = ∑ a : Fin 4, ∑ b : Fin 4,
      (ICO.QubitGaugeCertificates.lambdaCoeff i.val j.val a.val b.val : ℂ) * X a b := by
  fin_cases i <;> fin_cases j <;>
    norm_num [lambdaFour, ICO.QubitGaugeCertificates.lambdaCoeff,
      Matrix.trace, Fin.sum_univ_succ, Fin.sum_univ_two, Fin.succ, Fin.castSucc] <;>
    ring_nf

theorem lambdaCoeff_complex (i j a b : Fin 4) :
    (ICO.QubitGaugeCertificates.lambdaCoeff i.val j.val a.val b.val : ℂ) =
      ∑ k : Fin 13, pauliBasis k i j * pauliBasis k b a := by
  have h := congrArg pairComplex (ICO.QubitGaugeCertificates.lambda_expansion i j a b)
  rw [pairComplex_sum] at h
  simp only [pairComplex_mul] at h
  simpa [pauliBasis, pairComplex] using h.symm

theorem lambdaFour_expansion (X : SlotMatrix) (i j : Fin 4) :
    lambdaFour X i j = ∑ k : Fin 13, pauliBasis k i j * pairing (pauliBasis k) X := by
  rw [lambdaFour_coefficients]
  simp_rw [lambdaCoeff_complex, Finset.sum_mul]
  calc
    _ = ∑ a : Fin 4, ∑ k : Fin 13, ∑ b : Fin 4,
        pauliBasis k i j * pauliBasis k b a * X a b := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ k : Fin 13, ∑ a : Fin 4, ∑ b : Fin 4,
        pauliBasis k i j * pauliBasis k b a * X a b := Finset.sum_comm
    _ = _ := by simp [pairing, Finset.mul_sum, mul_assoc]

end
end ICO.QubitCPTPGauge
