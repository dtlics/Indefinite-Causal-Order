import ICO.SwitchExperiment
import Mathlib.Analysis.Fourier.ZMod

/-! Literal finite clock-phase twirls. The phases are private, and their
uniform conjugation average is exactly the hidden-outcome dephasing channel. -/
namespace ICO.C6OTOCClock
open Matrix QIT ICO.SwitchObservable
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {d : ℕ} [NeZero d]

def phase (k i : ZMod d) : ℂ := ZMod.stdAddChar (k*i)

theorem phase_mul_star (k i j : ZMod d) :
    phase k i * star (phase k j) = ZMod.stdAddChar ((i-j)*k) := by
  have hs : star (ZMod.stdAddChar (k*j)) = ZMod.stdAddChar (-(k*j)) := by
    simpa [Complex.star_def] using
      (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N:=d)) (k*j)).symm
  unfold phase
  rw [hs, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem phase_orthogonal (i j : ZMod d) :
    (∑ k : ZMod d, phase k i * star (phase k j)) =
      if i=j then (d : ℂ) else 0 := by
  simp only [phase_mul_star]
  by_cases h : i=j
  · simp [h]
  · rw [if_neg h]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d (sub_ne_zero.mpr h))

def clock (k : ZMod d) : CMatrix (ZMod d) := Matrix.diagonal (phase k)

theorem clock_isometry (k : ZMod d) : (clock k)ᴴ * clock k = 1 := by
  ext i j
  simp only [clock, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst j
    rw [mul_comm]
    simpa using phase_mul_star k i i
  · rfl

def rotatedClock (U : CMatrix (ZMod d)) (k : ZMod d) : CMatrix (ZMod d) :=
  U * clock k * Uᴴ

theorem clock_twirl (X : CMatrix (ZMod d)) :
    (d : ℂ)⁻¹ • ∑ k : ZMod d, clock k * X * (clock k)ᴴ =
      Matrix.diagonal (fun i => X i i) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, clock, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply, smul_eq_mul, Pi.star_apply]
  have hs : (∑ k : ZMod d, phase k i * X i j * star (phase k j)) =
      X i j * ∑ k : ZMod d, phase k i * star (phase k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hs, phase_orthogonal]
  split_ifs with h
  · subst j
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    field_simp
  · simp

theorem rotatedClock_isometry (U : Matrix.unitaryGroup (ZMod d) ℂ) (k : ZMod d) :
    (rotatedClock (U : CMatrix (ZMod d)) k)ᴴ * rotatedClock U k = 1 := by
  have hu : (U : CMatrix (ZMod d))ᴴ * U = 1 := U.property.1
  have hv : (U : CMatrix (ZMod d)) * (U : CMatrix (ZMod d))ᴴ = 1 := U.property.2
  simp only [rotatedClock, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = (U : CMatrix (ZMod d)) * (clock k)ᴴ * ((U : CMatrix (ZMod d))ᴴ * U) * clock k * (U : CMatrix (ZMod d))ᴴ := by noncomm_ring
    _ = 1 := by rw [hu, Matrix.mul_one]
                rw [Matrix.mul_assoc (U : CMatrix (ZMod d)) (clock k)ᴴ (clock k), clock_isometry, Matrix.mul_one, hv]

theorem single_twirl (X : CMatrix (ZMod d)) :
    (∑ i : ZMod d, Matrix.single i i 1 * X * Matrix.single i i 1) =
      Matrix.diagonal (fun i => X i i) := by
  ext a b
  by_cases h : a=b
  · subst b
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single, Matrix.diagonal_apply, ite_and]
  · simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single, Matrix.diagonal_apply, ite_and, h, Ne.symm h]

theorem basis_channel (U X : CMatrix (ZMod d)) :
    MatrixMap.ofKraus (basisProjection U) X =
      U * Matrix.diagonal (fun i => (Uᴴ * X * U) i i) * Uᴴ := by
  change (∑ i, basisProjection U i * X * (basisProjection U i)ᴴ) = _
  simp only [basisProjection_hermitian]
  rw [← single_twirl]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [basisProjection, Matrix.mul_assoc]

theorem rotatedClock_twirl (U X : CMatrix (ZMod d)) :
    (d : ℂ)⁻¹ • ∑ k : ZMod d, rotatedClock U k * X * (rotatedClock U k)ᴴ =
      MatrixMap.ofKraus (basisProjection U) X := by
  rw [basis_channel, ← clock_twirl]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [rotatedClock, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem sum_rotatedClock_twirl (U X : CMatrix (ZMod d)) :
    (∑ k : ZMod d, rotatedClock U k * X * (rotatedClock U k)ᴴ) =
      (d : ℂ) • MatrixMap.ofKraus (basisProjection U) X := by
  have h := congrArg (fun M : CMatrix (ZMod d) => (d : ℂ) • M)
    (rotatedClock_twirl U X)
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simpa only [smul_smul, mul_inv_cancel₀ hd, one_smul] using h

#print axioms rotatedClock_twirl
#print axioms phase_orthogonal
#print axioms clock_twirl
end
end ICO.C6OTOCClock
