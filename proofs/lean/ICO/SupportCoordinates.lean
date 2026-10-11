import ICO.SupportCoordinateFacts
import ICO.TensorRowOperators
import ICO.TensorBitOrder

namespace ICO.SupportCoordinates
open ICO.ExactSeparation ICO.ExactSupportIndependence ICO.ExactTensorCertificates
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
attribute [local irreducible] ICO.ExactSeparation.coordinate ICO.ExactSeparation.coordinateByNat

theorem coordinate_injective : Function.Injective coordinate := by
  intro c d hcd
  have h1 := coordinate_pairIndex c
  have h2 := coordinate_pairIndex d
  rw [← h1, ← h2]
  congr 1 <;> apply Fin.ext <;> simp [hcd]

theorem coordinate_eq_sorted_iff (c : Coord) (a b : Fin 25) :
    coordinate c = (min a.val b.val, max a.val b.val) ↔ c = pairIndex a b := by
  constructor
  · intro h
    apply coordinate_injective
    exact h.trans (pairIndex_coordinate a b).symm
  · intro h
    subst c
    exact pairIndex_coordinate a b

def symmetricBasis (c : Coord) : Matrix (Fin 25) (Fin 25) ℝ := fun a b =>
  (if a.val = (coordinate c).1 ∧ b.val = (coordinate c).2 then 1 else 0) +
    if (coordinate c).1 = (coordinate c).2 then 0 else
      if a.val = (coordinate c).2 ∧ b.val = (coordinate c).1 then 1 else 0

theorem symmetricBasis_entry (c : Coord) (a b : Fin 25) :
    symmetricBasis c a b = if c = pairIndex a b then 1 else 0 := by
  have hb := coordinate_bounds c
  have he := coordinate_eq_sorted_iff c a b
  have hpair : coordinate c = (min a.val b.val, max a.val b.val) ↔
      (a.val = (coordinate c).1 ∧ b.val = (coordinate c).2) ∨
        (a.val = (coordinate c).2 ∧ b.val = (coordinate c).1) := by
    constructor
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp at h1 h2
      omega
    · intro h
      apply Prod.ext <;> dsimp <;> omega
  have hflags := he.symm.trans hpair
  by_cases hc : c = pairIndex a b
  · rw [if_pos hc]
    rcases hflags.mp hc with h | h
    · by_cases hd : (coordinate c).1 = (coordinate c).2
      · simp [symmetricBasis, h, hd]
      · have hn : ¬(a.val = (coordinate c).2 ∧ b.val = (coordinate c).1) := by omega
        simp [symmetricBasis, h, hd, hn]
    · by_cases hd : (coordinate c).1 = (coordinate c).2
      · have hf : a.val = (coordinate c).1 ∧ b.val = (coordinate c).2 := by omega
        simp [symmetricBasis, hf, hd]
      · have hn : ¬(a.val = (coordinate c).1 ∧ b.val = (coordinate c).2) := by omega
        simp [symmetricBasis, hn, hd, h]
  · rw [if_neg hc]
    have hn : ¬((a.val = (coordinate c).1 ∧ b.val = (coordinate c).2) ∨
        (a.val = (coordinate c).2 ∧ b.val = (coordinate c).1)) :=
      fun h => hc (hflags.mpr h)
    have h1 := not_or.mp hn
    simp [symmetricBasis, h1.1, h1.2]

def coefficients (X : Matrix (Fin 25) (Fin 25) ℝ) : Vector :=
  fun c => X ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩
    ⟨(coordinate c).2, (coordinate_bounds c).2⟩

theorem symmetric_matrix_expansion (X : Matrix (Fin 25) (Fin 25) ℝ)
    (hX : ∀ a b, X a b = X b a) :
    X = ∑ c : Coord, coefficients X c • symmetricBasis c := by
  ext a b
  change X a b = ∑ c : Coord, coefficients X c * symmetricBasis c a b
  simp_rw [symmetricBasis_entry]
  rw [Finset.sum_eq_single (pairIndex a b)]
  · rw [if_pos rfl, mul_one]
    unfold coefficients
    simp only [pairIndex_coordinate]
    by_cases hab : a.val ≤ b.val
    · simp only [min_eq_left hab, max_eq_right hab]
    · have hba : b.val ≤ a.val := by omega
      simp only [min_eq_right hba, max_eq_left hba]
      exact hX a b
  · intro c hc hne
    simp [hne]
  · simp

variable {K : Type*} [Fintype K]

def realGram (x : K → Fin 25 → ℂ) : Matrix (Fin 25) (Fin 25) ℝ :=
  fun a b => (∑ k, x k a * star (x k b)).re

theorem realGram_symmetric (x : K → Fin 25 → ℂ) (a b : Fin 25) :
    realGram x a b = realGram x b a := by
  simp only [realGram, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Complex.mul_re, Complex.star_def]
  ring

def realSupport : Matrix (Fin 128) (Fin 25) ℝ :=
  fun i a => (basisEntry i.val a.val : ℝ)

def firstCoordinate (c : Coord) : Fin 25 :=
  ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩

def secondCoordinate (c : Coord) : Fin 25 :=
  ⟨(coordinate c).2, (coordinate_bounds c).2⟩

theorem symmetricBasis_single (c : Coord) :
    symmetricBasis c = Matrix.single (firstCoordinate c) (secondCoordinate c) (1 : ℝ) +
      if firstCoordinate c = secondCoordinate c then 0 else
        Matrix.single (secondCoordinate c) (firstCoordinate c) (1 : ℝ) := by
  ext a b
  simp [symmetricBasis, Matrix.single, firstCoordinate, secondCoordinate,
    Fin.ext_iff, Matrix.add_apply, Matrix.of_apply, ite_apply, eq_comm]
  split_ifs <;> simp_all [Matrix.of_apply]
  all_goals split_ifs <;> simp_all

theorem sandwich_single {m n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix m n ℝ) (a b : n) (i j : m) :
    (E * Matrix.single a b (1 : ℝ) * E.transpose) i j = E i a * E j b := by
  simp [Matrix.mul_apply, Matrix.single, Matrix.transpose_apply,
    Finset.sum_mul, ite_and]

theorem support_basis_coefficient (c : Coord) (i j : Fin 128) :
    (realSupport * symmetricBasis c * realSupport.transpose) i j =
      (choiCoefficient (coordinate c).1 (coordinate c).2 i.val j.val : ℝ) := by
  rw [symmetricBasis_single, Matrix.mul_add, Matrix.add_mul]
  by_cases hd : firstCoordinate c = secondCoordinate c
  · have hn : (coordinate c).1 = (coordinate c).2 := congrArg Fin.val hd
    simp [hd, sandwich_single, choiCoefficient, hn, realSupport,
      firstCoordinate, secondCoordinate]
  · have hn : (coordinate c).1 ≠ (coordinate c).2 := by
      intro h
      apply hd
      exact Fin.ext h
    simp [hd, sandwich_single, choiCoefficient, hn, realSupport,
      firstCoordinate, secondCoordinate]

theorem support_matrix_expansion (X : Matrix (Fin 25) (Fin 25) ℝ)
    (hX : ∀ a b, X a b = X b a) (i j : Fin 128) :
    (realSupport * X * realSupport.transpose) i j =
      ∑ c : Coord, coefficients X c *
        (choiCoefficient (coordinate c).1 (coordinate c).2 i.val j.val : ℝ) := by
  conv_lhs => rw [symmetric_matrix_expansion X hX]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, support_basis_coefficient]

/-- The real Choi matrix of supported Kraus vectors is E Re(XX†) Eᵀ. -/
theorem supported_choi_real (x : K → Fin 25 → ℂ) :
    (fun i j : Fin 128 => (∑ k,
      PositiveSupport.rankOne (encode (x k)) i j).re) =
      realSupport * realGram x * realSupport.transpose := by
  ext i j
  simp only [PositiveSupport.rankOne, Matrix.vecMulVec_apply, encode,
    Pi.star_apply, star_sum, StarMul.star_mul, star_intCast, Matrix.mul_apply, realSupport, realGram,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul, Complex.re_sum]
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.star_def,
    zero_mul, mul_zero, sub_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Complex.mul_im, Complex.intCast_im, Complex.intCast_re,
    zero_mul, mul_zero, zero_add, add_zero]
  ring

end
end ICO.SupportCoordinates
