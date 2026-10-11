import ICO.MHCreationCovariance
import ICO.MHOccupationCounts

/-! The symmetric creation map has the exact multiset coefficient
`sqrt(count + 1)`, including repetitions. -/

namespace ICO.MHCreationCoefficients

open QIT ICO.MHSymmetric ICO.MHCreationCovariance ICO.MHOccupationCounts
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section
set_option maxHeartbeats 1000000

variable {a : Type*} [Fintype a] [DecidableEq a]

theorem incrementProfile_word {n : ℕ} (z : a) (p : TensorPowerProfile a n)
    (w : TensorPower a n) (hw : w ∈ tensorPowerProfileClass p) :
    tensorPowerTypeProfile (n + 1) (z, w) = (incrementProfile z p).val := by
  funext x
  rw [tensorPowerTypeProfile_succ, incrementProfile_apply,
    (mem_tensorPowerProfileClass p w).mp hw]

theorem prepend_profile_mem {n : ℕ} (z : a) (p : TensorPowerProfile a n)
    (q : TensorPowerProfile a (n + 1)) (w : TensorPower a n)
    (hw : w ∈ tensorPowerProfileClass p) :
    ((z, w) : TensorPower a (n + 1)) ∈ tensorPowerProfileClass (a := a) (n := n + 1) q ↔ q = incrementProfile z p := by
  erw [mem_tensorPowerProfileClass (a := a) (n := n + 1) q (z, w), incrementProfile_word z p w hw]
  exact ⟨fun h => Subtype.ext h.symm, fun h => by rw [h]⟩

theorem creationOccupation_eq_compression (n : ℕ) (v : a → ℂ) :
    creationOccupation n v = (Real.sqrt (n + 1) : ℂ) •
      ((occupationEmbedding (a := a) (n + 1)).conjTranspose *
        prepend n v * occupationEmbedding (a := a) n) := by
  unfold creationOccupation creationWord
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    occupationEmbedding_adjoint_projection, Matrix.mul_assoc,
    Matrix.mul_assoc, symmetricProjection_occupationEmbedding]
  exact (Matrix.mul_assoc _ _ _).symm

theorem compressed_prepend_entry (n : ℕ) (z : a)
    (q : TensorPowerProfile a (n + 1)) (p : TensorPowerProfile a n) :
    ((occupationEmbedding (a := a) (n + 1)).conjTranspose *
      prepend n (basisVector z) * occupationEmbedding (a := a) n) q p =
    ∑ w : TensorPower a n, star (tensorPowerProfileUnitVector q (z, w)) *
      tensorPowerProfileUnitVector p w := by
  rw [Matrix.mul_assoc]
  change (∑ s : a × TensorPower a n,
      star (tensorPowerProfileUnitVector q s) *
        ∑ w : TensorPower a n,
          ((if s.1 = z then 1 else 0) * if s.2 = w then 1 else 0) *
            tensorPowerProfileUnitVector p w) = _
  simp only [Fintype.sum_prod_type]
  simp [mul_ite, ite_mul, Finset.mul_sum]

theorem compressed_prepend_card (n : ℕ) (z : a)
    (q : TensorPowerProfile a (n + 1)) (p : TensorPowerProfile a n) :
    ((occupationEmbedding (a := a) (n + 1)).conjTranspose *
      prepend n (basisVector z) * occupationEmbedding (a := a) n) q p =
    if q = incrementProfile z p then
      (tensorPowerProfileClass p).card *
        ((Real.sqrt (tensorPowerProfileClass q).card : ℂ)⁻¹ *
          (Real.sqrt (tensorPowerProfileClass p).card : ℂ)⁻¹)
    else 0 := by
  rw [compressed_prepend_entry]
  have hsum : (∑ w : TensorPower a n, star (tensorPowerProfileUnitVector q (z, w)) *
      tensorPowerProfileUnitVector p w) =
    ∑ w ∈ tensorPowerProfileClass p, star (tensorPowerProfileUnitVector q (z, w)) *
      tensorPowerProfileUnitVector p w := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w _ hw
    simp [tensorPowerProfileUnitVector_apply, hw]
  rw [hsum]
  by_cases h : q = incrementProfile z p
  · rw [if_pos h]
    calc
      _ = ∑ _w ∈ tensorPowerProfileClass p,
          ((Real.sqrt (tensorPowerProfileClass q).card : ℂ)⁻¹ *
            (Real.sqrt (tensorPowerProfileClass p).card : ℂ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hmem := (prepend_profile_mem z p q w hw).mpr h
        rw [tensorPowerProfileUnitVector_apply, tensorPowerProfileUnitVector_apply,
          if_pos hw]
        erw [if_pos hmem]
        simp
      _ = _ := by simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro w hw
    have hmem : ((z, w) : TensorPower a (n + 1)) ∉ tensorPowerProfileClass (a := a) (n := n + 1) q :=
      fun hmem => h ((prepend_profile_mem z p q w hw).mp hmem)
    rw [tensorPowerProfileUnitVector_apply]
    erw [if_neg hmem]
    simp

theorem sqrt_card_amplitude (N A B C : ℕ) (hA : 0 < A) (hB : 0 < B)
    (h : C * B = N * A) :
    (Real.sqrt N : ℂ) * ((A : ℂ) *
      ((Real.sqrt B : ℂ)⁻¹ * (Real.sqrt A : ℂ)⁻¹)) = (Real.sqrt C : ℂ) := by
  have hAr : 0 < (A : ℝ) := by exact_mod_cast hA
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  have hAs : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hAr)
  have hBs : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hBr)
  have hr : (C : ℝ) * B = N * A := by exact_mod_cast h
  have heq : Real.sqrt N * Real.sqrt A = Real.sqrt C * Real.sqrt B := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg N), ← Real.sqrt_mul (Nat.cast_nonneg C), hr]
  have hreal : Real.sqrt N * ((A : ℝ) * ((Real.sqrt B)⁻¹ * (Real.sqrt A)⁻¹)) =
      Real.sqrt C := by
    field_simp
    calc
      Real.sqrt N * A = Real.sqrt N * (Real.sqrt A * Real.sqrt A) := by
        rw [Real.mul_self_sqrt (le_of_lt hAr)]
      _ = Real.sqrt C * Real.sqrt B * Real.sqrt A := by rw [← mul_assoc, heq]
      _ = _ := by ring
  exact_mod_cast hreal

/-- The exact occupation-basis entry of bosonic creation, with the required
`+1` even when the appended symbol already occurs. -/
theorem creationOccupation_basis_entry (n : ℕ) (z : a)
    (q : TensorPowerProfile a (n + 1)) (p : TensorPowerProfile a n) :
    creationOccupation n (basisVector z) q p =
      if q = incrementProfile z p then (Real.sqrt (p.val z + 1) : ℂ) else 0 := by
  rw [creationOccupation_eq_compression, Matrix.smul_apply, smul_eq_mul,
    compressed_prepend_card]
  by_cases h : q = incrementProfile z p
  · rw [if_pos h, if_pos h]
    subst q
    have hc := sqrt_card_amplitude (n + 1) (tensorPowerProfileClass p).card
      (tensorPowerProfileClass (incrementProfile z p)).card (p.val z + 1)
      p.class_card_pos (incrementProfile z p).class_card_pos
      (increment_class_card_ratio z p)
    simpa only [Nat.cast_add, Nat.cast_one] using hc
  · simp [h]

end
end ICO.MHCreationCoefficients


