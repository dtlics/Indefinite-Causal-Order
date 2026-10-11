import ICO.C6OccupationLaw
import ICO.RecordingDepolarizing

/-! The dimension-linear dephasing bound for invariant label states. -/
namespace ICO.C6InvariantDephase
open QIT Matrix ICO.C6LabelSymmetry ICO.C6ConditionalCommon ICO.C6OccupationLaw
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A Z : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype Z] [DecidableEq Z]

def pairConstant (n : ℕ) (s : ℝ) : ℝ :=
  2 * (n : ℝ) * (2 * s / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) +
    s / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) - 1)))

theorem conditional_pair_bound (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hpos : ω.PosSemidef) (hω : CommonInvariant (n + 1) ω) (j a : A) (ha : a ≠ j) :
    traceNorm (conditional n ω j - conditional n ω a) ≤ pairConstant (A := A) n ω.trace.re := by
  have h := conditional_traceNorm_le n ω hpos hω j a
  have hj := badMass_bound n ω hpos hω j a ha
  have ha' := badMass_bound n ω hpos hω a j (Ne.symm ha)
  have hgood : goodProjection (Z := Z) n j a = goodProjection n a j := by
    simp only [goodProjection, good, and_comm]
    rfl
  change traceNorm (conditional n ω j - conditional n ω a) ≤
    badMass n ω j a +
      (conditional n ω a - goodProjection n j a * conditional n ω a * goodProjection n j a).trace.re at h
  rw [hgood] at h
  change traceNorm (conditional n ω j - conditional n ω a) ≤ badMass n ω j a + badMass n ω a j at h
  unfold pairConstant
  linarith

def average (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    CMatrix (TensorPower A n × Z) :=
  (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) • ∑ a : A, conditional n ω a

theorem conditional_average_difference (n : ℕ)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (j : A) :
    conditional n ω j - average n ω =
      (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ a : A, (conditional n ω j - conditional n ω a) := by
  unfold average
  rw [Finset.sum_sub_distrib, smul_sub]
  have hs : ∑ _a : A, conditional n ω j = (Fintype.card A : ℂ) • conditional n ω j := by
    simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  rw [hs, smul_smul]
  have hd : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hd]

theorem conditional_average_bound (n : ℕ)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (hpos : ω.PosSemidef)
    (hω : CommonInvariant (n + 1) ω) (j : A) :
    traceNorm (conditional n ω j - average n ω) ≤
      (Fintype.card A : ℝ)⁻¹ * ((Fintype.card A : ℝ) - 1) * pairConstant (A := A) n ω.trace.re := by
  rw [conditional_average_difference, traceNorm_real_smul_eq (by positivity)]
  have hpair (a : A) : traceNorm (conditional n ω j - conditional n ω a) ≤
      if a = j then 0 else pairConstant (A := A) n ω.trace.re := by
    by_cases ha : a = j
    · subst a; simp
    · simp only [ha, if_false]
      exact conditional_pair_bound n ω hpos hω j a ha
  have hsum : ∑ a : A, (if a = j then (0 : ℝ) else pairConstant (A := A) n ω.trace.re) =
      ((Fintype.card A : ℝ) - 1) * pairConstant (A := A) n ω.trace.re := by
    let C := pairConstant (A := A) n ω.trace.re
    change (∑ a : A, if a = j then (0 : ℝ) else C) = ((Fintype.card A : ℝ) - 1) * C
    calc
      _ = ∑ a : A, (C - if a = j then C else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> ring
      _ = (Fintype.card A : ℝ) * C - C := by
        rw [Finset.sum_sub_distrib]
        simp
      _ = _ := by ring
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ a : A, traceNorm (conditional n ω j - conditional n ω a) :=
      mul_le_mul_of_nonneg_left (traceNorm_sum_le_sum_traceNorm _ _) (by positivity)
    _ ≤ (Fintype.card A : ℝ)⁻¹ *
        ∑ a : A, (if a = j then 0 else pairConstant (A := A) n ω.trace.re) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => hpair a)) (by positivity)
    _ = _ := by rw [hsum]; ring

def dephased (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    CMatrix (A × (TensorPower A n × Z)) :=
  QIT.Classical.blockDiagonal (conditional n ω)

def depolarized (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    CMatrix (A × (TensorPower A n × Z)) :=
  QIT.Classical.blockDiagonal (fun _ : A => average n ω)

theorem dephasing_traceNorm_bound (n : ℕ)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (hpos : ω.PosSemidef)
    (hω : CommonInvariant (n + 1) ω) :
    traceNorm (dephased n ω - depolarized n ω) ≤
      6 * (n : ℝ) * ω.trace.re / (Fintype.card A : ℝ) := by
  rw [dephased, depolarized, ← QIT.Classical.blockDiagonal_sub,
    QIT.Classical.traceNorm_blockDiagonal]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    conditional_average_bound n ω hpos hω j)
  have hd : 1 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := A)
  have hs : 0 ≤ ω.trace.re := (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hzero : (Fintype.card A : ℝ) ≠ 0 := by linarith
  have hm : (Fintype.card A : ℝ) - 1 ≠ 0 := by linarith
  have hp : (Fintype.card A : ℝ) + 1 ≠ 0 := by linarith
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  apply h.trans
  unfold pairConstant
  apply (le_div_iff₀ (by linarith : 0 < (Fintype.card A : ℝ))).mpr
  field_simp [hzero, hm, hp]
  nlinarith [mul_nonneg hn hs]

#print axioms conditional_pair_bound
#print axioms dephasing_traceNorm_bound
end
end ICO.C6InvariantDephase
