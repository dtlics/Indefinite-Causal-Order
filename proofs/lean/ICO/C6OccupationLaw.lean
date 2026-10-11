import ICO.C6PairMarginal

/-! Quantitative diagonal occupation bounds for the common conditional
compression, retaining every reference system. -/
namespace ICO.C6OccupationLaw
open QIT Matrix ICO.C6LabelSymmetry ICO.C6ConditionalCommon ICO.C6LabelPair
  ICO.C6PairMarginal
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A Z : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype Z] [DecidableEq Z]

theorem labelCount_eq_sum (j : A) (n : ℕ) (w : TensorPower A n) :
    (labelCount j n w : ℝ) =
      ∑ i : Fin n, if tensorPowerEquiv n w i = j then (1 : ℝ) else 0 := by
  induction n with
  | zero => simp [labelCount]
  | succ n ih =>
    rcases w with ⟨x, v⟩
    rw [Fin.sum_univ_succ]
    change (((if x = j then 1 else 0) + labelCount j n v : ℕ) : ℝ) =
      (if x = j then 1 else 0) + ∑ i : Fin n, if tensorPowerEquiv n v i = j then 1 else 0
    rw [Nat.cast_add, ih v]
    split_ifs <;> simp

def eventMass (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (i : Fin n) (j a : A) : ℝ :=
  ∑ x : TensorPower A n × Z,
    if tensorPowerEquiv n x.1 i = a then (conditional n ω j x x).re else 0

theorem eventMass_eq_pair (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (i : Fin n) (j a : A) :
    eventMass n ω i j a = (pairMarginal i ω (j, a) (j, a)).re := by
  let e := pairEquiv (A := A) (Z := Z) i
  let f (x : TensorPower A (n + 1) × Z) : ℝ :=
    if x.1.1 = j ∧ tensorPowerEquiv n x.1.2 i = a then (ω x x).re else 0
  have hleft : (∑ x, f x) = eventMass n ω i j a := by
    change (∑ x : (A × TensorPower A n) × Z,
      if x.1.1 = j ∧ tensorPowerEquiv n x.1.2 i = a then (ω x x).re else 0) = _
    simp only [Fintype.sum_prod_type]
    dsimp only [eventMass, conditional, Matrix.submatrix_apply]
    simp only [Fintype.sum_prod_type]
    apply (Finset.sum_eq_single j ?_ ?_).trans
    · simp
      rfl
    · intro b _ hb
      simp [hb]
    · simp
  have hright : (∑ x, f x) = (pairMarginal i ω (j, a) (j, a)).re := by
    rw [← Equiv.sum_comp e.symm f]
    change (∑ x : Spectator A Z i × (A × A),
      if (e.symm x).1.1 = j ∧ tensorPowerEquiv n (e.symm x).1.2 i = a then
        (ω (e.symm x) (e.symm x)).re else 0) = _
    simp only [e, pairEquiv, Equiv.coe_fn_symm_mk, Equiv.apply_symm_apply, assemble_at,
      Fintype.sum_prod_type, ite_and]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp only [pairMarginal, partialTraceA, Matrix.submatrix_apply, e,
      pairEquiv, Equiv.coe_fn_symm_mk]
    simp only [Complex.re_sum, Fintype.sum_prod_type]
  exact hleft.symm.trans hright

def badMass (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) (j a : A) : ℝ :=
  (conditional n ω j - goodProjection n j a * conditional n ω j * goodProjection n j a).trace.re

theorem badMass_eq_sum (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) (j a : A) :
    badMass n ω j a = ∑ x : TensorPower A n × Z,
      if good n j a x then 0 else (conditional n ω j x x).re := by
  simp only [badMass, Matrix.trace, Matrix.diag_apply, Matrix.sub_apply, Complex.re_sum,
    goodProjection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : good n j a x <;> simp [h]

theorem badMass_le_events (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hpos : ω.PosSemidef) (j a : A) :
    badMass n ω j a ≤ ∑ i : Fin n, (eventMass n ω i j j + eventMass n ω i j a) := by
  rw [badMass_eq_sum]
  have hdiag (x : TensorPower A n × Z) : 0 ≤ (conditional n ω j x x).re :=
    diagonal_re_nonneg _ (conditional_pos n ω hpos j) x
  calc
    _ ≤ ∑ x : TensorPower A n × Z,
        ((labelCount j n x.1 : ℝ) + (labelCount a n x.1 : ℝ)) * (conditional n ω j x x).re := by
      apply Finset.sum_le_sum
      intro x _
      by_cases h : good n j a x
      · simp only [h, if_true]
        exact mul_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hdiag x)
      · simp only [h, if_false]
        have hcount : 1 ≤ labelCount j n x.1 + labelCount a n x.1 := by
          unfold good at h
          omega
        have hreal : (1 : ℝ) ≤ (labelCount j n x.1 : ℝ) + (labelCount a n x.1 : ℝ) := by exact_mod_cast hcount
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hreal (hdiag x)
    _ = _ := by
      simp_rw [labelCount_eq_sum, add_mul, Finset.sum_mul]
      simp_rw [← Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [eventMass, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp

theorem badMass_bound (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hpos : ω.PosSemidef) (hω : CommonInvariant (n + 1) ω) (j a : A) (ha : a ≠ j) :
    badMass n ω j a ≤ (n : ℝ) *
      (2 * ω.trace.re / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) +
        ω.trace.re / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) - 1))) := by
  apply (badMass_le_events n ω hpos j a).trans
  calc
    _ ≤ ∑ i : Fin n,
        (2 * ω.trace.re / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) +
          ω.trace.re / ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) - 1))) := by
      apply Finset.sum_le_sum
      intro i _
      rw [eventMass_eq_pair, eventMass_eq_pair]
      have hi := pairMarginal_invariant i ω hω
      have hp := pairMarginal_pos i ω hpos
      have hb := diagonal_bound (pairMarginal i ω) hi (pairMarginal_diagonal_bound i ω hpos hω) j
      have hc := off_diagonal_bound (pairMarginal i ω) hp hi j a ha
      rw [pairMarginal_trace] at hb hc
      exact add_le_add hb hc
    _ = _ := by simp; ring

#print axioms badMass_bound
end
end ICO.C6OccupationLaw
