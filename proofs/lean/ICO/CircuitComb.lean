import ICO.ReverseFidelity

/-!+# A final circuit channel enforces the causal comb constraint

`postprocessedComb` retains the input of a final channel as an open Choi wire.
The channel is given by an actual finite Stinespring isometry. Positivity and
the homogeneous partial-trace constraint follow from this representation.
This module does not identify arbitrary QC-CC adaptive trees with circuits;
it supplies the concrete final-channel step in that operational bridge.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT

namespace ICO.CircuitComb

set_option maxHeartbeats 1500000

noncomputable section

universe u
variable {H E F N K : Type u}
variable [Fintype H] [Fintype E] [Fintype F] [Fintype N] [Fintype K]
variable [DecidableEq H] [DecidableEq E] [DecidableEq F] [DecidableEq N] [DecidableEq K]

/-- One environment branch of the final Stinespring map, leaving its input
`E` open as a Choi leg. -/
def postLift (W : Matrix (F × K) (E × N) ℂ) (k : K) :
    Matrix ((H × E) × F) (H × N) ℂ :=
  fun i j => if i.1.1 = j.1 then W (i.2, k) (i.1.2, j.2) else 0

/-- Apply the final channel to a positive pre-channel memory operator. -/
def postprocessedComb (W : Matrix (F × K) (E × N) ℂ) (B : CMatrix (H × N)) :
    CMatrix ((H × E) × F) :=
  ∑ k : K, postLift W k * B * (postLift W k).conjTranspose

theorem postprocessedComb_pos (W : Matrix (F × K) (E × N) ℂ)
    {B : CMatrix (H × N)} (hB : B.PosSemidef) :
    (postprocessedComb W B).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ fun k _ =>
    hB.mul_mul_conjTranspose_same (postLift W k)

theorem postprocessedComb_entry (W : Matrix (F × K) (E × N) ℂ)
    (B : CMatrix (H × N)) (h h' : H) (e e' : E) (f f' : F) :
    postprocessedComb W B ((h, e), f) ((h', e'), f') =
      ∑ k : K, ∑ n : N, ∑ m : N,
        W (f, k) (e, n) * B (h, n) (h', m) * star (W (f', k) (e', m)) := by
  simp [postprocessedComb, postLift, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul, apply_ite]
  apply Finset.sum_congr rfl
  intro k hk
  exact Finset.sum_comm

/-- Isometry of the final Stinespring map is exactly the completeness
identity needed when tracing out the final output and environment. -/
theorem post_column_sum (W : Matrix (F × K) (E × N) ℂ)
    (hW : W.conjTranspose * W = 1) (e e' : E) (n m : N) :
    (∑ f : F, ∑ k : K, W (f, k) (e, n) * star (W (f, k) (e', m))) =
      (1 : CMatrix (E × N)) (e, n) (e', m) := by
  have h := congrFun (congrFun hW (e', m)) (e, n)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, eq_comm, mul_comm] using h

theorem sum_four_swap {R : Type*} [AddCommMonoid R]
    (g : F → K → N → N → R) :
    (∑ f : F, ∑ k : K, ∑ n : N, ∑ m : N, g f k n m) =
      ∑ n : N, ∑ m : N, ∑ f : F, ∑ k : K, g f k n m := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (fk : F × K) (nm : N × N) => g fk.1 fk.2 nm.1 nm.2))

/-- Tracing the output of the actual channel yields `Tr_N B ⊗ I_E`. -/
theorem postprocessedComb_causal (W : Matrix (F × K) (E × N) ℂ)
    (hW : W.conjTranspose * W = 1) (B : CMatrix (H × N)) :
    partialTraceB (postprocessedComb W B) =
      Matrix.kronecker (partialTraceB B) (1 : CMatrix E) := by
  ext i j
  rcases i with ⟨h, e⟩
  rcases j with ⟨h', e'⟩
  change (∑ f : F, postprocessedComb W B ((h, e), f) ((h', e'), f)) = _
  simp_rw [postprocessedComb_entry]
  rw [sum_four_swap]
  have hp (n m : N) :
      (∑ f : F, ∑ k : K,
        W (f, k) (e, n) * B (h, n) (h', m) * star (W (f, k) (e', m))) =
        B (h, n) (h', m) * (1 : CMatrix (E × N)) (e, n) (e', m) := by
    rw [← post_column_sum W hW e e' n m]
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  simp_rw [hp]
  simp [partialTraceB, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.ext_iff, ite_and, Finset.sum_mul]

/-- A concrete Stinespring realization satisfies the reverse bound without
assuming a causal partial-trace equation as extra input. -/
theorem postprocessed_reverse_bound {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
    (W : Matrix (A × K) (A × N) ℂ) (hW : W.conjTranspose * W = 1)
    (B : CMatrix (ICO.CausalReverse.FirstFourWires A × N)) (hB : B.PosSemidef) :
    ICO.CausalReverse.tracePair (postprocessedComb W B) (ICO.ReverseFidelity.reverseTest (A := A)) ≤
      ((postprocessedComb W B).trace.re / (Fintype.card A : ℝ) ^ 3) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  exact ICO.ReverseFidelity.causal_reverse_test_bound
    (postprocessedComb W B) (partialTraceB B)
    (postprocessedComb_pos W hB) (partialTraceB_posSemidef hB)
    (postprocessedComb_causal W hW B)

/-- Retain a set of final environment outcomes, without imposing a causal
normalization constraint on the selected outcome itself. -/
def outcomeComb (W : Matrix (F × K) (E × N) ℂ) (B : CMatrix (H × N)) (S : Finset K) :
    CMatrix ((H × E) × F) :=
  ∑ k ∈ S, postLift W k * B * (postLift W k).conjTranspose

theorem outcomeComb_pos (W : Matrix (F × K) (E × N) ℂ)
    {B : CMatrix (H × N)} (hB : B.PosSemidef) (S : Finset K) :
    (outcomeComb W B S).PosSemidef := by
  exact Matrix.posSemidef_sum S fun k _ =>
    hB.mul_mul_conjTranspose_same (postLift W k)

theorem outcomeComb_le_parent (W : Matrix (F × K) (E × N) ℂ)
    {B : CMatrix (H × N)} (hB : B.PosSemidef) (S : Finset K) :
    outcomeComb W B S ≤ postprocessedComb W B := by
  unfold outcomeComb postprocessedComb
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
  intro k hk hnot
  rw [Matrix.le_iff, sub_zero]
  exact hB.mul_mul_conjTranspose_same (postLift W k)

end

end ICO.CircuitComb


