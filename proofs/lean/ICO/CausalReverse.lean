import QIT.States.MaximallyEntangled
import QIT.Util.SDP.HermitianPSDTraceDuality

/-!+# Causal trace bounds for the reverse-order test

This file develops matrix lemmas used in the reverse-order fidelity bound.
The causal hypothesis is the actual partial-trace identity of a positive comb,
not a hypothesis asserting its final fidelity bound. The Haar-frame identity
and the relation between an operational circuit and its comb remain separate
obligations.

In `causal_bell_cap_bound`, `H` collects the unaffected wires, the two copies
of `A` are a connected input pair, and `F` is the final output wire. Tracing
out `F` leaves `C₂ ⊗ I_A`; the normalized Bell cap then contributes `1 / dim A`.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT

namespace ICO.CausalReverse

noncomputable section

universe u v w

variable {H : Type u} {A : Type v} {F : Type w}

/-- Real trace pairing, including subnormalized positive matrices. -/
def tracePair {N : Type*} [Fintype N] (X Y : CMatrix N) : ℝ :=
  ((X * Y).trace).re

theorem tracePair_comm {N : Type*} [Fintype N] (X Y : CMatrix N) :
    tracePair X Y = tracePair Y X := by
  unfold tracePair
  rw [Matrix.trace_mul_comm]

/-- Right-system version of QIT's left-system partial-trace multiplication
lemma (the analogous lemma in QIT's variational trace-norm module is private). -/
theorem partialTraceB_mul_kronecker_one
    [Fintype H] [Fintype A] [DecidableEq A]
    (X : CMatrix (H × A)) (Y : CMatrix H) :
    partialTraceB (X * Matrix.kronecker Y (1 : CMatrix A)) =
      partialTraceB X * Y := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Pairing with an identity on a discarded wire is the partial-trace pairing. -/
theorem tracePair_kronecker_one
    [Fintype H] [Fintype A] [DecidableEq A]
    (X : CMatrix (H × A)) (Y : CMatrix H) :
    tracePair X (Matrix.kronecker Y (1 : CMatrix A)) =
      tracePair (partialTraceB X) Y := by
  unfold tracePair
  rw [← partialTraceB_mul_kronecker_one X Y, partialTraceB_trace]

/-- Positive trace pairings are monotone in the tested effect. -/
theorem tracePair_mono_right {N : Type*} [Fintype N] [DecidableEq N]
    {X Y Z : CMatrix N} (hX : X.PosSemidef) (hYZ : Y ≤ Z) :
    tracePair X Y ≤ tracePair X Z :=
  cMatrix_trace_mul_le_of_le_posSemidef_left hX hYZ

/-- An instrument outcome is bounded using its parent comb. No normalization
of the selected outcome is inferred from the parent's causal constraints. -/
theorem outcome_test_le_parent {N : Type*} [Fintype N] [DecidableEq N]
    {C Cparent T : CMatrix N} (hT : T.PosSemidef) (hC : C ≤ Cparent) :
    tracePair C T ≤ tracePair Cparent T := by
  rw [tracePair_comm C T, tracePair_comm Cparent T]
  exact tracePair_mono_right hT hC

/-- Tensoring a Loewner inequality with an identity preserves it. -/
theorem kronecker_one_mono [Fintype H] [Fintype A]
    [DecidableEq H] [DecidableEq A] {X Y : CMatrix H} (hXY : X ≤ Y) :
    Matrix.kronecker X (1 : CMatrix A) ≤
      Matrix.kronecker Y (1 : CMatrix A) := by
  rw [Matrix.le_iff] at hXY ⊢
  convert hXY.kronecker (Matrix.PosSemidef.one : (1 : CMatrix A).PosSemidef) using 1
  ext i j
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, sub_mul]

theorem kronecker_one_le_one [Fintype H] [Fintype A]
    [DecidableEq H] [DecidableEq A] {X : CMatrix H} (hX : X ≤ 1) :
    Matrix.kronecker X (1 : CMatrix A) ≤ 1 := by
  simpa using kronecker_one_mono (A := A) hX

/-- A Hermitian idempotent is a bounded effect, proved by squaring its
Hermitian complement. -/
theorem projection_le_one {N : Type*} [Fintype N] [DecidableEq N]
    {P : CMatrix N} (hP : P.IsHermitian) (hPP : P * P = P) : P ≤ 1 := by
  rw [Matrix.le_iff]
  convert Matrix.posSemidef_conjTranspose_mul_self (1 - P) using 1
  simp [Matrix.conjTranspose_sub, hP.eq, Matrix.sub_mul, Matrix.mul_sub, hPP]

/-- Tensoring on the left by a positive matrix preserves Loewner order. -/
theorem kronecker_mono_right [Fintype H] [Fintype A]
    [DecidableEq H] [DecidableEq A] {S : CMatrix H} {X Y : CMatrix A}
    (hS : S.PosSemidef) (hXY : X ≤ Y) :
    Matrix.kronecker S X ≤ Matrix.kronecker S Y := by
  rw [Matrix.le_iff] at hXY ⊢
  convert hS.kronecker hXY using 1
  ext i j
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_sub]

/-- Relabelling tensor coordinates preserves Loewner inequalities. -/
theorem submatrix_mono {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N] {X Y : CMatrix N}
    (hXY : X ≤ Y) (e : M → N) : X.submatrix e e ≤ Y.submatrix e e := by
  rw [Matrix.le_iff] at hXY ⊢
  exact hXY.submatrix e

/-- Canonical normalized Bell-state matrix. -/
def bellMatrix (A : Type v) [Fintype A] [DecidableEq A] [Nonempty A] :
    CMatrix (A × A) :=
  (PureVector.maximallyEntangled (Equiv.refl A)).state.matrix

theorem bellMatrix_pos [Fintype A] [DecidableEq A] [Nonempty A] :
    (bellMatrix A).PosSemidef :=
  (PureVector.maximallyEntangled (Equiv.refl A)).state.pos

theorem bellMatrix_le_one [Fintype A] [DecidableEq A] [Nonempty A] :
    bellMatrix A ≤ 1 := by
  exact projection_le_one
    (PureVector.maximallyEntangled (Equiv.refl A)).state_matrix_isHermitian
    (PureVector.maximallyEntangled (Equiv.refl A)).state_matrix_mul_self

/-- Explicit Bell matrix entries, with the normalization factor visible. -/
theorem bellMatrix_entry [Fintype A] [DecidableEq A] [Nonempty A]
    (i j : A × A) :
    bellMatrix A i j =
      (if i.1 = i.2 then (1 : ℂ) else 0) *
        (if j.1 = j.2 then (1 : ℂ) else 0) / (Fintype.card A : ℂ) := by
  have hd : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card A : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hd))
  have hcoef :
      (Real.sqrt (Fintype.card A : ℝ) : ℂ)⁻¹ *
        star ((Real.sqrt (Fintype.card A : ℝ) : ℂ)⁻¹) =
          (Fintype.card A : ℂ)⁻¹ := by
    rw [star_inv₀]
    simp
    field_simp [hs]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow]
    exact congrArg Complex.ofReal (Real.sq_sqrt hd.le).symm
  have hcoef' : (Real.sqrt (Fintype.card A : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (Fintype.card A : ℝ) : ℂ)⁻¹ = (Fintype.card A : ℂ)⁻¹ := by
    simpa using hcoef
  simp only [bellMatrix, PureVector.state_matrix, rankOneMatrix_apply,
    PureVector.maximallyEntangled_amp, Equiv.refl_apply]
  by_cases hi : i.1 = i.2 <;> by_cases hj : j.1 = j.2 <;>
    simp [hi, hj, hcoef']

/-- The Bell matrix's marginal is exactly `I / dim A`. -/
theorem partialTraceB_bellMatrix [Fintype A] [DecidableEq A] [Nonempty A] :
    partialTraceB (bellMatrix A) =
      (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) • (1 : CMatrix A) := by
  simpa only [bellMatrix, State.marginalA_matrix, State.maximallyMixed_matrix] using
    congrArg State.matrix (PureVector.maximallyEntangled_marginalA (Equiv.refl A))

/-- Effect `T_H ⊗ Bell_AA`, with the first copy of `A` grouped with `H`. -/
def bellCap [Fintype A] [DecidableEq A] [Nonempty A]
    (T : CMatrix H) : CMatrix ((H × A) × A) :=
  fun i j => T i.1.1 j.1.1 * bellMatrix A (i.1.2, i.2) (j.1.2, j.2)

/-- Contracting one half of the Bell cap produces the dimension factor. -/
theorem partialTraceB_bellCap [Fintype H] [Fintype A]
    [DecidableEq A] [Nonempty A] (T : CMatrix H) :
    partialTraceB (bellCap (A := A) T) =
      (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) • Matrix.kronecker T (1 : CMatrix A) := by
  ext i j
  change (∑ k : A, T i.1 j.1 * bellMatrix A (i.2, k) (j.2, k)) = _
  rw [← Finset.mul_sum]
  change T i.1 j.1 * partialTraceB (bellMatrix A) i.2 j.2 = _
  rw [partialTraceB_bellMatrix]
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_comm, mul_left_comm]

/-- Exact causal contraction identity before applying positivity. -/
theorem causal_bell_cap_identity [Fintype H] [Fintype A] [Fintype F]
    [DecidableEq A] [DecidableEq F] [Nonempty A]
    (C : CMatrix (((H × A) × A) × F)) (C₂ : CMatrix (H × A))
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A))
    (T : CMatrix H) :
    tracePair C (Matrix.kronecker (bellCap (A := A) T) (1 : CMatrix F)) =
      (Fintype.card A : ℝ)⁻¹ * tracePair C₂ (Matrix.kronecker T (1 : CMatrix A)) := by
  rw [tracePair_kronecker_one, hcausal, tracePair_comm,
    tracePair_kronecker_one, partialTraceB_bellCap, tracePair_comm]
  simp [tracePair, Matrix.mul_smul, Matrix.trace_smul]

/-- A positive causal component's Bell-cap probability is bounded by its
parent trace divided by the dimension of the connected input wire. -/
theorem causal_bell_cap_bound [Fintype H] [Fintype A] [Fintype F]
    [DecidableEq H] [DecidableEq A] [DecidableEq F] [Nonempty A]
    (C : CMatrix (((H × A) × A) × F)) (C₂ : CMatrix (H × A))
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A))
    (hC₂ : C₂.PosSemidef) (T : CMatrix H) (hT : T ≤ 1) :
    tracePair C (Matrix.kronecker (bellCap (A := A) T) (1 : CMatrix F)) ≤
      (Fintype.card A : ℝ)⁻¹ * C₂.trace.re := by
  rw [causal_bell_cap_identity C C₂ hcausal T]
  apply mul_le_mul_of_nonneg_left
  · simpa [tracePair] using tracePair_mono_right hC₂ (kronecker_one_le_one (A := A) hT)
  · positivity

/-- Dropping a further bounded positive test is justified by Loewner order.
This is the form used after discarding the Bell test on the final output. -/
theorem causal_test_bound [Fintype H] [Fintype A] [Fintype F]
    [DecidableEq H] [DecidableEq A] [DecidableEq F] [Nonempty A]
    (C : CMatrix (((H × A) × A) × F)) (C₂ : CMatrix (H × A))
    (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A))
    (T : CMatrix H) (hT : T ≤ 1) (E : CMatrix (((H × A) × A) × F))
    (hE : E ≤ Matrix.kronecker (bellCap (A := A) T) (1 : CMatrix F)) :
    tracePair C E ≤ (Fintype.card A : ℝ)⁻¹ * C₂.trace.re := by
  exact (tracePair_mono_right hC hE).trans
    (causal_bell_cap_bound C C₂ hcausal hC₂ T hT)

/-! ## Six physical wires

Coordinates are ordered as `(((((P,c),b),a),e),f)`. This is just a permutation
of the paper's `P,a,b,c,e,f` convention, chosen to expose the causal partial
trace over `f` and the Bell contraction over `e`.
-/

abbrev SixWires (A : Type v) := ((((A × A) × A) × A) × A) × A
abbrev FirstFiveWires (A : Type v) := (((A × A) × A) × A) × A
abbrev FirstFourWires (A : Type v) := ((A × A) × A) × A

/-- Regroup the six physical wires into the three Bell pairs `(P,c),(a,e),(b,f)`. -/
def bellPairing (A : Type v) : SixWires A ≃ ((A × A) × (A × A)) × (A × A) where
  toFun x := ((x.1.1.1.1, (x.1.1.2, x.1.2)), (x.1.1.1.2, x.2))
  invFun x := ((((x.1.1, x.2.1), x.1.2.1), x.1.2.2), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The product of the three normalized Bell tests in the leading Haar-frame term. -/
def tripleBell [Fintype A] [DecidableEq A] [Nonempty A] : CMatrix (SixWires A) :=
  (Matrix.kronecker (Matrix.kronecker (bellMatrix A) (bellMatrix A))
    (bellMatrix A)).submatrix (bellPairing A) (bellPairing A)

/-- The leading Bell test is positive. -/
theorem tripleBell_pos [Fintype A] [DecidableEq A] [Nonempty A] :
    (tripleBell (A := A)).PosSemidef := by
  exact ((bellMatrix_pos (A := A)).kronecker (bellMatrix_pos (A := A)) |>.kronecker
    (bellMatrix_pos (A := A))).submatrix (bellPairing A)

/-- Dropping the final `(b,f)` Bell factor is an actual matrix-order inequality. -/
theorem tripleBell_le_cap [Fintype A] [DecidableEq A] [Nonempty A] :
    tripleBell (A := A) ≤
      Matrix.kronecker
        (bellCap (A := A) (Matrix.kronecker (bellMatrix A) (1 : CMatrix A)))
        (1 : CMatrix A) := by
  have h := submatrix_mono
    (kronecker_mono_right
      ((bellMatrix_pos (A := A)).kronecker (bellMatrix_pos (A := A)))
      (bellMatrix_le_one (A := A))) (bellPairing A)
  convert h using 1
  ext i j
  simp [bellCap, bellPairing, Matrix.submatrix, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff, ite_and,
    mul_assoc, mul_left_comm, mul_comm]

/-- The causal normalization enforces the `Tr C₂ / d` bound on the triple
Bell term, even when `C` is an unnormalized positive component. -/
theorem causal_tripleBell_bound [Fintype A] [DecidableEq A] [Nonempty A]
    (C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    tracePair C tripleBell ≤ (Fintype.card A : ℝ)⁻¹ * C₂.trace.re := by
  exact causal_test_bound C C₂ hC hC₂ hcausal
    (Matrix.kronecker (bellMatrix A) (1 : CMatrix A))
    (kronecker_one_le_one (bellMatrix_le_one (A := A))) tripleBell tripleBell_le_cap

/-- The causal trace relation fixes the mass of the parent component. -/
theorem causal_trace_identity [Fintype A] [DecidableEq A]
    (C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    C.trace.re = C₂.trace.re * (Fintype.card A : ℝ) := by
  have h := congrArg (fun M => M.trace.re) hcausal
  simpa [partialTraceB_trace, Matrix.trace_kronecker] using h

/-- Normalization-free form of the leading causal bound. -/
theorem causal_tripleBell_bound_trace [Fintype A] [DecidableEq A] [Nonempty A]
    (C : CMatrix (SixWires A)) (C₂ : CMatrix (FirstFourWires A))
    (hC : C.PosSemidef) (hC₂ : C₂.PosSemidef)
    (hcausal : partialTraceB C = Matrix.kronecker C₂ (1 : CMatrix A)) :
    tracePair C tripleBell ≤ C.trace.re / (Fintype.card A : ℝ) ^ 2 := by
  have h := causal_tripleBell_bound C C₂ hC hC₂ hcausal
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [causal_trace_identity C C₂ hcausal]
  convert h using 1 <;> field_simp [hd] <;> ring

end

end ICO.CausalReverse
