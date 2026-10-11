import ICO.C6LabelPair
import ICO.C6ConditionalCommon

/-! Actual two-label marginals, including their invariant diagonal laws. -/
namespace ICO.C6PairMarginal
open QIT Matrix ICO.C6LabelSymmetry ICO.C6LabelPair ICO.MHWordRotation
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
universe u
variable {A Γ Z : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype Γ] [DecidableEq Γ] [Fintype Z] [DecidableEq Z]

def TwoInvariant (ρ : CMatrix (A × A)) : Prop :=
  ∀ U : Matrix.unitaryGroup A ℂ, ICO.EqualityTwirl.sameTensor U * ρ =
    ρ * ICO.EqualityTwirl.sameTensor U

theorem marginal_invariant (σ : CMatrix (Γ × (A × A)))
    (S : Matrix.unitaryGroup A ℂ → Matrix.unitaryGroup Γ ℂ)
    (hinv : ∀ U : Matrix.unitaryGroup A ℂ,
      Matrix.kronecker (S U : CMatrix Γ) (ICO.EqualityTwirl.sameTensor U) * σ =
      σ * Matrix.kronecker (S U : CMatrix Γ) (ICO.EqualityTwirl.sameTensor U)) :
    TwoInvariant (partialTraceA σ) := by
  intro U
  let V := tensorUnitary U U
  let R := tensorUnitary (S U) V
  have hR : ((R : CMatrix (Γ × (A × A))).conjTranspose *
      (R : CMatrix (Γ × (A × A)))) = 1 := Matrix.UnitaryGroup.star_mul_self R
  have hc : (R : CMatrix (Γ × (A × A))) * σ = σ * (R : CMatrix (Γ × (A × A))) := hinv U
  have he : (R : CMatrix (Γ × (A × A))).conjTranspose * σ *
      (R : CMatrix (Γ × (A × A))) = σ := by
    rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hR, Matrix.one_mul]
  have hp := partialTraceA_local_unitary_conj σ (S U) V
  change partialTraceA ((R : CMatrix (Γ × (A × A))).conjTranspose * σ *
    (R : CMatrix (Γ × (A × A)))) =
      (V : CMatrix (A × A)).conjTranspose * partialTraceA σ * (V : CMatrix (A × A)) at hp
  rw [he] at hp
  have hV : (V : CMatrix (A × A)) * (V : CMatrix (A × A)).conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.property
  change (V : CMatrix (A × A)) * partialTraceA σ = partialTraceA σ * (V : CMatrix (A × A))
  calc
    _ = (V : CMatrix (A × A)) *
        ((V : CMatrix (A × A)).conjTranspose * partialTraceA σ * (V : CMatrix (A × A))) := by rw [← hp]
    _ = _ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul]

def pairMarginal {n : ℕ} (i : Fin n) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    CMatrix (A × A) :=
  partialTraceA (ω.submatrix (pairEquiv i).symm (pairEquiv i).symm)

theorem pairMarginal_pos {n : ℕ} (i : Fin n)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (hω : ω.PosSemidef) :
    (pairMarginal i ω).PosSemidef := partialTraceA_posSemidef (hω.submatrix _)

theorem pairMarginal_trace {n : ℕ} (i : Fin n) (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    (pairMarginal i ω).trace = ω.trace := by
  rw [pairMarginal, partialTraceA_trace, trace_reindex]

theorem pairMarginal_invariant {n : ℕ} (i : Fin n)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (hω : CommonInvariant (n + 1) ω) :
    TwoInvariant (pairMarginal i ω) := by
  apply marginal_invariant _ (spectatorRotation (Z := Z) i)
  intro U
  let e := pairEquiv (A := A) (Z := Z) i
  have he := congrArg (fun M : CMatrix (TensorPower A (n + 1) × Z) =>
    M.submatrix e.symm e.symm) (hω U)
  dsimp only at he
  rw [common_pair_factor i U,
    ← Matrix.submatrix_mul_equiv _ ω e.symm e.symm e.symm,
    ← Matrix.submatrix_mul_equiv ω _ e.symm e.symm e.symm] at he
  simpa only [e, Matrix.submatrix_submatrix, Function.comp_def, Equiv.apply_symm_apply,
    Matrix.submatrix_id_id] using he

theorem pairMarginal_equality_trace {n : ℕ} (i : Fin n)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) :
    (pairMarginal i ω * ICO.EqualityTwirl.equalityProjector).trace =
      (ω * pairEquality (Z := Z) i).trace := by
  let e := pairEquiv (A := A) (Z := Z) i
  rw [pairMarginal, partialTraceA_mul_trace_eq_trace_mul_kronecker_one_right]
  rw [← trace_reindex e (_ * _), ← Matrix.submatrix_mul_equiv _ _ e e e]
  simp only [e, Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply,
    pairEquality, ICO.MHSpectatorTwirl.lift]
  rfl

theorem pairMarginal_diagonal_bound {n : ℕ} (i : Fin n)
    (ω : CMatrix (TensorPower A (n + 1) × Z)) (hpos : ω.PosSemidef)
    (hω : CommonInvariant (n + 1) ω) :
    (pairMarginal i ω * ICO.EqualityTwirl.equalityProjector).trace.re ≤
      (2 / ((Fintype.card A : ℝ) + 1)) * (pairMarginal i ω).trace.re := by
  rw [pairMarginal_equality_trace, pairMarginal_trace]
  exact pair_equality_bound i ω hpos hω

theorem twoPermutation (e : Equiv.Perm A) :
    ICO.EqualityTwirl.sameTensor (basisPermutation e) =
      ICO.MemoryEmbedding.embedding ⟨e.prodCongr e, (e.prodCongr e).injective⟩ := by
  ext x y
  change (if x.1 = e y.1 then (1 : ℂ) else 0) * (if x.2 = e y.2 then 1 else 0) =
    if x = (e y.1, e y.2) then 1 else 0
  by_cases h : x.1 = e y.1 <;> by_cases ht : x.2 = e y.2 <;> simp [Prod.ext_iff, h, ht]

theorem twoPermutation_invariance (ρ : CMatrix (A × A)) (hρ : TwoInvariant ρ)
    (e : Equiv.Perm A) (x y : A × A) : ρ (e x.1, e x.2) (e y.1, e y.2) = ρ x y := by
  have hc := hρ (basisPermutation e)
  rw [twoPermutation] at hc
  exact embedding_commutation_entry (e.prodCongr e) ρ hc x y

def rowMass (ρ : CMatrix (A × A)) (j : A) : ℝ := ∑ a, (ρ (j, a) (j, a)).re

theorem rowMass_permutation (ρ : CMatrix (A × A)) (hρ : TwoInvariant ρ)
    (e : Equiv.Perm A) (j : A) : rowMass ρ (e j) = rowMass ρ j := by
  unfold rowMass
  rw [← Equiv.sum_comp e (fun a => (ρ (e j, a) (e j, a)).re)]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg Complex.re (twoPermutation_invariance ρ hρ e (j, a) (j, a))

theorem rowMass_uniform (ρ : CMatrix (A × A)) (hρ : TwoInvariant ρ) (j : A) :
    rowMass ρ j = ρ.trace.re / (Fintype.card A : ℝ) := by
  have he (a : A) : rowMass ρ a = rowMass ρ j := by
    simpa only [Equiv.swap_apply_left] using rowMass_permutation ρ hρ (Equiv.swap j a) j
  have htrace : ρ.trace.re = (Fintype.card A : ℝ) * rowMass ρ j := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Fintype.sum_prod_type]
    change (∑ a, rowMass ρ a) = _
    simp [he]
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [htrace, mul_div_cancel_left₀ _ hd]

theorem diagonal_uniform (ρ : CMatrix (A × A)) (hρ : TwoInvariant ρ) (j a : A) :
    ρ (j, j) (j, j) = ρ (a, a) (a, a) := by
  have h := twoPermutation_invariance ρ hρ (Equiv.swap j a) (j, j) (j, j)
  simpa only [Equiv.swap_apply_left] using h.symm

theorem off_diagonal_uniform (ρ : CMatrix (A × A)) (hρ : TwoInvariant ρ)
    (j a b : A) (ha : a ≠ j) (hb : b ≠ j) :
    ρ (j, a) (j, a) = ρ (j, b) (j, b) := by
  have h := twoPermutation_invariance ρ hρ (Equiv.swap a b) (j, a) (j, a)
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb), Equiv.swap_apply_left] at h
  exact h.symm

theorem diagonal_re_nonneg {H : Type u} [Fintype H] [DecidableEq H]
    (ρ : CMatrix H) (hρ : ρ.PosSemidef) (i : H) : 0 ≤ (ρ i i).re := by
  have h := hρ.2 (Finsupp.single i 1)
  have he : 0 ≤ ρ i i := by simpa using h
  exact (Complex.nonneg_iff.mp he).1

theorem equality_trace (ρ : CMatrix (A × A)) :
    (ρ * ICO.EqualityTwirl.equalityProjector).trace.re = ∑ j, (ρ (j, j) (j, j)).re := by
  simp [ICO.EqualityTwirl.equalityProjector, Matrix.mul_diagonal, Matrix.trace,
    Matrix.diag_apply, Complex.re_sum, Fintype.sum_prod_type]

theorem diagonal_bound (ρ : CMatrix (A × A)) (hρ : TwoInvariant ρ)
    (hbound : (ρ * ICO.EqualityTwirl.equalityProjector).trace.re ≤
      (2 / ((Fintype.card A : ℝ) + 1)) * ρ.trace.re) (j : A) :
    (ρ (j, j) (j, j)).re ≤ 2 * ρ.trace.re /
      ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) + 1)) := by
  have hd : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
  rw [equality_trace] at hbound
  have hsame (a : A) : (ρ (a, a) (a, a)).re = (ρ (j, j) (j, j)).re :=
    congrArg Complex.re (diagonal_uniform ρ hρ a j)
  simp only [hsame, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hbound
  apply (le_div_iff₀ (mul_pos hd (by positivity))).mpr
  have h := (mul_le_mul_of_nonneg_right hbound (show 0 ≤ (Fintype.card A : ℝ) + 1 by positivity))
  have hz : (Fintype.card A : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hz] at h
  nlinarith

theorem off_diagonal_bound (ρ : CMatrix (A × A)) (hpos : ρ.PosSemidef)
    (hρ : TwoInvariant ρ) (j a : A) (ha : a ≠ j) :
    (ρ (j, a) (j, a)).re ≤ ρ.trace.re /
      ((Fintype.card A : ℝ) * ((Fintype.card A : ℝ) - 1)) := by
  have hd : 1 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := A)
  have hs : (∑ b ∈ Finset.univ.erase j, (ρ (j, b) (j, b)).re) =
      ((Fintype.card A : ℝ) - 1) * (ρ (j, a) (j, a)).re := by
    have he (b : A) (hb : b ∈ Finset.univ.erase j) :
        (ρ (j, b) (j, b)).re = (ρ (j, a) (j, a)).re :=
      congrArg Complex.re (off_diagonal_uniform ρ hρ j b a (Finset.mem_erase.mp hb).1 ha)
    rw [Finset.sum_congr rfl he]
    simp [Nat.cast_sub (Fintype.card_pos (α := A)), Finset.card_erase_of_mem (Finset.mem_univ j)]
  have hadd := Finset.sum_erase_add Finset.univ (fun b => (ρ (j, b) (j, b)).re) (Finset.mem_univ j)
  rw [hs] at hadd
  change ((Fintype.card A : ℝ) - 1) * (ρ (j, a) (j, a)).re + (ρ (j, j) (j, j)).re = rowMass ρ j at hadd
  have hp := diagonal_re_nonneg ρ hpos (j, j)
  have hle : ((Fintype.card A : ℝ) - 1) * (ρ (j, a) (j, a)).re ≤ rowMass ρ j := by linarith
  have hf : (ρ (j, a) (j, a)).re ≤ rowMass ρ j / ((Fintype.card A : ℝ) - 1) :=
    (le_div_iff₀ (by linarith)).mpr (by simpa only [mul_comm] using hle)
  rw [rowMass_uniform ρ hρ j, div_div] at hf
  exact hf

#print axioms diagonal_bound
#print axioms off_diagonal_bound

#print axioms pairMarginal_invariant
#print axioms rowMass_uniform
end
end ICO.C6PairMarginal
