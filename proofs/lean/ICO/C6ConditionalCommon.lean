import ICO.C6LabelSymmetry
import ICO.CommonPartDistance

/-! A common positive compression for first-label conditional matrices.
The projection excludes two basis values on all remaining labels. -/

namespace ICO.C6ConditionalCommon
open QIT Matrix ICO.C6LabelSymmetry
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1000000

variable {A Z : Type*} [Fintype A] [DecidableEq A] [Fintype Z] [DecidableEq Z]

def conditional (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z)) (j : A) :
    CMatrix (TensorPower A n × Z) :=
  ω.submatrix (fun x => ((j, x.1), x.2)) (fun x => ((j, x.1), x.2))

theorem conditional_pos (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hω : ω.PosSemidef) (j : A) : (conditional n ω j).PosSemidef :=
  hω.submatrix _

def good (n : ℕ) (j a : A) (w : TensorPower A n × Z) : Prop :=
  labelCount j n w.1 = 0 ∧ labelCount a n w.1 = 0

instance (n : ℕ) (j a : A) (w : TensorPower A n × Z) : Decidable (good n j a w) :=
  inferInstanceAs (Decidable (labelCount j n w.1 = 0 ∧ labelCount a n w.1 = 0))

def goodProjection (n : ℕ) (j a : A) : CMatrix (TensorPower A n × Z) :=
  Matrix.diagonal (fun w => if good n j a w then 1 else 0)

theorem goodProjection_adjoint (n : ℕ) (j a : A) :
    (goodProjection (Z := Z) n j a).conjTranspose = goodProjection n j a := by
  rw [goodProjection, Matrix.diagonal_conjTranspose]
  congr 1
  ext w
  simp only [Function.comp_apply, Pi.star_apply]
  split_ifs <;> simp

theorem goodProjection_square (n : ℕ) (j a : A) :
    goodProjection (Z := Z) n j a * goodProjection n j a = goodProjection n j a := by
  rw [goodProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  ext w
  split_ifs <;> simp

theorem conditional_selection (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hω : CommonInvariant (n + 1) ω) (j a : A) (x y : TensorPower A n × Z)
    (hxy : labelCount a n x.1 ≠ labelCount a n y.1) :
    conditional n ω j x y = 0 := by
  apply occupation_selection (n + 1) ω hω a ((j, x.1), x.2) ((j, y.1), y.2)
  change (if j = a then 1 else 0) + labelCount a n x.1 ≠
    (if j = a then 1 else 0) + labelCount a n y.1
  omega

theorem conditional_good_selection (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hω : CommonInvariant (n + 1) ω) (j a : A) (x y : TensorPower A n × Z)
    (hx : good n j a x) (hy : ¬good n j a y) : conditional n ω j x y = 0 := by
  by_cases hj : labelCount j n y.1 = 0
  · have ha : labelCount a n y.1 ≠ 0 := fun h => hy ⟨hj, h⟩
    exact conditional_selection n ω hω j a x y (by rw [hx.2]; exact Ne.symm ha)
  · exact conditional_selection n ω hω j j x y (by rw [hx.1]; exact Ne.symm hj)

theorem conditional_commutes_good (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hω : CommonInvariant (n + 1) ω) (j a : A) :
    goodProjection n j a * conditional n ω j = conditional n ω j * goodProjection n j a := by
  ext x y
  simp only [goodProjection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hx : good n j a x <;> by_cases hy : good n j a y
  · simp [hx, hy]
  · simp [hx, hy, conditional_good_selection n ω hω j a x y hx hy]
  · have he : conditional n ω j x y = 0 := by
      by_cases hj : labelCount j n x.1 = 0
      · have ha : labelCount a n x.1 ≠ 0 := fun h => hx ⟨hj, h⟩
        exact conditional_selection n ω hω j a x y (by rw [hy.2]; exact ha)
      · exact conditional_selection n ω hω j j x y (by rw [hy.1]; exact hj)
    simp [hx, hy, he]
  · simp [hx, hy]

theorem tensor_swap_fixed (n : ℕ) (j a : A) (w : TensorPower A n)
    (hj : labelCount j n w = 0) (ha : labelCount a n w = 0) :
    tensorPerm (Equiv.swap j a) n w = w := by
  induction n with
  | zero => cases w; rfl
  | succ n ih =>
    rcases w with ⟨x, v⟩
    have hxn : x ≠ j := by intro h; subst x; simp [labelCount] at hj
    have hxa : x ≠ a := by intro h; subst x; simp [labelCount] at ha
    have hvj : labelCount j n v = 0 := by simpa [labelCount, hxn] using hj
    have hva : labelCount a n v = 0 := by simpa [labelCount, hxa] using ha
    change (Equiv.swap j a x, tensorPerm (Equiv.swap j a) n v) = (x, v)
    rw [Equiv.swap_apply_of_ne_of_ne hxn hxa, ih v hvj hva]

theorem conditional_common_compression (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hω : CommonInvariant (n + 1) ω) (j a : A) :
    goodProjection n j a * conditional n ω j * goodProjection n j a =
      goodProjection n j a * conditional n ω a * goodProjection n j a := by
  ext x y
  simp only [goodProjection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hx : good n j a x <;> by_cases hy : good n j a y
  · simp only [hx, hy, if_true, one_mul, mul_one]
    have he := permutation_invariance (n + 1) ω hω (Equiv.swap j a)
      ((j, x.1), x.2) ((j, y.1), y.2)
    change ω ((Equiv.swap j a j, tensorPerm (Equiv.swap j a) n x.1), x.2)
      ((Equiv.swap j a j, tensorPerm (Equiv.swap j a) n y.1), y.2) = _ at he
    rw [Equiv.swap_apply_left, tensor_swap_fixed n j a x.1 hx.1 hx.2,
      tensor_swap_fixed n j a y.1 hy.1 hy.2] at he
    exact he.symm
  all_goals simp [hx, hy]

theorem commuting_remainder {H : Type*} [Fintype H] [DecidableEq H]
    (σ P : CMatrix H) (hσ : σ.PosSemidef) (hPsq : P * P = P)
    (hPstar : P.conjTranspose = P) (hc : P * σ = σ * P) :
    (σ - P * σ * P).PosSemidef := by
  have hPσP : P * σ * P = P * σ := by rw [hc, Matrix.mul_assoc, hPsq, ← hc]
  have he : σ - P * σ * P = (1 - P).conjTranspose * σ * (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPstar]
    have hform : (1 - P) * σ * (1 - P) = σ - P * σ - σ * P + P * σ * P := by noncomm_ring
    rw [hform, hPσP, hc]
    abel
  rw [he]
  exact hσ.conjTranspose_mul_mul_same _

theorem common_compression_traceNorm {H : Type*} [Fintype H] [DecidableEq H]
    (σ τ P : CMatrix H) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (hPsq : P * P = P) (hPstar : P.conjTranspose = P)
    (hcσ : P * σ = σ * P) (hcτ : P * τ = τ * P)
    (hcommon : P * σ * P = P * τ * P) :
    traceNorm (σ - τ) ≤
      (σ - P * σ * P).trace.re + (τ - P * τ * P).trace.re := by
  have hs := commuting_remainder σ P hσ hPsq hPstar hcσ
  have ht := commuting_remainder τ P hτ hPsq hPstar hcτ
  have he : σ - τ = (σ - P * σ * P) + -(τ - P * τ * P) := by rw [← hcommon]; abel
  rw [he]
  calc
    _ ≤ traceNorm (σ - P * σ * P) + traceNorm (-(τ - P * τ * P)) := traceNorm_add_le _ _
    _ = _ := by rw [traceNorm_neg, traceNorm_posSemidef_eq_trace_re _ hs,
      traceNorm_posSemidef_eq_trace_re _ ht]

theorem conditional_traceNorm_le (n : ℕ) (ω : CMatrix (TensorPower A (n + 1) × Z))
    (hpos : ω.PosSemidef) (hω : CommonInvariant (n + 1) ω) (j a : A) :
    traceNorm (conditional n ω j - conditional n ω a) ≤
      (conditional n ω j - goodProjection n j a * conditional n ω j * goodProjection n j a).trace.re +
      (conditional n ω a - goodProjection n j a * conditional n ω a * goodProjection n j a).trace.re := by
  apply common_compression_traceNorm _ _ _ (conditional_pos n ω hpos j)
    (conditional_pos n ω hpos a) (goodProjection_square n j a) (goodProjection_adjoint n j a)
    (conditional_commutes_good n ω hω j a)
  · simpa only [goodProjection, good, and_comm] using conditional_commutes_good n ω hω a j
  · exact conditional_common_compression n ω hω j a

#print axioms conditional_common_compression
#print axioms conditional_traceNorm_le
end
end ICO.C6ConditionalCommon
