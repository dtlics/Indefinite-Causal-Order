import ICO.MHBellBlocks
import ICO.MHProjectionCompression

/-! The actual equality-minus-Bell projector and its compression by a
distinct-record projector. -/
namespace ICO.MHBellProjectors
open Matrix QIT ICO.MHBellBlocks
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
variable {A Γ : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype Γ] [DecidableEq Γ]

def equalityProjection : CMatrix (Γ × (A × A)) :=
  Matrix.diagonal (fun p => if p.2.1 = p.2.2 then 1 else 0)

def bellProjection : CMatrix (Γ × (A × A)) :=
  bellColumns (fun _ : Γ => True) * (bellColumns (fun _ : Γ => True)).conjTranspose

theorem true_bell_gram :
    (bellColumns (fun _ : Γ => True) (A := A)).conjTranspose *
      bellColumns (fun _ : Γ => True) (A := A) = 1 := by
  ext γ δ
  by_cases h : γ = δ
  · subst δ
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq]
    have he (z : ℂ) : star z * z = ((‖z‖^2 : ℝ) : ℂ) := by
      rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    simp_rw [he]
    rw [← Complex.ofReal_sum]
    rw [bellColumns_column_norm]
    simp
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_ne h]
    apply Finset.sum_eq_zero
    intro p _
    by_cases hp : p.1 = γ
    · have hδ : p.1 ≠ δ := by intro hx; exact h (hp.symm.trans hx)
      simp [bellColumns, hδ]
    · simp [bellColumns, hp]

theorem bell_projection : IsStarProjection (bellProjection (A := A) (Γ := Γ)) := by
  constructor
  · show bellProjection * bellProjection = (bellProjection (A := A) (Γ := Γ))
    simp only [bellProjection]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc
      (bellColumns (fun _ : Γ => True) (A := A)).conjTranspose,
      true_bell_gram, Matrix.one_mul]
  · change (bellProjection (A := A) (Γ := Γ)).conjTranspose = _
    simp [bellProjection]

theorem equality_projection : IsStarProjection (equalityProjection (A := A) (Γ := Γ)) := by
  constructor
  · show equalityProjection * equalityProjection = (equalityProjection (A := A) (Γ := Γ))
    simp only [equalityProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    split_ifs <;> simp
  · change (equalityProjection (A := A) (Γ := Γ)).conjTranspose = _
    ext p q
    simp only [equalityProjection, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hpq : p = q
    · subst q; simp
    · simp [hpq, Ne.symm hpq]

theorem equality_mul_bell :
    equalityProjection * bellProjection = (bellProjection (A := A) (Γ := Γ)) := by
  have hJ : equalityProjection * bellColumns (fun _ : Γ => True) =
      bellColumns (fun _ : Γ => True) (A := A) := by
    ext p γ
    simp only [equalityProjection, Matrix.diagonal_mul, bellColumns, bellVector]
    by_cases he : p.2.1 = p.2.2 <;> simp [he]
  rw [bellProjection, ← Matrix.mul_assoc, hJ]

theorem projection_difference {H : Type*} [Fintype H] [DecidableEq H]
    (Q B : CMatrix H) (hQ : IsStarProjection Q) (hB : IsStarProjection B)
    (hQB : Q * B = B) : IsStarProjection (Q - B) := by
  have hBQ : B * Q = B := by
    have hh := congrArg Matrix.conjTranspose hQB
    have hQc : Q.conjTranspose = Q := hQ.isSelfAdjoint.star_eq
    have hBc : B.conjTranspose = B := hB.isSelfAdjoint.star_eq
    simpa only [Matrix.conjTranspose_mul, hQc, hBc] using hh
  constructor
  · show (Q-B)*(Q-B) = Q-B
    simp only [Matrix.mul_sub, Matrix.sub_mul, hQ.isIdempotentElem.eq,
      hB.isIdempotentElem.eq, hQB, hBQ]
    abel
  · show star (Q-B) = Q-B
    simp only [star_sub, hQ.isSelfAdjoint.star_eq, hB.isSelfAdjoint.star_eq]

theorem equality_sub_bell_projection :
    IsStarProjection (equalityProjection (A := A) (Γ := Γ) - bellProjection) :=
  projection_difference _ _ equality_projection bell_projection equality_mul_bell

theorem record_equality_commute (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) :
    recordProjection good S * equalityProjection =
      equalityProjection * recordProjection good S := by
  simp only [recordProjection, equalityProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  exact mul_comm _ _

theorem record_compression_le (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) (t : ℕ) (hcard : ∀ γ, (S γ).card ≤ t) :
    recordProjection good S * (equalityProjection - bellProjection) * recordProjection good S ≤
      (equalityProjection - bellProjection) +
        (2 * Real.sqrt ((t : ℝ)/Fintype.card A)) • (1 : CMatrix (Γ × (A × A))) := by
  apply ICO.MHProjectionCompression.compression_le_of_commutator_le _ _
    (recordProjection_projection good S) equality_sub_bell_projection
  have hh := full_bell_commutator_norm_le good S t hcard
  have he : recordProjection good S * (equalityProjection - bellProjection) -
      (equalityProjection - bellProjection) * recordProjection good S =
        -(recordProjection good S * bellProjection - bellProjection * recordProjection good S) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    rw [record_equality_commute]
    abel
  rw [he, norm_neg]
  exact hh

#print axioms record_compression_le
end
end ICO.MHBellProjectors
