import ICO.MHBellCommute
import ICO.MHUniqueNorm

/-! Concrete Bell columns and distinct-record projectors, with arbitrary
spectator records. Each spectator fixes a forbidden set of labels. -/
namespace ICO.MHBellBlocks
open Matrix QIT
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 0
variable {A Γ : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype Γ] [DecidableEq Γ]

def bellScale : ℝ := (Real.sqrt (Fintype.card A : ℝ))⁻¹

theorem bellScale_sq : (bellScale (A := A)) ^ 2 = (Fintype.card A : ℝ)⁻¹ := by
  simp only [bellScale, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

def bellVector (p : A × A) : ℂ :=
  if p.1 = p.2 then (bellScale (A := A) : ℂ) else 0

theorem bellVector_norm_sq_sum : (∑ p : A × A, ‖bellVector p‖ ^ 2) = 1 := by
  have he (a b : A) : ‖bellVector (a,b)‖ ^ 2 =
      if a = b then (bellScale (A := A)) ^ 2 else 0 := by
    unfold bellVector
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [Fintype.sum_prod_type, he]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, bellScale_sq]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

def bellColumns (good : Γ → Prop) [DecidablePred good] :
    Matrix (Γ × (A × A)) Γ ℂ := fun p γ =>
  if p.1 = γ ∧ good γ then bellVector p.2 else 0

def recordProjection (good : Γ → Prop) [DecidablePred good] (S : Γ → Finset A) :
    CMatrix (Γ × (A × A)) :=
  Matrix.diagonal (fun p => if good p.1 ∧ p.2.2 ∉ S p.1 then 1 else 0)

theorem bellColumns_row_unique (good : Γ → Prop) [DecidablePred good]
    (p : Γ × (A × A)) (i j : Γ) :
    bellColumns good p i ≠ 0 → bellColumns good p j ≠ 0 → i = j := by
  intro hi hj
  have hi' : p.1 = i := by
    by_contra h; exact hi (by simp [bellColumns, h])
  have hj' : p.1 = j := by
    by_contra h; exact hj (by simp [bellColumns, h])
  exact hi'.symm.trans hj'

theorem bellColumns_column_norm (good : Γ → Prop) [DecidablePred good] (γ : Γ) :
    (∑ p : Γ × (A × A), ‖bellColumns good p γ‖ ^ 2) =
      if good γ then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  by_cases hg : good γ
  · simp [bellColumns, hg, apply_ite, bellVector_norm_sq_sum]
  · simp [bellColumns, hg]

theorem bellColumns_norm_le (good : Γ → Prop) [DecidablePred good] :
    ‖bellColumns good (A := A)‖ ≤ 1 := by
  have h := ICO.MHUniqueNorm.row_unique_norm_le (bellColumns good (A := A))
    (bellColumns_row_unique good) 1 (by norm_num) (by
      intro γ; rw [bellColumns_column_norm]; split_ifs <;> norm_num)
  simpa using h

theorem recordProjection_projection (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) : IsStarProjection (recordProjection good S) := by
  constructor
  · show recordProjection good S * recordProjection good S = _
    simp only [recordProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    split_ifs <;> simp
  · change (recordProjection good S).conjTranspose = _
    ext p q
    simp only [recordProjection, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hpq : p = q
    · subst q; simp
    · simp [hpq, Ne.symm hpq]

def forbiddenColumns (good : Γ → Prop) [DecidablePred good] (S : Γ → Finset A) :
    Matrix (Γ × (A × A)) Γ ℂ := fun p γ =>
  if p.1 = γ ∧ good γ ∧ p.2.2 ∈ S γ then bellVector p.2 else 0

theorem one_sub_projection_mul_bell (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) :
    (1 - recordProjection good S) * bellColumns good = forbiddenColumns good S := by
  ext p γ
  simp only [Matrix.sub_mul, Matrix.one_mul, recordProjection,
    Matrix.diagonal_mul, Matrix.sub_apply, bellColumns, forbiddenColumns]
  by_cases h : p.1 = γ
  · subst γ; by_cases hg : good p.1 <;> by_cases hs : p.2.2 ∈ S p.1 <;>
      simp [hg, hs]
  · simp [h]

theorem forbiddenColumns_row_unique (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) (p : Γ × (A × A)) (i j : Γ) :
    forbiddenColumns good S p i ≠ 0 → forbiddenColumns good S p j ≠ 0 → i = j := by
  intro hi hj
  have hi' : p.1 = i := by
    by_contra h; exact hi (by simp [forbiddenColumns, h])
  have hj' : p.1 = j := by
    by_contra h; exact hj (by simp [forbiddenColumns, h])
  exact hi'.symm.trans hj'

theorem forbiddenColumns_column_norm (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) (γ : Γ) :
    (∑ p : Γ × (A × A), ‖forbiddenColumns good S p γ‖ ^ 2) =
      if good γ then (S γ).card / (Fintype.card A : ℝ) else 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  by_cases hg : good γ
  · have he (p : A × A) :
        (∑ g : Γ, ‖forbiddenColumns good S (g,p) γ‖ ^ 2) =
          if p.2 ∈ S γ then ‖bellVector p‖ ^ 2 else 0 := by
      by_cases hs : p.2 ∈ S γ <;> simp [forbiddenColumns, hg, hs, apply_ite]
    simp_rw [he]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have he' (b : A) :
        (∑ a : A, if b ∈ S γ then ‖bellVector (a,b)‖ ^ 2 else 0) =
          if b ∈ S γ then (bellScale (A := A)) ^ 2 else 0 := by
      by_cases hs : b ∈ S γ <;> simp [hs, bellVector, apply_ite,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp_rw [he']
    simp [hg, bellScale_sq, div_eq_mul_inv]
  · simp [forbiddenColumns, hg]

theorem forbiddenColumns_norm_le (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) (t : ℕ) (hcard : ∀ γ, (S γ).card ≤ t) :
    ‖forbiddenColumns good S‖ ≤ Real.sqrt ((t : ℝ) / Fintype.card A) := by
  apply ICO.MHUniqueNorm.row_unique_norm_le (forbiddenColumns good S)
    (forbiddenColumns_row_unique good S) _ (by positivity)
  intro γ
  rw [forbiddenColumns_column_norm]
  split_ifs
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hcard γ) (Nat.cast_nonneg _)
  · positivity

theorem good_bell_commutator_norm_le (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) (t : ℕ) (hcard : ∀ γ, (S γ).card ≤ t) :
    ‖recordProjection good S * (bellColumns good * (bellColumns good).conjTranspose) -
      (bellColumns good * (bellColumns good).conjTranspose) * recordProjection good S‖ ≤
        Real.sqrt ((t : ℝ) / Fintype.card A) := by
  have hb : IsSelfAdjoint (bellColumns good (A := A) *
      (bellColumns good (A := A)).conjTranspose) := by
    change (bellColumns good (A := A) *
      (bellColumns good (A := A)).conjTranspose).conjTranspose = _
    simp
  rw [ICO.MHBellCommute.projection_commutator_norm _ _
    (recordProjection_projection good S) hb]
  rw [← Matrix.mul_assoc (1 - recordProjection good S), one_sub_projection_mul_bell]
  have h := (norm_mul_le (forbiddenColumns good S * (bellColumns good).conjTranspose)
    (recordProjection good S)).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul
        (forbiddenColumns good S) (bellColumns good (A := A)).conjTranspose)
        (norm_nonneg _))
  have hP := (recordProjection_projection good S).norm_le
  have hJ := bellColumns_norm_le good (A := A)
  rw [Matrix.l2_opNorm_conjTranspose] at h
  have h1 := mul_le_mul_of_nonneg_left hP
    (mul_nonneg (norm_nonneg (forbiddenColumns good S))
      (norm_nonneg (bellColumns good (A := A))))
  have h2 := mul_le_mul_of_nonneg_left hJ (norm_nonneg (forbiddenColumns good S))
  have hK := forbiddenColumns_norm_le good S t hcard
  nlinarith [norm_nonneg (forbiddenColumns good S)]

theorem bellFrame_apply (good : Γ → Prop) [DecidablePred good]
    (p q : Γ × (A × A)) :
    (bellColumns good * (bellColumns good).conjTranspose) p q =
      if p.1 = q.1 ∧ good p.1 then bellVector p.2 * star (bellVector q.2) else 0 := by
  rw [Matrix.mul_apply]
  have hs : (∑ γ : Γ, bellColumns good p γ * (bellColumns good).conjTranspose γ q) =
      bellColumns good p p.1 * (bellColumns good).conjTranspose p.1 q := by
    apply Finset.sum_eq_single p.1
    · intro γ _ hγ
      simp [bellColumns, Ne.symm hγ]
    · simp
  rw [hs]
  simp only [Matrix.conjTranspose_apply]
  by_cases hpq : p.1 = q.1
  · have hqp := hpq.symm
    by_cases hg : good p.1 <;> simp [bellColumns, hqp, hg]
  · have hqp : q.1 ≠ p.1 := Ne.symm hpq
    simp [bellColumns, hpq, hqp]

theorem record_mul_full_bell (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) :
    recordProjection good S *
        (bellColumns (fun _ : Γ => True) * (bellColumns (fun _ : Γ => True)).conjTranspose) =
      recordProjection good S * (bellColumns good * (bellColumns good).conjTranspose) := by
  ext p q
  simp only [recordProjection, Matrix.diagonal_mul, bellFrame_apply]
  by_cases hg : good p.1 <;> by_cases hs : p.2.2 ∈ S p.1 <;> simp [hg, hs]

theorem full_bell_commutator_norm_le (good : Γ → Prop) [DecidablePred good]
    (S : Γ → Finset A) (t : ℕ) (hcard : ∀ γ, (S γ).card ≤ t) :
    ‖recordProjection good S *
        (bellColumns (fun _ : Γ => True) * (bellColumns (fun _ : Γ => True)).conjTranspose) -
      (bellColumns (fun _ : Γ => True) * (bellColumns (fun _ : Γ => True)).conjTranspose) *
        recordProjection good S‖ ≤ Real.sqrt ((t : ℝ) / Fintype.card A) := by
  have hr := record_mul_full_bell good S
  have hl := congrArg Matrix.conjTranspose hr
  have hP : (recordProjection good S).conjTranspose = recordProjection good S :=
    (recordProjection_projection good S).isSelfAdjoint.star_eq
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hP] at hl
  rw [hr, hl]
  exact good_bell_commutator_norm_le good S t hcard

#print axioms bellColumns_norm_le
#print axioms one_sub_projection_mul_bell
#print axioms good_bell_commutator_norm_le
#print axioms full_bell_commutator_norm_le
end
end ICO.MHBellBlocks
