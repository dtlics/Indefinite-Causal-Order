import ICO.RecordingOperatorSupport

/-!
# The finite recording insertions are partial isometries

All matrices include the total relation-size cutoff. This file identifies
their initial projection and proves contraction in the Euclidean norm.
-/

namespace ICO.RecordingPartialIsometry

open ICO.PathRecordingSupport ICO.RecordingOperatorSupport
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem fresh_right_insert_injective {s t : Relation α α} {x z y : α}
    (hs : FreshRight y s) (ht : FreshRight y t)
    (heq : insert (x, y) s = insert (z, y) t) : x = z ∧ s = t := by
  have hy : (x, y) ∈ insert (z, y) t := by
    rw [← heq]
    exact Finset.mem_insert_self _ _
  have hxz : x = z := by
    rcases Finset.mem_insert.mp hy with hy | hy
    · exact (Prod.mk.inj hy).1
    · exact (ht x hy).elim
  subst z
  have herase := congrArg (fun u : Relation α α => u.erase (x, y)) heq
  dsimp only at herase
  rw [Finset.erase_insert (hs x), Finset.erase_insert (ht x)] at herase
  exact ⟨rfl, herase⟩

theorem left_row_unique {o i j : Basis α}
    (hi : leftInsertion o i ≠ 0) (hj : leftInsertion o j ≠ 0) : i = j := by
  obtain ⟨hiR, hif, hiL⟩ := leftInsertion_support hi
  obtain ⟨hjR, hjf, hjL⟩ := leftInsertion_support hj
  obtain ⟨hx, hL⟩ := fresh_right_insert_injective
    (fun x h => hif x (Finset.mem_union_left _ h))
    (fun x h => hjf x (Finset.mem_union_left _ h)) (hiL.symm.trans hjL)
  exact Prod.ext hx (Prod.ext hL (hiR.symm.trans hjR))

theorem right_row_unique {o i j : Basis α}
    (hi : rightInsertion o i ≠ 0) (hj : rightInsertion o j ≠ 0) : i = j := by
  obtain ⟨hiL, hif, hiR⟩ := rightInsertion_support hi
  obtain ⟨hjL, hjf, hjR⟩ := rightInsertion_support hj
  obtain ⟨hx, hR⟩ := fresh_insert_injective
    (fun x h => hif x (Finset.mem_union_right _ h))
    (fun x h => hjf x (Finset.mem_union_right _ h)) (hiR.symm.trans hjR)
  exact Prod.ext hx (Prod.ext (hiL.symm.trans hjL) hR)

omit [DecidableEq α] in
theorem column_orthogonal_of_row_unique {A : Matrix (Basis α) (Basis α) ℂ}
    (hA : ∀ o i j, A o i ≠ 0 → A o j ≠ 0 → i = j)
    {i j : Basis α} (hij : i ≠ j) : (A.conjTranspose * A) i j = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro o _
  by_cases hi : A o i = 0
  · simp [hi]
  · have hj : A o j = 0 := by
      by_contra hj
      exact hij (hA o i j hi hj)
    simp [hj]

def domainProjection : Matrix (Basis α) (Basis α) ℂ :=
  Matrix.diagonal fun i => if i.2.1.card + i.2.2.card < Fintype.card α then 1 else 0

theorem right_column_normSq (i : Basis α)
    (hi : i.2.1.card + i.2.2.card < Fintype.card α) :
    ∑ o, Complex.normSq (rightInsertion o i) = 1 := by
  have hfree : (leftDomain (i.2.1 ∪ i.2.2)).card < Fintype.card α :=
    lt_of_le_of_lt (domain_card_le_records i.2.1 i.2.2) hi
  have h := rightInsertionMatrix_column_normSq i.2.1 i.1 i.2.2 hfree
  rw [Fintype.sum_prod_type] at h ⊢
  have hin (x : α) :
      (∑ lr : Relation α α × Relation α α,
        Complex.normSq (rightInsertion (x, lr) i)) =
      ∑ r, Complex.normSq (rightInsertionMatrix i.2.1 (x, r) (i.1, i.2.2)) := by
    rw [Fintype.sum_prod_type]
    simp only [rightInsertion, RightStep, hi, true_and]
    rw [Finset.sum_eq_single i.2.1]
    · apply Finset.sum_congr rfl
      intro r _
      unfold rightInsertionMatrix
      congr 1
      split_ifs <;> first | rfl | tauto
    · intro l _ hl
      apply Finset.sum_eq_zero
      intro r _
      simp [hl]
    · simp
  simpa only [hin] using h

theorem right_gram_eq_projection :
    (rightInsertion (α := α)).conjTranspose * rightInsertion = domainProjection := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [domainProjection, Matrix.diagonal_apply_eq]
    by_cases hi : i.2.1.card + i.2.2.card < Fintype.card α
    · rw [if_pos hi]
      have h := congrArg (fun r : ℝ => (r : ℂ)) (right_column_normSq i hi)
      simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
        Complex.ofReal_one, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.star_def] using h
    · rw [if_neg hi, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro o _
      simp [rightInsertion, hi]
  · rw [column_orthogonal_of_row_unique (A := rightInsertion)
      (fun _ _ _ hi hj => right_row_unique hi hj) hij]
    simp [domainProjection, Matrix.diagonal_apply_ne _ hij]

theorem domainProjection_norm_le : ‖domainProjection (α := α)‖ ≤ 1 := by
  rw [domainProjection, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  split_ifs <;> norm_num

theorem rightInsertion_norm_le : ‖rightInsertion (α := α)‖ ≤ 1 := by
  have h := domainProjection_norm_le (α := α)
  rw [← right_gram_eq_projection, Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg (rightInsertion (α := α))]

theorem left_column_normSq (i : Basis α)
    (hi : i.2.1.card + i.2.2.card < Fintype.card α) :
    ∑ o, Complex.normSq (leftInsertion o i) = 1 := by
  classical
  let S := (i.2.1 ∪ i.2.2).image Prod.snd
  have hfree : S.card < Fintype.card α :=
    lt_of_le_of_lt (le_trans (Finset.card_image_le) (Finset.card_union_le _ _)) hi
  have hd : (0 : ℝ) < (Fintype.card α : ℝ) - S.card := by
    have h : (S.card : ℝ) < Fintype.card α := by exact_mod_cast hfree
    linarith
  have hfilt : Finset.univ.filter (fun y => FreshRight y (i.2.1 ∪ i.2.2)) = Sᶜ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, S,
      Finset.mem_image, FreshRight]
    constructor
    · intro h ⟨p, hp, hy⟩
      exact h p.1 (hy ▸ hp)
    · intro h x hx
      exact h ⟨(x, y), hx, rfl⟩
  have hin (y : α) :
      (∑ lr : Relation α α × Relation α α,
        Complex.normSq (leftInsertion (y, lr) i)) =
      if FreshRight y (i.2.1 ∪ i.2.2) then
        1 / ((Fintype.card α : ℝ) - S.card) else 0 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    by_cases hf : FreshRight y (i.2.1 ∪ i.2.2)
    · simp only [leftInsertion, LeftStep, hi, hf, true_and]
      rw [Finset.sum_eq_single i.2.2]
      · simp [apply_ite, Complex.normSq_ofReal, S, Real.mul_self_sqrt hd.le]
      · intro r _ hr
        apply Finset.sum_eq_zero
        intro l _
        simp [hr]
      · simp
    · simp [leftInsertion, LeftStep, hi, hf]
  rw [Fintype.sum_prod_type]
  simp_rw [hin]
  rw [Finset.sum_ite]
  simp only [hfilt, Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
  rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ _)]
  field_simp [ne_of_gt hd]

theorem left_gram_eq_projection :
    (leftInsertion (α := α)).conjTranspose * leftInsertion = domainProjection := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [domainProjection, Matrix.diagonal_apply_eq]
    by_cases hi : i.2.1.card + i.2.2.card < Fintype.card α
    · rw [if_pos hi]
      have h := congrArg (fun r : ℝ => (r : ℂ)) (left_column_normSq i hi)
      simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
        Complex.ofReal_one, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.star_def] using h
    · rw [if_neg hi, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro o _
      simp [leftInsertion, hi]
  · rw [column_orthogonal_of_row_unique (A := leftInsertion)
      (fun _ _ _ hi hj => left_row_unique hi hj) hij]
    simp [domainProjection, Matrix.diagonal_apply_ne _ hij]

theorem leftInsertion_norm_le : ‖leftInsertion (α := α)‖ ≤ 1 := by
  have h := domainProjection_norm_le (α := α)
  rw [← left_gram_eq_projection, Matrix.l2_opNorm_conjTranspose_mul_self] at h
  nlinarith [norm_nonneg (leftInsertion (α := α))]

theorem domainProjection_isStarProjection :
    IsStarProjection (domainProjection (α := α)) := by
  refine ⟨?_, ?_⟩
  · change domainProjection * domainProjection = domainProjection (α := α)
    rw [domainProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp_all
  · change (domainProjection (α := α)).conjTranspose = domainProjection
    rw [domainProjection, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    split_ifs <;> simp_all

theorem left_domain_identity :
    leftInsertion (α := α) * domainProjection = leftInsertion := by
  ext o i
  rw [domainProjection, Matrix.mul_diagonal]
  by_cases hi : i.2.1.card + i.2.2.card < Fintype.card α
  · simp [hi]
  · simp [leftInsertion, hi]

theorem right_domain_identity :
    rightInsertion (α := α) * domainProjection = rightInsertion := by
  ext o i
  rw [domainProjection, Matrix.mul_diagonal]
  by_cases hi : i.2.1.card + i.2.2.card < Fintype.card α
  · simp [hi]
  · simp [rightInsertion, hi]

theorem left_degree {o i : Basis α} (h : leftInsertion o i ≠ 0) :
    o.2.1.card + o.2.2.card = i.2.1.card + i.2.2.card + 1 := by
  obtain ⟨hR, hf, hL⟩ := leftInsertion_support h
  have hn : (i.1, o.1) ∉ i.2.1 := fun he => hf i.1 (Finset.mem_union_left _ he)
  rw [hR, hL, Finset.card_insert_of_notMem hn]
  omega

theorem right_degree {o i : Basis α} (h : rightInsertion o i ≠ 0) :
    o.2.1.card + o.2.2.card = i.2.1.card + i.2.2.card + 1 := by
  obtain ⟨hL, hf, hR⟩ := rightInsertion_support h
  have hn : (o.1, i.1) ∉ i.2.2 := fun he => hf i.1 (Finset.mem_union_right _ he)
  rw [hL, hR, Finset.card_insert_of_notMem hn]
  omega

theorem domain_commutes_image_of_degree (A : Matrix (Basis α) (Basis α) ℂ)
    (hdeg : ∀ o i, A o i ≠ 0 →
      o.2.1.card + o.2.2.card = i.2.1.card + i.2.2.card + 1) :
    Commute domainProjection (A * A.conjTranspose) := by
  change domainProjection * (A * A.conjTranspose) =
    (A * A.conjTranspose) * domainProjection
  ext o i
  rw [domainProjection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases he : (A * A.conjTranspose) o i = 0
  · simp [he]
  · obtain ⟨k, hk, hki⟩ := product_nonzero_path _ _ o i he
    have hik : A i k ≠ 0 := adjoint_entry_nonzero _ _ _ hki
    have hsize : o.2.1.card + o.2.2.card = i.2.1.card + i.2.2.card :=
      (hdeg o k hk).trans (hdeg i k hik).symm
    rw [hsize]
    split_ifs <;> simp

theorem domain_commutes_left_image :
    Commute domainProjection
      (leftInsertion (α := α) * leftInsertion.conjTranspose) :=
  domain_commutes_image_of_degree _ (fun _ _ h => left_degree h)

theorem domain_commutes_right_image :
    Commute domainProjection
      (rightInsertion (α := α) * rightInsertion.conjTranspose) :=
  domain_commutes_image_of_degree _ (fun _ _ h => right_degree h)

end
end ICO.RecordingPartialIsometry
