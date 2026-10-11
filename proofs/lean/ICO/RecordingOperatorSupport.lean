import ICO.PathRecordingSupport

/-!
# Support of the actual inverse-recording matrix expansion

This file relates nonzero matrix entries of `V† = A† - BB†A† + B - BAA†`
to the branch relation already used in the finite support invariant. The
finite matrices retain the insertion rules and the total-size cutoff.
Their embedding in the variable-length multiset Hilbert space is separate.
-/

namespace ICO.RecordingOperatorSupport

open ICO.PathRecordingSupport
open scoped BigOperators Matrix

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Basis (α : Type*) := α × Relation α α × Relation α α

def LeftStep (i o : Basis α) : Prop :=
  o.2.2 = i.2.2 ∧ FreshRight o.1 (i.2.1 ∪ i.2.2) ∧
    o.2.1 = insert (i.1, o.1) i.2.1

def RightStep (i o : Basis α) : Prop :=
  o.2.1 = i.2.1 ∧ FreshLeft o.1 (i.2.1 ∪ i.2.2) ∧
    o.2.2 = insert (o.1, i.1) i.2.2

def leftInsertion : Matrix (Basis α) (Basis α) ℂ := by
  classical
  exact fun o i => if i.2.1.card + i.2.2.card < Fintype.card α ∧ LeftStep i o then
    (((Real.sqrt ((Fintype.card α : ℝ) -
      (((i.2.1 ∪ i.2.2).image Prod.snd).card : ℝ)))⁻¹ : ℝ) : ℂ) else 0

def rightInsertion : Matrix (Basis α) (Basis α) ℂ := by
  classical
  exact fun o i => if i.2.1.card + i.2.2.card < Fintype.card α ∧ RightStep i o then
    (((Real.sqrt ((Fintype.card α : ℝ) -
      ((leftDomain (i.2.1 ∪ i.2.2)).card : ℝ)))⁻¹ : ℝ) : ℂ) else 0

theorem leftInsertion_support {i o : Basis α} (h : leftInsertion o i ≠ 0) :
    LeftStep i o := by
  classical
  unfold leftInsertion at h
  split_ifs at h with hs
  · exact hs.2
  · exact (h rfl).elim

theorem rightInsertion_support {i o : Basis α} (h : rightInsertion o i ≠ 0) :
    RightStep i o := by
  classical
  unfold rightInsertion at h
  split_ifs at h with hs
  · exact hs.2
  · exact (h rfl).elim

omit [Fintype α] in
theorem reverse_left_data {i o : Basis α} (h : LeftStep o i) :
    (o.1, i.1) ∈ i.2.1 ∧ o.2.1 = i.2.1.erase (o.1, i.1) ∧ o.2.2 = i.2.2 := by
  obtain ⟨hr, hf, hl⟩ := h
  have hn : (o.1, i.1) ∉ o.2.1 := by
    intro he
    exact hf o.1 (Finset.mem_union_left _ he)
  refine ⟨?_, ?_, hr.symm⟩
  · rw [hl]
    exact Finset.mem_insert_self _ _
  · rw [hl, Finset.erase_insert hn]

omit [Fintype α] in
theorem reverse_right_data {i o : Basis α} (h : RightStep o i) :
    (i.1, o.1) ∈ i.2.2 ∧ o.2.2 = i.2.2.erase (i.1, o.1) ∧ o.2.1 = i.2.1 := by
  obtain ⟨hl, hf, hr⟩ := h
  have hn : (i.1, o.1) ∉ o.2.2 := by
    intro he
    exact hf o.1 (Finset.mem_union_right _ he)
  refine ⟨?_, ?_, hl.symm⟩
  · rw [hr]
    exact Finset.mem_insert_self _ _
  · rw [hr, Finset.erase_insert hn]

omit [Fintype α] in
theorem branch_reverse_left {i o : Basis α} (h : LeftStep o i) :
    InverseBranch i.2.1 i.2.2 o.2.1 o.2.2 o.1 := by
  obtain ⟨he, hl, hr⟩ := reverse_left_data h
  rw [hl, hr]
  exact InverseBranch.removeLeft he

omit [Fintype α] in
theorem branch_insert_right {i o : Basis α} (h : RightStep i o) :
    InverseBranch i.2.1 i.2.2 o.2.1 o.2.2 o.1 := by
  obtain ⟨hl, hf, hr⟩ := h
  rw [hl, hr]
  apply InverseBranch.insertRight
  · intro y hy
    exact hf y (Finset.mem_union_left _ hy)
  · intro y hy
    exact hf y (Finset.mem_union_right _ hy)

omit [Fintype α] in
theorem branch_reverse_left_right_projector {i j k o : Basis α}
    (hA : LeftStep j i) (hBd : RightStep k j) (hB : RightStep k o) :
    InverseBranch i.2.1 i.2.2 o.2.1 o.2.2 o.1 := by
  obtain ⟨heL, hjL, hjR⟩ := reverse_left_data hA
  obtain ⟨heR, hkR, hkL⟩ := reverse_right_data hBd
  obtain ⟨hoL, hf, hoR⟩ := hB
  have hL : k.2.1 = i.2.1.erase (j.1, i.1) := hkL.trans hjL
  have hR : k.2.2 = i.2.2.erase (j.1, k.1) := by simpa only [hjR] using hkR
  rw [hoL, hoR, hL, hR]
  apply InverseBranch.removeLeftMoveRight heL
  · simpa only [hjR] using heR
  · intro y hy
    exact hf y (Finset.mem_union_left _ (hL.symm ▸ hy))
  · intro y hy
    exact hf y (Finset.mem_union_right _ (hR.symm ▸ hy))

omit [Fintype α] in
theorem branch_left_projector_insert_right {i j k o : Basis α}
    (hAd : LeftStep j i) (hA : LeftStep j k) (hB : RightStep k o) :
    InverseBranch i.2.1 i.2.2 o.2.1 o.2.2 o.1 := by
  obtain ⟨he, hjL, hjR⟩ := reverse_left_data hAd
  obtain ⟨hkR, hfA, hkL⟩ := hA
  obtain ⟨hoL, hfB, hoR⟩ := hB
  have hL : k.2.1 = insert (j.1, k.1) (i.2.1.erase (j.1, i.1)) := by
    simpa only [hjL] using hkL
  have hR : k.2.2 = i.2.2 := hkR.trans hjR
  rw [hoL, hoR, hL, hR]
  apply InverseBranch.moveLeftInsertRight he
  · intro x hx
    exact hfA x (Finset.mem_union_left _ (hjL.symm ▸ hx))
  · intro y hy
    exact hfB y (Finset.mem_union_left _ (hL.symm ▸ hy))
  · intro y hy
    exact hfB y (Finset.mem_union_right _ (hR.symm ▸ hy))

/-- A nonzero finite matrix product has a nonzero contributing path. -/
theorem product_nonzero_path {σ τ υ : Type*} [Fintype τ]
    (M : Matrix σ τ ℂ) (N : Matrix τ υ ℂ) (o : σ) (i : υ)
    (h : (M * N) o i ≠ 0) : ∃ j, M o j ≠ 0 ∧ N j i ≠ 0 := by
  rw [Matrix.mul_apply] at h
  obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨j, (mul_ne_zero_iff.mp hj).1, (mul_ne_zero_iff.mp hj).2⟩

theorem adjoint_entry_nonzero {σ τ : Type*} (M : Matrix σ τ ℂ) (i : σ) (o : τ)
    (h : M.conjTranspose o i ≠ 0) : M i o ≠ 0 := by
  intro hz
  exact h (by simp [Matrix.conjTranspose_apply, hz])

/-- The inverse recording expansion with the two overlap corrections. -/
def inverseRecording : Matrix (Basis α) (Basis α) ℂ :=
  leftInsertion.conjTranspose -
    rightInsertion * rightInsertion.conjTranspose * leftInsertion.conjTranspose +
    rightInsertion - rightInsertion * leftInsertion * leftInsertion.conjTranspose

/-- Every nonzero entry of the actual inverse matrix follows one of the four
    support branches. Cancellation of amplitudes cannot create a new branch. -/
theorem inverseRecording_support {i o : Basis α} (h : inverseRecording o i ≠ 0) :
    InverseBranch i.2.1 i.2.2 o.2.1 o.2.2 o.1 := by
  classical
  by_cases hA : leftInsertion.conjTranspose o i ≠ 0
  · exact branch_reverse_left (leftInsertion_support (adjoint_entry_nonzero _ _ _ hA))
  by_cases hBBA : ((rightInsertion (α := α) * rightInsertion.conjTranspose *
      leftInsertion.conjTranspose) : Matrix (Basis α) (Basis α) ℂ) o i ≠ 0
  · obtain ⟨j, hBB, hAd⟩ := product_nonzero_path _ _ o i hBBA
    obtain ⟨k, hB, hBd⟩ := product_nonzero_path _ _ o j hBB
    exact branch_reverse_left_right_projector
      (leftInsertion_support (adjoint_entry_nonzero _ _ _ hAd))
      (rightInsertion_support (adjoint_entry_nonzero _ _ _ hBd))
      (rightInsertion_support hB)
  by_cases hB : rightInsertion o i ≠ 0
  · exact branch_insert_right (rightInsertion_support hB)
  by_cases hBAA : ((rightInsertion (α := α) * leftInsertion * leftInsertion.conjTranspose) :
      Matrix (Basis α) (Basis α) ℂ) o i ≠ 0
  · obtain ⟨j, hBA, hAd⟩ := product_nonzero_path _ _ o i hBAA
    obtain ⟨k, hB', hA'⟩ := product_nonzero_path _ _ o j hBA
    exact branch_left_projector_insert_right
      (leftInsertion_support (adjoint_entry_nonzero _ _ _ hAd))
      (leftInsertion_support hA') (rightInsertion_support hB')
  · apply False.elim
    apply h
    simp only [not_not] at hA hBBA hB hBAA
    simp only [inverseRecording, Matrix.sub_apply, Matrix.add_apply, hA, hBBA, hB, hBAA,
      sub_self, add_zero]

/-- The matrix support bridge discharges the abstract branch premise. -/
theorem inverseRecording_preserves {i o : Basis α} (h : inverseRecording o i ≠ 0)
    (hgood : Good i.2.1 i.2.2) :
    Good o.2.1 o.2.2 ∧ FreshLeft o.1 o.2.1 ∧
      o.2.1.card + o.2.2.card ≤ i.2.1.card + i.2.2.card + 1 :=
  inverse_branch_preserves hgood (inverseRecording_support h)

theorem vector_nonzero_path {σ τ : Type*} [Fintype τ]
    (M : Matrix σ τ ℂ) (ψ : τ → ℂ) (o : σ) (h : (M *ᵥ ψ) o ≠ 0) :
    ∃ i, M o i ≠ 0 ∧ ψ i ≠ 0 := by
  change (∑ i, M o i * ψ i) ≠ 0 at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨i, (mul_ne_zero_iff.mp hi).1, (mul_ne_zero_iff.mp hi).2⟩

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

omit [Fintype μ] in
/-- A nonzero tensor-extended inverse entry has a nonzero recording entry. -/
theorem inverse_with_memory_entry {i o : Basis α × μ}
    (h : Matrix.kronecker inverseRecording (1 : Matrix μ μ ℂ) o i ≠ 0) :
    inverseRecording o.1 i.1 ≠ 0 := by
  intro hz
  exact h (by simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hz])

/-- Applying the inverse recording matrix preserves the invariant on an
    arbitrary entangled amplitude vector with quantum memory. -/
theorem inverse_with_memory_support (ψ : Basis α × μ → ℂ) (m : ℕ)
    (hψ : ∀ i, ψ i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) (o : Basis α × μ)
    (ho : ((Matrix.kronecker inverseRecording (1 : Matrix μ μ ℂ)) *ᵥ ψ) o ≠ 0) :
    Good o.1.2.1 o.1.2.2 ∧ FreshLeft o.1.1 o.1.2.1 ∧
      o.1.2.1.card + o.1.2.2.card ≤ m + 1 := by
  obtain ⟨i, hM, hi⟩ := vector_nonzero_path _ ψ o ho
  obtain ⟨hg, hsize⟩ := hψ i hi
  obtain ⟨hg', hf, hsize'⟩ := inverseRecording_preserves (inverse_with_memory_entry hM) hg
  exact ⟨hg', hf, by omega⟩

/-- The growing-only left insertion restores the completed-wrapper invariant. -/
theorem leftInsertion_preserves {i o : Basis α} (h : leftInsertion o i ≠ 0)
    (hgood : Good i.2.1 i.2.2) (hf : FreshLeft i.1 i.2.1) :
    Good o.2.1 o.2.2 ∧ o.2.1.card + o.2.2.card ≤ i.2.1.card + i.2.2.card + 1 := by
  obtain ⟨hr, hfr, hl⟩ := leftInsertion_support h
  obtain ⟨hgL, hgR, hgRR⟩ := hgood
  rw [hr, hl]
  have hy : FreshRight o.1 i.2.1 := by
    intro x hx
    exact hfr x (Finset.mem_union_left _ hx)
  refine ⟨⟨leftUnique_insert hgL hf, rightUnique_insert hgR hy, hgRR⟩, ?_⟩
  have hc := Finset.card_insert_le (i.1, o.1) i.2.1
  omega

theorem leftInsertion_with_memory_support (ψ : Basis α × μ → ℂ) (m : ℕ)
    (hψ : ∀ i, ψ i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧ FreshLeft i.1.1 i.1.2.1 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) (o : Basis α × μ)
    (ho : ((Matrix.kronecker leftInsertion (1 : Matrix μ μ ℂ)) *ᵥ ψ) o ≠ 0) :
    Good o.1.2.1 o.1.2.2 ∧ o.1.2.1.card + o.1.2.2.card ≤ m + 1 := by
  obtain ⟨i, hM, hi⟩ := vector_nonzero_path _ ψ o ho
  have hA : leftInsertion o.1 i.1 ≠ 0 := by
    intro hz
    exact hM (by simp [Matrix.kronecker, Matrix.kroneckerMap_apply, hz])
  obtain ⟨hg, hf, hsize⟩ := hψ i hi
  obtain ⟨hg', hsize'⟩ := leftInsertion_preserves hA hg hf
  exact ⟨hg', by omega⟩

/-- Coherently copy the current query to a new auxiliary register. -/
def copyQuery : Matrix (Basis α × (α × μ)) (Basis α × μ) ℂ := fun o i =>
  if o.1 = i.1 ∧ o.2.2 = i.2 ∧ o.2.1 = i.1.1 then 1 else 0

theorem copyQuery_support (ψ : Basis α × μ → ℂ) (m : ℕ)
    (hψ : ∀ i, ψ i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧ FreshLeft i.1.1 i.1.2.1 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) (o : Basis α × (α × μ))
    (ho : (copyQuery *ᵥ ψ) o ≠ 0) :
    Good o.1.2.1 o.1.2.2 ∧ FreshLeft o.1.1 o.1.2.1 ∧
      o.1.2.1.card + o.1.2.2.card ≤ m := by
  obtain ⟨i, hC, hi⟩ := vector_nonzero_path _ ψ o ho
  have hb : o.1 = i.1 := by
    unfold copyQuery at hC
    split_ifs at hC with h
    · exact h.1
    · exact (hC rfl).elim
  rw [hb]
  exact hψ i hi

/-- One modified purified wrapper, retaining the copied query as an auxiliary
    register. No measurement outcome is made available by this definition. -/
def modifiedWrapper (ψ : Basis α × μ → ℂ) : Basis α × (α × μ) → ℂ :=
  Matrix.kronecker leftInsertion (1 : Matrix (α × μ) (α × μ) ℂ) *ᵥ
    (copyQuery *ᵥ (Matrix.kronecker inverseRecording (1 : Matrix μ μ ℂ) *ᵥ ψ))

/-- The concrete inverse/copy/insertion wrapper increases the recording-size
    bound by at most two on arbitrary coherent and entangled amplitudes. -/
theorem modifiedWrapper_support (ψ : Basis α × μ → ℂ) (m : ℕ)
    (hψ : ∀ i, ψ i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) (o : Basis α × (α × μ))
    (ho : modifiedWrapper ψ o ≠ 0) :
    Good o.1.2.1 o.1.2.2 ∧ o.1.2.1.card + o.1.2.2.card ≤ m + 2 := by
  have hI := inverse_with_memory_support ψ m hψ
  have hC := copyQuery_support _ (m + 1) hI
  have hA := leftInsertion_with_memory_support _ (m + 1) hC o ho
  simpa only [Nat.add_assoc] using hA

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

/-- An arbitrary query-and-memory operation that leaves both relation
    registers unchanged. Restricting it further to preserve private auxiliary
    registers only reduces the class covered by this support statement. -/
def knownOperation (K : Matrix (α × ν) (α × μ) ℂ) :
    Matrix (Basis α × ν) (Basis α × μ) ℂ := fun o i =>
  if o.1.2 = i.1.2 then K (o.1.1, o.2) (i.1.1, i.2) else 0

omit [DecidableEq μ] [Fintype ν] [DecidableEq ν] in
theorem knownOperation_support (K : Matrix (α × ν) (α × μ) ℂ)
    (ψ : Basis α × μ → ℂ) (m : ℕ)
    (hψ : ∀ i, ψ i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) (o : Basis α × ν)
    (ho : (knownOperation K *ᵥ ψ) o ≠ 0) :
    Good o.1.2.1 o.1.2.2 ∧ o.1.2.1.card + o.1.2.2.card ≤ m := by
  obtain ⟨i, hK, hi⟩ := vector_nonzero_path _ ψ o ho
  have hr : o.1.2 = i.1.2 := by
    unfold knownOperation at hK
    split_ifs at hK with h
    · exact h
    · exact (hK rfl).elim
  rw [hr]
  exact hψ i hi

/-- The concrete sequence of modified wrappers has at most `2t` recorded
    edges, allowing any changing finite ancillary spaces and intervening
    operators that leave the relation registers unchanged. -/
theorem iterated_modified_wrapper_support
    (M : ℕ → Type*) [∀ t, Fintype (M t)] [∀ t, DecidableEq (M t)]
    (ψ : (t : ℕ) → Basis α × M t → ℂ)
    (K : (t : ℕ) → Matrix (α × M (t + 1)) (α × (α × M t)) ℂ)
    (hinit : ∀ i, ψ 0 i ≠ 0 → i.1.2.1 = ∅ ∧ i.1.2.2 = ∅)
    (hstep : ∀ t, ψ (t + 1) = knownOperation (K t) *ᵥ modifiedWrapper (ψ t))
    (t : ℕ) : ∀ i, ψ t i ≠ 0 →
      Good i.1.2.1 i.1.2.2 ∧ i.1.2.1.card + i.1.2.2.card ≤ 2 * t := by
  induction t with
  | zero =>
      intro i hi
      obtain ⟨hL, hR⟩ := hinit i hi
      rw [hL, hR]
      exact ⟨good_empty, by simp⟩
  | succ t ih =>
      intro o ho
      have hw := modifiedWrapper_support (ψ t) (2 * t) ih
      have hOut : (knownOperation (K t) *ᵥ modifiedWrapper (ψ t)) o ≠ 0 := by
        simpa only [hstep t] using ho
      obtain ⟨hg, hc⟩ := knownOperation_support (K t) (modifiedWrapper (ψ t))
        (2 * t + 2) hw o hOut
      exact ⟨hg, by omega⟩

end
end ICO.RecordingOperatorSupport
