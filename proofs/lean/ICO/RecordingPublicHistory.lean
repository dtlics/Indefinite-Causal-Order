import ICO.RecordingHistory

/-! Public matrix operations do not read accumulated private copy histories.
The exact pure-state reduction below supplies the recurrence correspondence. -/

namespace ICO.RecordingPublicHistory

open QIT ICO.PathRecordingSupport ICO.RecordingOperatorSupport
  ICO.RecordingKnownChannel ICO.RecordingPureCorrespondence ICO.RecordingHistory
  ICO.RecordingActiveWrapper ICO.RecordingRetainedProcess
open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

variable {α μ ν h e : Type*} [Fintype α] [DecidableEq α]
  [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν]
  [Fintype h] [DecidableEq h] [Fintype e]

theorem knownOperation_mulVec_apply (K : Matrix (α × ν) (α × μ) ℂ)
    (v : Basis α × μ → ℂ) (o : Basis α) (i : ν) :
    (knownOperation K *ᵥ v) (o, i) =
      ∑ x : α, ∑ j : μ, K (o.1, i) (x, j) * v ((x, o.2), j) := by
  rcases o with ⟨y, l, r⟩
  simp [knownOperation, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Prod.mk.injEq, ite_and]

theorem liftKnown_rect_rankOne (K : Matrix (α × ν) (α × μ) ℂ)
    (v : Basis α × μ → ℂ) :
    liftKnown (rectSingleOperatorMap K) (rankOneMatrix v) =
      rankOneMatrix (knownOperation K *ᵥ v) := by
  ext u w
  rcases u with ⟨⟨y, l⟩, i⟩
  rcases w with ⟨⟨z, r⟩, j⟩
  rw [liftKnown_apply]
  simp [rectSingleOperatorMap, MatrixMap.ofKraus, Matrix.mul_apply,
    Matrix.conjTranspose_apply, rankOneMatrix_apply, knownOperation_mulVec_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm]

theorem liftKnown_sum (Φ : MatrixMap (α × μ) (α × ν))
    (X : e → CMatrix (Basis α × μ)) :
    liftKnown Φ (∑ k, X k) = ∑ k, liftKnown Φ (X k) := by
  ext u v
  rcases u with ⟨⟨y, l⟩, i⟩
  rcases v with ⟨⟨z, r⟩, j⟩
  simp only [liftKnown_apply, Matrix.sum_apply]
  have hSum : (fun u v : α × μ => ∑ k, X k ((u.1, l), u.2) ((v.1, r), v.2)) =
      ∑ k, (fun u v : α × μ => X k ((u.1, l), u.2) ((v.1, r), v.2)) := by
    ext u v
    simp only [Finset.sum_apply]
  rw [hSum]
  have hMap := congrFun (congrFun (map_sum Φ
    (fun k => (fun u v : α × μ => X k ((u.1, l), u.2) ((v.1, r), v.2)))
    Finset.univ) (y, i)) (z, j)
  simpa only [Matrix.sum_apply] using hMap

def historyKnown (K : Matrix (α × ν) (α × μ) ℂ) :
    Matrix (α × (h × ν)) (α × (h × μ)) ℂ := fun o i =>
  if o.2.1 = i.2.1 then K (o.1, o.2.2) (i.1, i.2.2) else 0

theorem historyKnown_branch (K : Matrix (α × ν) (α × μ) ℂ)
    (v : Basis α × (h × μ) → ℂ) (o : Basis α) (e : h) (i : ν) :
    (knownOperation (historyKnown K) *ᵥ v) (o, (e, i)) =
      (knownOperation K *ᵥ (fun u : Basis α × μ => v (u.1, (e, u.2)))) (o, i) := by
  simp [knownOperation_mulVec_apply, historyKnown, Fintype.sum_prod_type]

theorem eraseHistory_known_rankOne (K : Matrix (α × ν) (α × μ) ℂ)
    (v : Basis α × (h × μ) → ℂ) :
    eraseHistory.map (rankOneMatrix (knownOperation (historyKnown K) *ᵥ v)) =
      liftKnown (rectSingleOperatorMap K) (eraseHistory.map (rankOneMatrix v)) := by
  rw [eraseHistory_rankOne, eraseHistory_rankOne, liftKnown_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [liftKnown_rect_rankOne]
  congr 1
  funext u
  exact historyKnown_branch K v u.1 e u.2

def regroupCopy (v : Basis α × (α × (h × μ)) → ℂ) :
    Basis α × ((α × h) × μ) → ℂ :=
  fun u => v (u.1, (u.2.1.1, (u.2.1.2, u.2.2)))

theorem eraseHistory_regroupCopy (v : Basis α × (α × (h × μ)) → ℂ) :
    eraseHistory.map (rankOneMatrix (regroupCopy v)) =
      eraseHistory.map (eraseCopied (rankOneMatrix v)) := by
  ext u w
  rcases u with ⟨u, i⟩
  rcases w with ⟨w, j⟩
  simp only [eraseHistory_apply, eraseCopied, rankOneMatrix_apply,
    regroupCopy, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- A public operation after the purified modified wrapper reduces to the
    actual retained-record mixed recurrence. All new and old copied query
    labels are traced out, while the public memory is preserved. -/
theorem purified_modified_step_reduction (m : ℕ)
    (K : Matrix (α × ν) (α × μ) ℂ) (v : Basis α × (h × μ) → ℂ)
    (hv : ∀ i, v i ≠ 0 → Good i.1.2.1 i.1.2.2 ∧
      i.1.2.1.card + i.1.2.2.card ≤ m) :
    eraseHistory.map (rankOneMatrix
      (knownOperation (historyKnown K) *ᵥ regroupCopy (modifiedWrapper v))) =
      liftKnown (rectSingleOperatorMap K)
        (retainedGrowingWrapper (m + 1) (eraseHistory.map (rankOneMatrix v))) := by
  rw [eraseHistory_known_rankOne, eraseHistory_regroupCopy,
    ← retainedGrowingWrapper_purified_history m v hv]

end
end ICO.RecordingPublicHistory
