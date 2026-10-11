import ICO.MHWordProfileGram
import ICO.MHWordSlots
import ICO.MHCreatorEmbedding

/-! Exact spectator and associativity transport for a Bell projector on a
right-record slot of the full two-word register. -/
namespace ICO.MHWordBellSpectator
open QIT ICO.MHWordProfiles ICO.MHWordDistinct ICO.MHWordSlots ICO.MHBellEntries
  ICO.MHSymmetric ICO.MHCreatorEmbedding
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2200000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def rightWordEquiv (l r : ℕ) : WordBasis α (Fin l⊕Fin r) ≃
    (α×TensorPower (α×α) r)×TensorPower (α×α) l where
  toFun w := ((w.1,rightWord w.2),leftWord w.2)
  invFun w := (w.1.1,Sum.elim (tensorPowerEquiv l w.2) (tensorPowerEquiv r w.1.2))
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    cases j <;> simp [leftWord,rightWord]
  right_inv w := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      simp [rightWord]
    · simp [leftWord]

def rightProfileEquiv (l r : ℕ) :
    ((α×TensorPowerProfile (α×α) r)×TensorPowerProfile (α×α) l) ≃ ProfileBasis α l r where
  toFun p := (p.1.1,p.2,p.1.2)
  invFun p := ((p.1,p.2.2),p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def rightWordEmbedding (l r : ℕ) :
    Matrix ((α×TensorPower (α×α) r)×TensorPower (α×α) l)
      ((α×TensorPowerProfile (α×α) r)×TensorPowerProfile (α×α) l) ℂ :=
  Matrix.kronecker (queryOccupationEmbedding r) (occupationEmbedding l)

theorem wordEmbedding_right (l r : ℕ) :
    (wordEmbedding (A := α) l r).submatrix id (rightProfileEquiv l r)=
      (rightWordEmbedding (α := α) l r).submatrix (rightWordEquiv l r) id := by
  ext w p
  simp only [Matrix.submatrix_apply,id_eq,wordEmbedding,rightProfileEquiv,rightWordEmbedding,
    rightWordEquiv,Equiv.coe_fn_mk,queryOccupationEmbedding,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  ring

theorem leftWord_eq_iff {l r : ℕ} (w v : Fin l⊕Fin r→α×α) :
    leftWord w=leftWord v ↔ ∀ j : Fin l, w (.inl j)=v (.inl j) := by
  simp only [leftWord,Equiv.symm_apply_eq,Equiv.apply_symm_apply]
  exact funext_iff

theorem spectator_right_iff {l r : ℕ} (j : Fin r) (w v : Fin l⊕Fin r→α×α) :
    (∀ k : Fin l⊕Fin r, k≠Sum.inr j → w k=v k) ↔
      (∀ k : Fin r, k≠j → w (.inr k)=v (.inr k)) ∧ leftWord w=leftWord v := by
  rw [leftWord_eq_iff]
  constructor
  · intro h
    exact ⟨fun k hk => h (.inr k) (by simpa using hk),
      fun k => h (.inl k) (by simp)⟩
  · rintro ⟨hR,hL⟩ k hk
    cases k with
    | inl k => exact hL k
    | inr k => exact hR k (by simpa using hk)

theorem right_slot_spectator {l r : ℕ} (j : Fin r) :
    slotBell (A := α) (J := Fin l⊕Fin r) (Sum.inr j)=
      (Matrix.kronecker (slotMatrix (A := α) r j)
        (1 : CMatrix (TensorPower (α×α) l))).submatrix (rightWordEquiv l r) (rightWordEquiv l r) := by
  ext o i
  simp only [Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
    slotMatrix,slotBell_apply,spectator_eq_iff,wordEquiv,rightWordEquiv,Equiv.coe_fn_mk,Equiv.prodCongr_apply,
    Equiv.refl_apply,rightWord,Equiv.apply_symm_apply,spectator_right_iff]
  by_cases hL : leftWord o.2=leftWord i.2
  · simp [hL]
  · simp [hL]

end
end ICO.MHWordBellSpectator
