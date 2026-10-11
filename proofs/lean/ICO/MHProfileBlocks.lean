import ICO.MHWProfileLeft
import ICO.MHBlockNorm

/-! Uniform sector bounds on the entire coherent multiset Fock register. -/
namespace ICO.MHProfileBlocks
open QIT ICO.MHWordProfiles ICO.MHWProfileLeft ICO.MHBoundedRecording
  ICO.MHFockSpace ICO.MHFockProjection ICO.RecordingCopyIdentity ICO.RecordingProcess
  ICO.MHBlockNorm
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def profileFockEquiv (T : ℕ) : InputCutoff (α := α) T ≃
    Σ s : Lengths T, ProfileBasis α s.val.1.val s.val.2.val where
  toFun v := ⟨v.1.1,(v.2.1,v.2.2,v.1.2)⟩
  invFun v := ⟨⟨v.1,v.2.2.2⟩,(v.2.1,v.2.2.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem matrix_profile_blocks (T : ℕ) (M : CMatrix (InputCutoff (α := α) T))
    (hM : ∀ o i, M o i≠0 → o.1.1=i.1.1) :
    M=(Matrix.blockDiagonal' (fun s : Lengths T =>
      M.submatrix (profileEmbed (A := α) s.property) (profileEmbed s.property))).submatrix
        (profileFockEquiv T) (profileFockEquiv T) := by
  ext ⟨⟨s,q⟩,x,p⟩ ⟨⟨s',q'⟩,y,p'⟩
  by_cases he : s=s'
  · subst s'
    simp only [Matrix.submatrix_apply,profileFockEquiv,Equiv.coe_fn_mk,Matrix.blockDiagonal'_apply_eq]
    rfl
  · have hz : M ⟨⟨s,q⟩,(x,p)⟩ ⟨⟨s',q'⟩,(y,p')⟩=0 := by
      by_contra hn
      exact he (hM _ _ hn)
    simp [hz,profileFockEquiv,Matrix.submatrix_apply,Matrix.blockDiagonal'_apply,he]

theorem reindex_norm_le {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (M : CMatrix a) (e : b≃a) : ‖M.submatrix e e‖≤‖M‖ := by
  rw [← basisEmbedding_compression]
  have hK := isometry_matrix_norm_le (basisEmbedding e) (basisEmbedding_gram e e.injective)
  have hKa : ‖(basisEmbedding e).conjTranspose‖≤1 := by
    simpa only [Matrix.l2_opNorm_conjTranspose] using hK
  calc
    _ ≤ (‖(basisEmbedding e).conjTranspose‖*‖M‖)*‖basisEmbedding e‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖M‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hKa (norm_nonneg M)) hK (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem matrix_norm_le_of_profile_blocks (T : ℕ) (M : CMatrix (InputCutoff (α := α) T))
    (hM : ∀ o i, M o i≠0 → o.1.1=i.1.1) (β : ℝ) (hβ : 0≤β)
    (hb : ∀ s : Lengths T,
      ‖M.submatrix (profileEmbed (A := α) s.property) (profileEmbed s.property)‖≤β) : ‖M‖≤β := by
  rw [matrix_profile_blocks T M hM]
  apply (reindex_norm_le _ (profileFockEquiv T)).trans
  have hs : Real.sqrt (β^2)=β := by rw [Real.sqrt_sq_eq_abs,abs_of_nonneg hβ]
  rw [← hs]
  apply blockDiagonal'_norm_le _ _ (sq_nonneg β)
  intro s
  rw [hs]
  exact hb s

end
end ICO.MHProfileBlocks
