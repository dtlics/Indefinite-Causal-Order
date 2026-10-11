import ICO.C6FockCompression
import ICO.C6ForwardAlgebra

namespace ICO.C6RightCompression
open Matrix QIT ICO.C6FockCompression ICO.MHBoundedRecording ICO.MHFockSpace
open ICO.MHFockKnownOperation ICO.MHFockProjection ICO.RecordingCopyIdentity
open ICO.RecordingProcess ICO.MHFockSwap ICO.MHFockOracle ICO.MHProfileTranspose
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option synthInstance.maxSize 512
variable {A : Type*} [Fintype A] [DecidableEq A]

def flipRecords {T : ℕ} (R : Records (α:=A) T) : Records (α:=A) T :=
  ⟨lengthSwap R.1,(profileTranspose _ R.2.2,profileTranspose _ R.2.1)⟩

theorem flipRecords_involutive {T : ℕ} (R : Records (α:=A) T) :
    flipRecords (flipRecords R)=R := by
  rcases R with ⟨s,p,q⟩
  change (⟨s,(profileTranspose _ (profileTranspose _ p),
    profileTranspose _ (profileTranspose _ q))⟩:Records (α:=A) T)=⟨s,(p,q)⟩
  rw [profileTranspose_involutive,profileTranspose_involutive]

def flipEquiv (T : ℕ) : Records (α:=A) T ≃ Records (α:=A) T :=
  ⟨flipRecords,flipRecords,flipRecords_involutive,flipRecords_involutive⟩

theorem flipRecords_records {T : ℕ} (i : InputCutoff (α:=A) T) :
    flipRecords (records i)=records (recordSwap i) := rfl

theorem swap_query (T : ℕ) (ψ : A→ℂ) :
    swapMatrix T*fockQuery T ψ=fockQuery T ψ*basisEmbedding (flipEquiv T) := by
  ext i R
  have hl : (swapMatrix (α:=A) T*fockQuery T ψ) i R=fockQuery T ψ (recordSwap i) R := by
    rw [←swapMatrix_selfAdjoint T]
    exact congrFun (basisEmbedding_adjoint_mulVec (recordSwapEquiv T)
      (fun j => fockQuery T ψ j R)) i
  rw [hl]
  have hr : (fockQuery T ψ*basisEmbedding (flipEquiv (A:=A) T)) i R=
      fockQuery T ψ i (flipRecords R) := by
    simp [Matrix.mul_apply,basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,flipEquiv]
  rw [hr]
  change (if flipRecords (records i)=R then ψ i.2.1 else 0)=
    (if records i=flipRecords R then ψ i.2.1 else 0)
  have he : flipRecords (records i)=R ↔ records i=flipRecords R := by
    constructor
    · intro h
      rw [←h,flipRecords_involutive]
    · intro h
      rw [h,flipRecords_involutive]
  simp only [he]

theorem right_fock_compression {t T : ℕ} (h : t+1≤T) (ψ : A→ℂ)
    (hψ : ∑ y,‖ψ y‖^2≤1) (ht : t<Fintype.card A) :
    ‖(rightOnFock (α:=A) h).conjTranspose*fockQuery T ψ‖≤
      Real.sqrt ((t+1:ℝ)/((Fintype.card A:ℝ)-t)) := by
  have hs := swapMatrix_norm_le (α:=A) T
  have hr := isometry_matrix_norm_le (basisEmbedding (flipEquiv (A:=A) T))
    (basisEmbedding_gram _ (flipEquiv T).injective)
  have he : (rightOnFock (α:=A) h).conjTranspose*fockQuery T ψ=
      swapMatrix T*((leftOnFock h).conjTranspose*fockQuery T ψ)*basisEmbedding (flipEquiv T) := by
    rw [rightOnFock,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose,swapMatrix_selfAdjoint]
    simp only [Matrix.mul_assoc]
    rw [swap_query]
  rw [he]
  calc
    _ ≤ (‖swapMatrix (α:=A) T‖*‖(leftOnFock h).conjTranspose*fockQuery T ψ‖)*
        ‖basisEmbedding (flipEquiv T)‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*Real.sqrt ((t+1:ℝ)/((Fintype.card A:ℝ)-t)))*1 :=
      mul_le_mul (mul_le_mul hs (left_fock_compression h ψ hψ ht) (norm_nonneg _) (by norm_num))
        hr (norm_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms right_fock_compression
end
end ICO.C6RightCompression
