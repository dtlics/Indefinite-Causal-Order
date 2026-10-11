import ICO.AllChannelDilation
import Mathlib.Data.Matrix.Block

namespace ICO.ControlledIsometry
open Matrix QIT
open scoped BigOperators
noncomputable section
universe u
variable {J Q : Type u} [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]
variable {B E : J → Type u} [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
  [∀ j, Fintype (E j)] [∀ j, DecidableEq (E j)]
set_option maxHeartbeats 1200000

def distrib (Q : Type u) (E : J → Type u) : (Q×(j:J)×E j) ≃ ((j:J)×(Q×E j)) where
  toFun x := ⟨x.2.1,(x.1,x.2.2)⟩
  invFun x := (x.2.1,⟨x.1,x.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

def controlled (W : (j:J) → Matrix (Q×E j) (B j) ℂ) : Matrix (Q×(j:J)×E j) ((j:J)×B j) ℂ :=
  (Matrix.blockDiagonal' W).submatrix (distrib Q E) (Equiv.refl _)

theorem controlled_isometry (W : (j:J) → Matrix (Q×E j) (B j) ℂ)
    (hW : ∀j,(W j).conjTranspose*W j=1) :
    (controlled W).conjTranspose*controlled W=1 := by
  rw [controlled,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv]
  rw [Matrix.blockDiagonal'_conjTranspose,←Matrix.blockDiagonal'_mul]
  simp_rw [hW]
  change (Matrix.blockDiagonal' (1 : (j : J) → CMatrix (B j))).submatrix (Equiv.refl _) (Equiv.refl _) = 1
  rw [Matrix.blockDiagonal'_one,Matrix.submatrix_one_equiv]

theorem controlled_entry_same (W : (j:J) → Matrix (Q×E j) (B j) ℂ)
    (j:J) (q:Q) (e:E j) (b:B j) : controlled W (q,⟨j,e⟩) ⟨j,b⟩=W j (q,e) b := by
  simp [controlled,distrib]

theorem controlled_entry_ne (W : (j:J) → Matrix (Q×E j) (B j) ℂ)
    (j k:J) (h:j≠k) (q:Q) (e:E j) (b:B k) : controlled W (q,⟨j,e⟩) ⟨k,b⟩=0 := by
  exact Matrix.blockDiagonal'_apply_ne W (q,e) b h

theorem controlled_row_mul (W : (j:J) → Matrix (Q×E j) (B j) ℂ)
    (X : CMatrix ((j:J)×B j)) (j:J) (q:Q) (e:E j) (b:(j:J)×B j) :
    (controlled W*X) (q,⟨j,e⟩) b = ∑ a:B j,W j (q,e) a*X ⟨j,a⟩ b := by
  rw [Matrix.mul_apply,Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp_rw [controlled_entry_same]
  · intro k hk hkj
    apply Finset.sum_eq_zero
    intro a ha
    rw [controlled_entry_ne W j k (Ne.symm hkj),zero_mul]
  · intro hj
    exact (hj (Finset.mem_univ _)).elim

theorem controlled_sandwich_block (W : (j:J) → Matrix (Q×E j) (B j) ℂ)
    (X : CMatrix ((j:J)×B j)) (j:J) (q r:Q) (e f:E j) :
    (controlled W*X*(controlled W).conjTranspose) (q,⟨j,e⟩) (r,⟨j,f⟩)=
      (W j * X.submatrix (Sigma.mk j) (Sigma.mk j) * (W j).conjTranspose) (q,e) (r,f) := by
  rw [Matrix.mul_apply,Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.conjTranspose_apply,controlled_entry_same,controlled_row_mul]
    rfl
  · intro k hk hkj
    apply Finset.sum_eq_zero
    intro a ha
    rw [Matrix.conjTranspose_apply,controlled_entry_ne W j k (Ne.symm hkj),star_zero,mul_zero]
  · intro hj
    exact (hj (Finset.mem_univ _)).elim

theorem controlled_erasure (W : (j:J) → Matrix (Q×E j) (B j) ℂ)
    (X : CMatrix ((j:J)×B j)) :
    partialTraceB (controlled W*X*(controlled W).conjTranspose)=
      ∑ j,partialTraceB (W j * X.submatrix (Sigma.mk j) (Sigma.mk j)*(W j).conjTranspose) := by
  ext q r
  simp only [partialTraceB,Fintype.sum_sigma,Matrix.sum_apply,controlled_sandwich_block]

#print axioms controlled_erasure
#print axioms controlled_isometry
end
end ICO.ControlledIsometry

