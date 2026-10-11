import ICO.MHBijectionProfiles
import ICO.MHCreatorEmbedding
import ICO.MHCreationCoefficients

/-! The right partial recording branch in exact occupation coordinates.
Its image is a bijection projection sandwich of symmetric creation. -/

namespace ICO.MHWOccupation

open QIT ICO.MHBijectionProfiles ICO.MHOccupationCounts ICO.MHOccupationSupport
  ICO.MHFockLabels ICO.MHOccupationCovariance ICO.MHCreationCoefficients
  ICO.MHCreatorEmbedding ICO.MHCreationCovariance ICO.RecordingMultisetBridge
open scoped BigOperators Matrix

noncomputable section
set_option maxHeartbeats 2500000
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {α : Type*} [Fintype α] [DecidableEq α]

def bijRightProjection {n : ℕ} (p : TensorPowerProfile (α × α) n) (r : ℕ) :
    CMatrix (α × TensorPowerProfile (α × α) r) :=
  Matrix.diagonal (fun i => if BijProfile p i.2 then 1 else 0)

def rightWOccupation {n r : ℕ} (p : TensorPowerProfile (α × α) n) :
    Matrix (α × TensorPowerProfile (α × α) (r+1)) (α × TensorPowerProfile (α × α) r) ℂ :=
  fun o i => if o.2=incrementProfile (o.1,i.1) i.2 ∧ BijProfile p o.2 then
    (((Real.sqrt ((Fintype.card α : ℝ)-n-r))⁻¹ : ℝ) : ℂ) else 0

theorem bij_increment_count_zero {n r : ℕ} (p : TensorPowerProfile (α × α) n)
    (q : TensorPowerProfile (α × α) r) (x y : α)
    (h : BijProfile p (incrementProfile (x,y) q)) : q.val (x,y)=0 := by
  have hb := (bijProfile_increment_right p q x y).mp h
  have hy : y ∉ usedOutputs p q := by rw [usedOutputs_multisets]; exact hb.2.2
  have hm := (mem_usedOutputs p q y).not.mp hy
  have he := entry_le_outputMultiplicity q x y
  omega

theorem rightWOccupation_factor {n r : ℕ} (p : TensorPowerProfile (α × α) n) :
    rightWOccupation (r := r) p =
      ((((Real.sqrt ((Fintype.card α : ℝ)-n-r))⁻¹ : ℝ) : ℂ) •
        (bijRightProjection p (r+1) * occupationRightCreator (α := α) r)) := by
  ext o i
  simp only [rightWOccupation,Matrix.smul_apply,smul_eq_mul,bijRightProjection,
    Matrix.diagonal_mul,occupationRightCreator,creationOccupation_basis_entry]
  by_cases he : o.2=incrementProfile (o.1,i.1) i.2
  · by_cases hb : BijProfile p o.2
    · have hz := bij_increment_count_zero p i.2 o.1 i.1 (he ▸ hb)
      simp [he,hb,hz]
    · have hb' : ¬BijProfile p (incrementProfile (o.1,i.1) i.2) := he ▸ hb
      simp [he,hb']
  · simp [he]

theorem bijRightProjection_adjoint {n : ℕ} (p : TensorPowerProfile (α × α) n) (r : ℕ) :
    (bijRightProjection p r).conjTranspose=bijRightProjection p r := by
  ext i j
  by_cases he : i=j
  · subst j; simp [bijRightProjection]
  · simp [bijRightProjection,Matrix.conjTranspose_apply,he,Ne.symm he]

theorem inverse_sqrt_square (x : ℝ) (hx : 0≤x) :
    (((Real.sqrt x)⁻¹ : ℝ) : ℂ)*star (((Real.sqrt x)⁻¹ : ℝ) : ℂ) = ((x⁻¹ : ℝ) : ℂ) := by
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
  congr 1
  rw [← pow_two,inv_pow,Real.sq_sqrt hx]

theorem rightWOccupation_image {n r : ℕ} (p : TensorPowerProfile (α × α) n)
    (hsize : n+r≤Fintype.card α) :
    rightWOccupation (r := r) p * (rightWOccupation (r := r) p).conjTranspose =
      (((((Fintype.card α : ℝ)-n-r)⁻¹ : ℝ) : ℂ) •
        (bijRightProjection p (r+1) *
          (occupationRightCreator (α := α) r * (occupationRightCreator (α := α) r).conjTranspose) *
          bijRightProjection p (r+1))) := by
  have hgap : 0≤(Fintype.card α : ℝ)-n-r := by
    have hs : (n:ℝ)+r≤Fintype.card α := by exact_mod_cast hsize
    linarith
  rw [rightWOccupation_factor]
  simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,bijRightProjection_adjoint,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,inverse_sqrt_square _ hgap,Matrix.mul_assoc]
  congr 1
  exact (mul_comm _ _).trans (inverse_sqrt_square _ hgap)

theorem rightWOccupation_word_image {n r : ℕ} (p : TensorPowerProfile (α × α) n)
    (hsize : n+r≤Fintype.card α) :
    rightWOccupation (r := r) p * (rightWOccupation (r := r) p).conjTranspose =
      (((((Fintype.card α : ℝ)-n-r)⁻¹ : ℝ) : ℂ) •
        (bijRightProjection p (r+1) *
          ((queryOccupationEmbedding (α := α) (r+1)).conjTranspose *
            (ICO.MHRightCovariance.rightCreator r * (ICO.MHRightCovariance.rightCreator (α := α) r).conjTranspose) *
              queryOccupationEmbedding (α := α) (r+1)) * bijRightProjection p (r+1))) := by
  rw [rightWOccupation_image p hsize,occupationRightCreator_image]

end
end ICO.MHWOccupation
