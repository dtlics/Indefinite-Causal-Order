import ICO.MHWordSectorTwirl

/-! Transport the actual Haar word-domain estimate through the normalized
symmetric embedding, without postulating a relation between the two models. -/
namespace ICO.MHProfileTwirl
open Matrix QIT MeasureTheory ICO.MHWordProfiles ICO.MHWordRotation
  ICO.MHWordDomainTwirl ICO.MHWordSectorTwirl ICO.MHWordDistinct ICO.MHWordDomain
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm

def compressionCLM {H K : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (E : Matrix H K ℂ) : CMatrix H →L[ℝ] CMatrix K :=
  ({ toFun := fun X => E.conjTranspose*X*E
     map_add' := by intros; simp [Matrix.mul_add,Matrix.add_mul]
     map_smul' := by intros; simp [Matrix.mul_smul,Matrix.smul_mul] } :
    CMatrix H →ₗ[ℝ] CMatrix K).toContinuousLinearMap

def profileTwirl (l r : ℕ) (X : CMatrix (ProfileBasis A l r)) : CMatrix (ProfileBasis A l r) :=
  ∫ D, ∫ C, (profileTurn C D l r : CMatrix (ProfileBasis A l r)).conjTranspose*X*
    (profileTurn C D l r : CMatrix (ProfileBasis A l r))
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)

theorem conjugation_embedding (C D : Matrix.unitaryGroup A ℂ) (l r : ℕ)
    (X : CMatrix (WordBasis A (Fin l⊕Fin r))) :
    (profileTurn C D l r : CMatrix (ProfileBasis A l r)).conjTranspose*
      ((wordEmbedding l r).conjTranspose*X*wordEmbedding l r)*
      (profileTurn C D l r : CMatrix (ProfileBasis A l r)) =
    (wordEmbedding l r).conjTranspose*
      ((turn (rightSlots l r) C D : CMatrix (WordBasis A (Fin l⊕Fin r))).conjTranspose*X*
        (turn (rightSlots l r) C D : CMatrix (WordBasis A (Fin l⊕Fin r))))*wordEmbedding l r := by
  have hh := turn_embedding C D l r
  have ha := congrArg Matrix.conjTranspose hh
  simp only [Matrix.conjTranspose_mul] at ha
  simp only [← Matrix.mul_assoc]
  rw [← ha]
  simp only [Matrix.mul_assoc]
  rw [← hh]

theorem profile_twirl_compression (l r : ℕ) (X : CMatrix (WordBasis A (Fin l⊕Fin r))) :
    profileTwirl l r ((wordEmbedding l r).conjTranspose*X*wordEmbedding l r) =
      (wordEmbedding l r).conjTranspose*
        (∫ D, twirl (rightSlots l r) D X ∂unitaryHaarMeasure (a := A))*wordEmbedding l r := by
  simp only [profileTwirl]
  simp_rw [conjugation_embedding]
  have he (D : Matrix.unitaryGroup A ℂ) :
      (∫ C, (wordEmbedding l r).conjTranspose*
        ((turn (rightSlots l r) C D : CMatrix (WordBasis A (Fin l⊕Fin r))).conjTranspose*X*
          (turn (rightSlots l r) C D : CMatrix (WordBasis A (Fin l⊕Fin r))))*wordEmbedding l r
          ∂unitaryHaarMeasure (a := A)) =
      (wordEmbedding l r).conjTranspose*twirl (rightSlots l r) D X*wordEmbedding l r :=
    (compressionCLM (wordEmbedding l r)).integral_comp_comm (conjugation_integrable _ D X)
  simp_rw [he]
  exact (compressionCLM (wordEmbedding l r)).integral_comp_comm
    ((twirl_continuous _ X).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := unitaryHaarMeasure (a := A)))

theorem rectangular_compression_mono {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (E : Matrix H K ℂ) {X Y : CMatrix H} (h : X≤Y) :
    E.conjTranspose*X*E≤E.conjTranspose*Y*E := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub,Matrix.sub_mul] using (Matrix.le_iff.mp h).conjTranspose_mul_mul_same E

theorem profile_domain_twirl_le (l r : ℕ) (κ : ℝ) (hκ1 : 1≤κ) (hκ2 : κ≤2) :
    profileTwirl l r ((wordEmbedding l r).conjTranspose*
      (distinctProjection (A := A) (J := Fin l⊕Fin r)-domainModel (rightSlots l r) κ)*wordEmbedding l r) ≤
      (6*((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/Fintype.card A)) •
        (1 : CMatrix (ProfileBasis A l r)) := by
  rw [profile_twirl_compression]
  have hh := rectangular_compression_mono (wordEmbedding (A := A) l r)
    (fixed_sector_six_twirl_le l r κ hκ1 hκ2)
  simpa only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,wordEmbedding_gram] using hh

#print axioms profile_twirl_compression
#print axioms profile_domain_twirl_le
end
end ICO.MHProfileTwirl

