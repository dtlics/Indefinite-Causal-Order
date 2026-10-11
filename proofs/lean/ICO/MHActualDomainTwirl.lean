import ICO.MHProfileTwirl
import ICO.MHWDomainModel

/-! The actual embedded W-domain projector satisfies the full Haar loss
bound on every fixed record-length sector. -/
namespace ICO.MHActualDomainTwirl
open Matrix QIT MeasureTheory ICO.MHWordProfiles ICO.MHWordRotation ICO.MHProfileTwirl
  ICO.MHWDomainModel ICO.MHWProfileLeft ICO.MHWDomainProjection ICO.MHWEmbedding
  ICO.RecordingCopyIdentity
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

local instance cmContinuousENorm {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousENorm (CMatrix ι) := SeminormedAddGroup.toContinuousENorm
local instance matrixNonUnitalCStar (n : Type) [Fintype n] [DecidableEq n] :
    NonUnitalCStarAlgebra (CMatrix n) := ⟨⟩
local instance matrixCStar (n : Type) [Fintype n] [DecidableEq n] :
    CStarAlgebra (CMatrix n) := ⟨⟩

theorem domainScale_bounds (l r : ℕ) (hsmall : 2*(l+r)≤Fintype.card A) :
    1≤domainScale (α := A) l r ∧ domainScale (α := A) l r≤2 := by
  cases r with
  | zero => simp [domainScale]
  | succ r =>
    simp only [domainScale,Nat.add_eq_zero_iff,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel]
    have hc : (2 : ℝ)*((l : ℝ)+(r : ℝ)+1)≤Fintype.card A := by exact_mod_cast hsmall
    have hp : 0<(Fintype.card A : ℝ)-l-r := by nlinarith [Nat.cast_nonneg (α := ℝ) l,Nat.cast_nonneg (α := ℝ) r]
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith [Nat.cast_nonneg (α := ℝ) l,Nat.cast_nonneg (α := ℝ) r]
    · apply (div_le_iff₀ hp).2
      nlinarith

def sectorMissing {l r T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (h : l+r≤T) :
    CMatrix (ProfileBasis A l r) :=
  (basisEmbedding (profileEmbed (A := A) h)).conjTranspose*
    (bijProjection T-(recordW hT).conjTranspose*recordW hT)*basisEmbedding (profileEmbed h)

theorem sectorMissing_nonneg {l r T : ℕ} (hT : 2*Fintype.card (A×A)≤T) (h : l+r≤T) :
    0≤sectorMissing hT h := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  exact (Matrix.le_iff.mp (recordGram_le_bij hT)).conjTranspose_mul_mul_same (basisEmbedding (profileEmbed h))

theorem profileTwirl_nonneg {l r : ℕ} (X : CMatrix (ProfileBasis A l r)) (hX : 0≤X) :
    0≤profileTwirl l r X := by
  apply integral_nonneg
  intro D
  apply integral_nonneg
  intro C
  exact ((Matrix.nonneg_iff_posSemidef.mp hX).conjTranspose_mul_mul_same
    (profileTurn C D l r : CMatrix (ProfileBasis A l r))).nonneg

theorem actual_sector_mean_le {l r T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (h : l+r≤T) (hsize : l+r<Fintype.card A) (hsmall : 2*(l+r)≤Fintype.card A) :
    profileTwirl l r (sectorMissing hT h) ≤
      (6*((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/Fintype.card A)) •
        (1 : CMatrix (ProfileBasis A l r)) := by
  rw [sectorMissing,missing_domain_compression hT h hsize]
  exact profile_domain_twirl_le l r _ (domainScale_bounds l r hsmall).1 (domainScale_bounds l r hsmall).2

theorem actual_sector_mean_norm_le {l r T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (h : l+r≤T) (hsize : l+r<Fintype.card A) (hsmall : 2*(l+r)≤Fintype.card A) :
    ‖profileTwirl l r (sectorMissing hT h)‖ ≤
      6*((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/Fintype.card A) := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (by positivity)
    (profileTwirl_nonneg _ (sectorMissing_nonneg hT h))).2
  simpa only [Algebra.algebraMap_eq_smul_one] using actual_sector_mean_le hT h hsize hsmall

#print axioms actual_sector_mean_norm_le
end
end ICO.MHActualDomainTwirl
