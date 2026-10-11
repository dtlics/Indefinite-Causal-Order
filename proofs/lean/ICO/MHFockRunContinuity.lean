import ICO.MHRotatedTrajectory
import ICO.MHFockEmptyRotation
import ICO.MHCoherentDomainTwirl

/-! Continuity of the literal rotated recording experiment, sufficient for
all compact Haar integrability statements in the hybrid proof. -/
namespace ICO.MHFockRunContinuity
open QIT ICO.MHFockTrajectory ICO.MHFockKnownOperation ICO.MHFockPublicRotation
  ICO.MHFockRotation ICO.MHFockProjection ICO.MHFockLabels ICO.MHBijectionProfiles
  ICO.MHBoundedRecording ICO.MHRotatedTrajectory ICO.MHFockRunIsometry
  ICO.MHProfileTurnFock ICO.MHCoherentDomainTwirl ICO.MHProtocolOverlap
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 512
variable {α : Type} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem query_continuous (T : ℕ) :
    Continuous (fun C : Matrix.unitaryGroup α ℂ =>
      (fockQuery C T : CMatrix (InputCutoff (α := α) T))) := by
  apply continuous_pi
  intro o
  apply continuous_pi
  intro i
  simp_rw [←query_known_entry]
  simp only [known_coefficient,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  exact ((continuous_subtype_val.matrix_elem o.2.1 i.2.1).mul continuous_const).mul continuous_const

theorem actualTurn_continuous (T : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ => actualTurn p.1 p.2 T) := by
  simp_rw [actual_turn_profileBlocks]
  exact (blocksCLM (A := α) T).continuous.comp
    (continuous_pi (fun s => profileTurn_continuous s.val.1.val s.val.2.val))

theorem record_continuous (T : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ =>
      (fockQ p.1 p.2 T : CMatrix (InputCutoff (α := α) T))) := by
  have he (C D : Matrix.unitaryGroup α ℂ) :
      (fockQ C D T : CMatrix (InputCutoff (α := α) T))=
        (fockQuery C T : CMatrix (InputCutoff (α := α) T)).conjTranspose*actualTurn C D T := by
    rw [actualTurn,←Matrix.mul_assoc]
    have hu := Matrix.mem_unitaryGroup_iff'.mp (fockQuery C T).property
    change (fockQuery C T : CMatrix (InputCutoff (α := α) T)).conjTranspose*
      (fockQuery C T : CMatrix (InputCutoff (α := α) T))=1 at hu
    rw [hu,Matrix.one_mul]
  simp_rw [he]
  exact ((query_continuous T).comp continuous_fst).matrix_conjTranspose.matrix_mul (actualTurn_continuous T)

theorem before_continuous (inverse : Bool) :
    Continuous (fun p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ => before p.1 p.2 inverse) := by
  cases inverse
  · exact continuous_fst
  · exact continuous_snd.inv

theorem after_continuous (inverse : Bool) :
    Continuous (fun p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ => after p.1 p.2 inverse) := by
  cases inverse
  · exact continuous_snd
  · exact continuous_fst.inv

theorem rotatedW_continuous {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (inverse : Bool) :
    Continuous (fun p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ => rotatedW hT p.1 p.2 inverse) :=
  (((query_continuous T).comp (after_continuous inverse)).matrix_mul continuous_const).matrix_mul
    ((query_continuous T).comp (before_continuous inverse))

theorem tensor_identity_continuous {Ω a b μ : Type*} [TopologicalSpace Ω]
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype μ] [DecidableEq μ]
    (F : Ω→Matrix b a ℂ) (hF : Continuous F) :
    Continuous (fun ω => Matrix.kronecker (F ω) (1 : CMatrix μ)) := by
  apply continuous_pi
  intro o
  apply continuous_pi
  intro i
  exact (hF.matrix_elem o.1 i.1).mul continuous_const

theorem act_continuous {Ω H : Type*} [TopologicalSpace Ω] [Fintype H] [DecidableEq H]
    (F : Ω→CMatrix H) (hF : Continuous F) : Continuous (fun ω => act (F ω)) := by
  exact (Matrix.toEuclideanCLM (n := H) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp hF

theorem rotatedAction_continuous {T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (inverse : Bool)
    (μ : Type*) [Fintype μ] [DecidableEq μ] :
    Continuous (fun p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ =>
      act (Matrix.kronecker (rotatedW hT p.1 p.2 inverse) (1 : CMatrix μ))) :=
  act_continuous _ (tensor_identity_continuous _ (rotatedW_continuous hT inverse))

theorem recordAction_continuous (T : ℕ) (μ : Type*) [Fintype μ] [DecidableEq μ] :
    Continuous (fun p : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup α ℂ =>
      act (Matrix.kronecker (fockQ p.1 p.2 T : CMatrix (InputCutoff (α := α) T)) (1 : CMatrix μ))) :=
  act_continuous _ (tensor_identity_continuous _ (record_continuous T))

#print axioms rotatedAction_continuous
#print axioms recordAction_continuous
end
end ICO.MHFockRunContinuity
