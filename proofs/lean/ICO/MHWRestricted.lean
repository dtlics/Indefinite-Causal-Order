import ICO.MHWLengths
import ICO.MHCutoffOverlap
import ICO.MHFockFullCovariance

/-! Reachable-cutoff versions of the physical W/V overlap and covariance. -/
namespace ICO.MHWRestricted
open QIT ICO.MHWEmbedding ICO.MHWDomainProjection ICO.MHWLengths ICO.MHCutoffOverlap
  ICO.MHFockAlgebra ICO.MHFockProjection ICO.MHFockTransport ICO.MHFockRotation
  ICO.MHFockFullCovariance ICO.MHBoundedRecording ICO.MHSectorCovariance
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {α : Type*} [Fintype α] [DecidableEq α]

def restrictedW {t T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (ht : t≤T) :
    CMatrix (InputCutoff (α := α) T) := recordW hT*sourceProjection ht

def restrictedV {t T : ℕ} (h : t+1≤T) : CMatrix (InputCutoff (α := α) T) :=
  ICO.MHFockOracle.fullOracle h*sourceProjection (Nat.le_trans (Nat.le_succ t) h)

theorem restrictedW_initial_projection {t T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (ht : t≤T) :
    IsStarProjection ((restrictedW hT ht).conjTranspose*restrictedW hT ht) :=
  restricted_domain_projection _ _ (recordW_initial_projection hT)
    (sourceProjection_projection ht) (recordGram_cutoff_commute ht hT)

theorem restrictedW_gram {t T : ℕ} (hT : 2*Fintype.card (α×α)≤T) (ht : t≤T) :
    (restrictedW hT ht).conjTranspose*restrictedW hT ht=
      ((recordW hT).conjTranspose*recordW hT)*sourceProjection ht :=
  restricted_gram _ _ (sourceProjection_projection ht) (recordGram_cutoff_commute ht hT)

theorem restrictedW_overlap {t T : ℕ} (hT : 2*Fintype.card (α×α)≤T)
    (h : t+1≤T) (ht : t<Fintype.card α) :
    (restrictedW hT (Nat.le_trans (Nat.le_succ t) h)).conjTranspose*restrictedV h=
      (restrictedW hT (Nat.le_trans (Nat.le_succ t) h)).conjTranspose*
        restrictedW hT (Nat.le_trans (Nat.le_succ t) h) :=
  restricted_overlap _ _ _ (recordW_overlap_low h hT ht)

theorem source_commute_query (C : Matrix.unitaryGroup α ℂ) {t T : ℕ} (ht : t≤T) :
    Commute (sourceProjection (α := α) ht) (fockQuery C T : CMatrix (InputCutoff (α := α) T)) := by
  change Commute (sourceProjection ht) (inputFamily (fun n r => (queryTurn C n r : CMatrix (Sector (α := α) n r))) T)
  rw [sourceProjection_diagonal]
  exact cutoff_commute_of_grade grade t _ (inputFamily_grade _ T)

theorem source_commute_rotation (C D : Matrix.unitaryGroup α ℂ) {t T : ℕ} (ht : t≤T) :
    Commute (sourceProjection (α := α) ht) (fockQ C D T : CMatrix (InputCutoff (α := α) T)) := by
  change Commute (sourceProjection ht) (inputFamily (fun n r => (outputTurn C D n r : CMatrix (Sector (α := α) n r))) T)
  rw [sourceProjection_diagonal]
  exact cutoff_commute_of_grade grade t _ (inputFamily_grade _ T)

theorem restrictedV_covariance (C D : Matrix.unitaryGroup α ℂ) {t T : ℕ}
    (h : t+1≤T) (ht : t<Fintype.card α) :
    ‖(fockQ C D T : CMatrix (InputCutoff (α := α) T))*restrictedV h-
      (fockQuery D T : CMatrix (InputCutoff (α := α) T))*restrictedV h*
        (fockQuery C T : CMatrix (InputCutoff (α := α) T))*(fockQ C D T : CMatrix (InputCutoff (α := α) T))‖≤
      16*Real.sqrt ((2*(t:ℝ)*(t+1))/Fintype.card α) := by
  apply cutoff_covariance _ _ (fockQuery C T) (fockQuery D T) (fockQ C D T)
    (sourceProjection_projection _) (source_commute_query C _) (source_commute_rotation C D _)
  have hh := fullOracle_covariance C D h ht
  rw [norm_sub_rev] at hh
  simpa only [Matrix.mul_assoc] using hh

end
end ICO.MHWRestricted
