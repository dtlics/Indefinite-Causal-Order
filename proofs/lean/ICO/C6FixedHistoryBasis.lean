import ICO.C6HistoryCoordinates

/-! One adapted basis for all actual private-history prefixes of a complete
outcome transcript. No independently chosen prefix bases are assumed. -/
namespace ICO.C6FixedHistoryBasis
open Matrix QIT ICO.C6HistoryCoordinates ICO.C6RetainedHistory ICO.C6ResidualModes
  ICO.C6ResidualCoordinates ICO.C6ResidualSpan ICO.C6CacheSpanProjection
  ICO.RecordingPurifiedProtocol
noncomputable section
set_option maxHeartbeats 900000
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem prior_actual (H:Matrix.unitaryGroup A ℂ) {q:ℕ} (η:History (A×Bool) q)
    (i:Fin q) : vectors H i.val (prefixHistory η i.val i.isLt.le)=prior (vectors H q η) i := by
  rw [vectors_prefix]
  rfl

theorem actual_history_basis (H:Matrix.unitaryGroup A ℂ) (q:ℕ) (η:History (A×Bool) q) :
    ∃(U:Matrix.unitaryGroup A ℂ)(labels:Active (vectors H q η)→A),
      Function.Injective labels ∧
      (∀i x,(U:CMatrix A) x (labels i)=mode (vectors H q η) i x) ∧
      ∀s (hs:s≤q),historyProjection (vectors H s (prefixHistory η s hs))=
        spanProjection U (activeIndices (vectors H q η) labels s) := by
  obtain ⟨U,f,hf,he,hP⟩:=all_prefix_projections (vectors H q η)
  refine ⟨U,f,hf,he,?_⟩
  intro s hs
  rw [vectors_prefix]
  exact hP s hs

#print axioms actual_history_basis
end
end ICO.C6FixedHistoryBasis
