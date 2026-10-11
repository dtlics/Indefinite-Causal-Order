import ICO.ChoiDiamond
import ICO.MemoryEmbedding

/-! Ordinary input preparation cannot increase half-diamond distance. -/
namespace ICO.DiamondPreprocessing
open Matrix QIT ICO.ClassicalDilation ICO.MemoryEmbedding
noncomputable section
set_option maxHeartbeats 800000
variable {A B O : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B] [Fintype O] [DecidableEq O]

theorem identity_map {H : Type} [Fintype H] [DecidableEq H] :
    (Channel.idChannel H).map = LinearMap.id := by
  ext X i j
  simp [Channel.idChannel, MatrixMap.ofKraus]

theorem input_distance_le_diamond (Φ Ψ : Channel B O) (ω : State (B × B)) :
    ((Φ.prod (Channel.idChannel B)).applyState ω).normalizedTraceDistance
      ((Ψ.prod (Channel.idChannel B)).applyState ω) ≤ Φ.diamondTraceDistance Ψ := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro y ⟨ρ,rfl⟩
    exact ICO.ChoiWitnessState.state_distance_le_one _ _
  · exact ⟨ω,rfl⟩

theorem decoded_input (Φ : Channel B O) (P E : Channel A B) (R : Channel B A)
    (hRE : R.map.comp E.map = LinearMap.id) (ω : State (A × A)) :
    ((Channel.idChannel O).prod R).applyState
      ((Φ.prod (Channel.idChannel B)).applyState ((P.prod E).applyState ω)) =
        (((Φ.comp P).prod (Channel.idChannel A)).applyState ω) := by
  apply State.ext
  change MatrixMap.kron (Channel.idChannel O).map R.map
    (MatrixMap.kron Φ.map (Channel.idChannel B).map
      (MatrixMap.kron P.map E.map ω.matrix)) =
    MatrixMap.kron (Φ.map.comp P.map) (Channel.idChannel A).map ω.matrix
  rw [MatrixMap.kron_comp_apply_general, MatrixMap.kron_comp_apply_general]
  simp only [identity_map, LinearMap.id_comp, LinearMap.comp_id, hRE]

theorem diamond_precompose_le (Φ Ψ : Channel B O) (P E : Channel A B) (R : Channel B A)
    (hRE : R.map.comp E.map = LinearMap.id) :
    (Φ.comp P).diamondTraceDistance (Ψ.comp P) ≤ Φ.diamondTraceDistance Ψ := by
  apply Channel.diamondTraceDistance_le_of_inputReferenceBound
  intro ω
  have h := Channel.normalizedTraceDistance_applyState_le ((Channel.idChannel O).prod R)
    ((Φ.prod (Channel.idChannel B)).applyState ((P.prod E).applyState ω))
    ((Ψ.prod (Channel.idChannel B)).applyState ((P.prod E).applyState ω))
  rw [decoded_input Φ P E R hRE ω, decoded_input Ψ P E R hRE ω] at h
  exact h.trans (input_distance_le_diamond Φ Ψ ((P.prod E).applyState ω))

theorem diamond_precompose_of_embedding (Φ Ψ : Channel B O) (P : Channel A B)
    (e : A ↪ B) : (Φ.comp P).diamondTraceDistance (Ψ.comp P) ≤ Φ.diamondTraceDistance Ψ := by
  let E := isometryChannel (embedding e) (embedding_isometry e)
  let R := retractChannel e (Classical.choice (inferInstance : Nonempty A))
  apply diamond_precompose_le Φ Ψ P E R
  ext X i j
  change R.map (E.map X) i j = X i j
  simp only [E, R, isometryChannel_apply, retract_embedding_identity]

#print axioms diamond_precompose_of_embedding
end
end ICO.DiamondPreprocessing
