import ICO.ChoiWitnessState
import ICO.CommonPartDistance
import QIT.Channels.Diamond

/-! The normalized physical Choi test is an admissible diamond-distance input. -/
namespace ICO.ChoiWitnessState
open Matrix QIT ICO.CausalReverse ICO.ControlCoherence
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
variable {A Z : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype Z] [DecidableEq Z]

def choiOutputEquiv : ((A × A) × Z) ≃ ((A × Z) × A) where
  toFun x := ((x.1.2,x.2),x.1.1)
  invFun x := ((x.2,x.1.1),x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem bell_slice (p p' : A) :
    (fun i i' => bellMatrix A (i,p) (i',p')) =
      (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) • Matrix.single p p' (1 : ℂ) := by
  ext i i'
  simp only [bellMatrix_entry, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply,
    Complex.ofReal_inv, Complex.ofReal_natCast]
  by_cases hi : i = p <;> by_cases hj : i' = p' <;> simp_all [eq_comm]

/-- The grouped normalized Choi state is the output on a normalized Bell input,
up to a concrete tensor-factor permutation. -/
theorem normalizedChoi_matrix_output (Φ : Channel A (A × Z)) :
    (normalizedChoiState Φ).matrix =
      (((Φ.prod (Channel.idChannel A)).applyState
        (PureVector.maximallyEntangled (Equiv.refl A)).state).matrix).submatrix
          (choiOutputEquiv (A := A) (Z := Z)) (choiOutputEquiv (A := A) (Z := Z)) := by
  ext i j
  change (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) *
      Φ.map (Matrix.single i.1.1 j.1.1 1) (i.1.2,i.2) (j.1.2,j.2) =
    MatrixMap.kron Φ.map (Channel.idChannel A).map (bellMatrix A)
      ((i.1.2,i.2),i.1.1) ((j.1.2,j.2),j.1.1)
  rw [MatrixMap.kron_idChannel_apply_slice, bell_slice, map_smul]
  rfl

theorem normalizedChoi_distance_output (Φ Ψ : Channel A (A × Z)) :
    (normalizedChoiState Φ).normalizedTraceDistance (normalizedChoiState Ψ) =
      (((Φ.prod (Channel.idChannel A)).applyState
        (PureVector.maximallyEntangled (Equiv.refl A)).state).normalizedTraceDistance
       ((Ψ.prod (Channel.idChannel A)).applyState
        (PureVector.maximallyEntangled (Equiv.refl A)).state)) := by
  change (1/2 : ℝ) * traceNorm ((normalizedChoiState Φ).matrix - (normalizedChoiState Ψ).matrix) = _
  rw [normalizedChoi_matrix_output Φ, normalizedChoi_matrix_output Ψ]
  change (1/2 : ℝ) * traceNorm
    ((((Φ.prod (Channel.idChannel A)).applyState
      (PureVector.maximallyEntangled (Equiv.refl A)).state).matrix -
      ((Ψ.prod (Channel.idChannel A)).applyState
      (PureVector.maximallyEntangled (Equiv.refl A)).state).matrix).submatrix
        (choiOutputEquiv (A := A) (Z := Z)) (choiOutputEquiv (A := A) (Z := Z))) = _
  rw [traceNorm_submatrix_equiv]
  rfl

theorem state_distance_le_one {H : Type} [Fintype H] [DecidableEq H] (ρ σ : State H) :
    ρ.normalizedTraceDistance σ ≤ 1 := by
  simpa using ICO.CommonPartDistance.distance_le_missing_trace ρ σ 0
    (by simpa using ρ.pos) (by simpa using σ.pos)

theorem normalizedChoi_distance_le_diamond (Φ Ψ : Channel A (A × Z)) :
    (normalizedChoiState Φ).normalizedTraceDistance (normalizedChoiState Ψ) ≤
      Φ.diamondTraceDistance Ψ := by
  rw [normalizedChoi_distance_output]
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro y ⟨ω, rfl⟩
    exact state_distance_le_one _ _
  · exact ⟨(PureVector.maximallyEntangled (Equiv.refl A)).state, rfl⟩

#print axioms normalizedChoi_distance_le_diamond
end
end ICO.ChoiWitnessState
