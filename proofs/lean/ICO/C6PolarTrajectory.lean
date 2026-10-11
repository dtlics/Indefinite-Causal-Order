import ICO.C6PolarReplacement
import ICO.C6MatrixTrajectory

/-! Literal varying-memory polar replacement, including all known operations
between successive inverse/middle/forward pairs. -/
namespace ICO.C6PolarTrajectory
open QIT ICO.C6PolarReplacement ICO.C6PolarFockBounds ICO.C6MatrixTrajectory
  ICO.MHBoundedRecording ICO.MHRectangularAction
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {α:Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  {μ ν:ℕ→Type*} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]
  [∀i,Fintype (ν i)] [∀i,DecidableEq (ν i)]

def oldStage {t T:ℕ} (h:t+1≤T)
    (L:∀i,Matrix (InputCutoff (α:=α) T×ν i) (InputCutoff (α:=α) T×μ i) ℂ)
    (K:∀i,Matrix (InputCutoff (α:=α) T×μ (i+1)) (InputCutoff (α:=α) T×ν i) ℂ)
    (i:ℕ) : Matrix (InputCutoff (α:=α) T×μ (i+1)) (InputCutoff (α:=α) T×μ i) ℂ :=
  K i*oldPair h (L i)

def polarStage {t T:ℕ} (h:t+1≤T)
    (L:∀i,Matrix (InputCutoff (α:=α) T×ν i) (InputCutoff (α:=α) T×μ i) ℂ)
    (K:∀i,Matrix (InputCutoff (α:=α) T×μ (i+1)) (InputCutoff (α:=α) T×ν i) ℂ)
    (i:ℕ) : Matrix (InputCutoff (α:=α) T×μ (i+1)) (InputCutoff (α:=α) T×μ i) ℂ :=
  K i*polarPair h (L i)

theorem oldStage_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α)
    (L:∀i,Matrix (InputCutoff (α:=α) T×ν i) (InputCutoff (α:=α) T×μ i) ℂ)
    (K:∀i,Matrix (InputCutoff (α:=α) T×μ (i+1)) (InputCutoff (α:=α) T×ν i) ℂ)
    (hL:∀i,‖L i‖≤1) (hK:∀i,‖K i‖≤1) (i:ℕ) : ‖oldStage h L K i‖≤1 := by
  exact (Matrix.l2_opNorm_mul _ _).trans (by
    simpa using mul_le_mul (hK i) (oldPair_norm h ht (L i) (hL i))
      (norm_nonneg _) (by norm_num))

theorem polarStage_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α)
    (L:∀i,Matrix (InputCutoff (α:=α) T×ν i) (InputCutoff (α:=α) T×μ i) ℂ)
    (K:∀i,Matrix (InputCutoff (α:=α) T×μ (i+1)) (InputCutoff (α:=α) T×ν i) ℂ)
    (hL:∀i,‖L i‖≤1) (hK:∀i,‖K i‖≤1) (i:ℕ) : ‖polarStage h L K i‖≤1 := by
  exact (Matrix.l2_opNorm_mul _ _).trans (by
    simpa using mul_le_mul (hK i) (polarPair_norm h ht (L i) (hL i))
      (norm_nonneg _) (by norm_num))

theorem stage_difference {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α)
    (L:∀i,Matrix (InputCutoff (α:=α) T×ν i) (InputCutoff (α:=α) T×μ i) ℂ)
    (K:∀i,Matrix (InputCutoff (α:=α) T×μ (i+1)) (InputCutoff (α:=α) T×ν i) ℂ)
    (hL:∀i,‖L i‖≤1) (hK:∀i,‖K i‖≤1) (i:ℕ) :
    ‖oldStage h L K i-polarStage h L K i‖≤7*delta t (Fintype.card α) := by
  rw [oldStage,polarStage,←Matrix.mul_sub]
  exact (Matrix.l2_opNorm_mul _ _).trans (by
    have hh := mul_le_mul_of_nonneg_right (hK i)
      (norm_nonneg (oldPair h (L i)-polarPair h (L i)))
    simp only [one_mul] at hh
    exact hh.trans (pair_difference h ht (L i) (hL i)))

/-- The constant comes from one δ_t forward-creator replacement and one
6δ_t inverse-full-oracle replacement per pair. No fixed-memory assumption. -/
theorem trajectory_distance {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card α)
    (L:∀i,Matrix (InputCutoff (α:=α) T×ν i) (InputCutoff (α:=α) T×μ i) ℂ)
    (K:∀i,Matrix (InputCutoff (α:=α) T×μ (i+1)) (InputCutoff (α:=α) T×ν i) ℂ)
    (hL:∀i,‖L i‖≤1) (hK:∀i,‖K i‖≤1)
    (z:EuclideanSpace ℂ (InputCutoff (α:=α) T×μ 0)) (hz:‖z‖≤1) (q:ℕ) :
    ‖run (H:=fun i => InputCutoff (α:=α) T×μ i) (oldStage h L K) z q-run (H:=fun i => InputCutoff (α:=α) T×μ i) (polarStage h L K) z q‖≤
      7*(q:ℝ)*delta t (Fintype.card α) := by
  have hh := run_distance (H:=fun i => InputCutoff (α:=α) T×μ i) (oldStage h L K) (polarStage h L K)
    (oldStage_norm h ht L K hL hK) (polarStage_norm h ht L K hL hK)
    (7*delta t (Fintype.card α)) (stage_difference h ht L K hL hK) z hz q
  convert hh using 1 <;> ring

#print axioms trajectory_distance
end
end ICO.C6PolarTrajectory
