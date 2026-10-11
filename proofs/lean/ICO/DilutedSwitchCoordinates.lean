import ICO.DilutedSwitchSemantics
import ICO.SupportCoordinateRows

namespace ICO.DilutedSwitchTarget
open ICO.ExactSeparation ICO.ExactTensorCertificates ICO.SupportCoordinates
open ICO.TensorRowOperators ICO.TensorBitOrder
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
attribute [local irreducible] ICO.ExactSeparation.coordinate ICO.ExactSeparation.coordinateByNat

theorem target_coefficients (lambda mu : ℝ) :
    coefficients (targetGram lambda mu) = target lambda mu := by
  funext c
  unfold coefficients target
  rw [targetGram_entry]

theorem target_tensor_expansion (lambda mu : ℝ) :
    TensorRowOperators.realPart (periodicTensor (targetChoi lambda mu)) =
      ∑ c : Coord, target lambda mu c •
        (intCastTensor (choiCoefficient (coordinate c).1 (coordinate c).2) : Tensor ℝ) := by
  ext i j
  change (targetChoi lambda mu (modIndex i) (modIndex j)).re = _
  have he := congrFun (congrFun (targetChoi_real_factor lambda mu) (modIndex i)) (modIndex j)
  change (targetChoi lambda mu (modIndex i) (modIndex j)).re =
    (realSupport * targetGram lambda mu * realSupport.transpose) (modIndex i) (modIndex j) at he
  rw [he, support_matrix_expansion _ (targetGram_symmetric lambda mu), target_coefficients]
  simp [intCastTensor, modIndex, choiCoefficient_mod128]

theorem target_gaugeRows (lambda mu : ℝ) (k : Nat) :
    rowValue (coefficient rowGauge16) k (target lambda mu) =
      (gaugeRow k (periodicTensor (targetChoi lambda mu))).re := by
  rw [gaugeRow_realPart, target_tensor_expansion]
  simp only [map_sum, map_smul, smul_eq_mul, rowValue, coefficient]
  apply Finset.sum_congr rfl
  intro c hc
  rw [gaugeRow_cast]
  ring

#print axioms target_gaugeRows
end
end ICO.DilutedSwitchTarget
