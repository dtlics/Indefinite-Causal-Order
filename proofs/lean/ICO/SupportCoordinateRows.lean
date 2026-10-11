import ICO.SupportCoordinates
import ICO.TensorRealPart

namespace ICO.SupportCoordinates
open ICO.ExactSeparation ICO.ExactSupportIndependence ICO.ExactTensorCertificates
open ICO.TensorRowOperators ICO.TensorBitOrder
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
attribute [local irreducible] ICO.ExactSeparation.coordinate ICO.ExactSeparation.coordinateByNat

variable {K : Type*} [Fintype K]

def supportedChoi (x : K → Fin 25 → ℂ) : Matrix (Fin 128) (Fin 128) ℂ :=
  ∑ k, PositiveSupport.rankOne (encode (x k))

def supportCoordinates (x : K → Fin 25 → ℂ) : Vector := coefficients (realGram x)

theorem supported_tensor_expansion (x : K → Fin 25 → ℂ) :
    TensorRowOperators.realPart (periodicTensor (supportedChoi x)) =
      ∑ c : Coord, supportCoordinates x c •
        (intCastTensor (choiCoefficient (coordinate c).1 (coordinate c).2) : Tensor ℝ) := by
  ext i j
  simp only [TensorRowOperators.realPart, periodicTensor, supportedChoi, Matrix.sum_apply]
  have he := congrFun (congrFun (supported_choi_real x) (modIndex i)) (modIndex j)
  rw [he, support_matrix_expansion (realGram x) (realGram_symmetric x)]
  simp [supportCoordinates, intCastTensor, modIndex, choiCoefficient_mod128]

theorem coordinate_row_transport (x : K → Fin 25 → ℂ)
    (row : Nat → Nat → Nat → Int) (F : Nat → Tensor ℝ →ₗ[ℝ] ℝ)
    (hF : ∀ k a b, (row k a b : ℝ) = F k (intCastTensor (choiCoefficient a b)))
    (k : Nat) :
    rowValue (coefficient row) k (supportCoordinates x) =
      F k (TensorRowOperators.realPart (periodicTensor (supportedChoi x))) := by
  rw [supported_tensor_expansion]
  simp only [map_sum, map_smul, smul_eq_mul, rowValue, coefficient]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hF]
  ring

theorem support_abRows (x : K → Fin 25 → ℂ) (k : Nat) :
    rowValue (coefficient rowAB) k (supportCoordinates x) =
      (abRow k (periodicTensor (supportedChoi x))).re := by
  rw [coordinate_row_transport x rowAB abRow (fun k a b => abRow_cast a b k),
    ← abRow_realPart]

theorem support_baRows (x : K → Fin 25 → ℂ) (k : Nat) :
    rowValue (coefficient rowBA) k (supportCoordinates x) =
      (baRow k (periodicTensor (supportedChoi x))).re := by
  rw [coordinate_row_transport x rowBA baRow (fun k a b => baRow_cast a b k),
    ← baRow_realPart]

theorem support_gaugeRows (x : K → Fin 25 → ℂ) (k : Nat) :
    rowValue (coefficient rowGauge16) k (supportCoordinates x) =
      (gaugeRow k (periodicTensor (supportedChoi x))).re := by
  rw [coordinate_row_transport x rowGauge16 gaugeRow (fun k a b => gaugeRow_cast a b k),
    ← gaugeRow_realPart]

#print axioms support_abRows
#print axioms support_baRows
#print axioms support_gaugeRows
end
end ICO.SupportCoordinates
