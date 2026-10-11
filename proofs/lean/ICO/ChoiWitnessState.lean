import ICO.GramControl
import ICO.CompositionGram
import ICO.ReverseCompositionGram
import ICO.TreeCoherence

/-! The normalized physical Choi state, in the coordinate convention of
the switch Gram witness. Its cross quadratic is the actual channel coherence. -/
namespace ICO.ChoiWitnessState
open Matrix QIT ICO.TreeCoherence ICO.ControlCoherence ICO.CircuitOutput
open ICO.CompositionGram ICO.GramWitness
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
variable {A Z : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype Z] [DecidableEq Z]

theorem grouped_channelChoi_pos (Φ : Channel A (A × Z)) :
    (groupedMapChoi Φ.map).PosSemidef :=
  Φ.completelyPositive.submatrix _

theorem grouped_channelChoi_trace (Φ : Channel A (A × Z)) :
    (groupedMapChoi Φ.map).trace = (Fintype.card A : ℂ) := by
  have he : (groupedMapChoi Φ.map).trace = (MatrixMap.choi Φ.map).trace := by
    simp [groupedMapChoi, Matrix.trace, Matrix.diag_apply, Matrix.submatrix,
      Fintype.sum_prod_type]
  rw [he, ICO.ChoiMass.choi_trace_eq_apply_one, Φ.tracePreserving, Matrix.trace_one]

def normalizedChoiState (Φ : Channel A (A × Z)) : State ((A × A) × Z) where
  matrix := (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) • groupedMapChoi Φ.map
  pos := (grouped_channelChoi_pos Φ).smul (by
    exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card A)) :
      (0 : ℝ) ≤ (Fintype.card A : ℝ)⁻¹))
  trace_eq_one := by
    rw [Matrix.trace_smul, grouped_channelChoi_trace]
    simp [Complex.ofReal_inv, Fintype.card_ne_zero]

theorem controlVector_smul {H : Type} [Fintype H]
    (c : ℂ) (v : H → ℂ) (z : Z) :
    controlVector (c • v) z = c • controlVector v z := by
  funext p
  by_cases hp : p.2 = z <;> simp [controlVector, hp]

theorem normalized_quadratic_eq_coherence (Φ : Channel A (A × Z))
    (z z' : Z) (T S : CMatrix A) :
    star (controlVector (coefficient (A := A) • targetVector T) z) ⬝ᵥ
      ((normalizedChoiState Φ).matrix *ᵥ
        controlVector (coefficient (A := A) • targetVector S) z') =
      mapCoherence Φ.map z z' T S := by
  simp only [controlVector_smul, star_smul, coefficient_star, normalizedChoiState,
    Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, mapCoherence]
  have hc : coefficient (A := A) * (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) *
      coefficient (A := A) = (((Fintype.card A : ℝ)^2)⁻¹ : ℝ) := by
    calc
      _ = (coefficient (A := A) * coefficient (A := A)) *
          (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) := by ring
      _ = _ := by
        rw [coefficient_square]
        simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast,
          Complex.ofReal_mul, pow_two, mul_inv]
  calc
    _ = (coefficient (A := A) * (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) *
        coefficient (A := A)) *
      (star (controlVector (targetVector T) z) ⬝ᵥ
        (groupedMapChoi Φ.map *ᵥ controlVector (targetVector S) z')) := by ring
    _ = _ := by rw [hc]

theorem columns_cross_eq_coherence {r s : ℕ}
    (Φ : Channel A (A × Bool)) (U : Fin r → Matrix.unitaryGroup A ℂ)
    (V : Fin s → Matrix.unitaryGroup A ℂ) (ij : Fin r × Fin s) :
    star (controlVector (fun p => columns U V p ij) false) ⬝ᵥ
      ((normalizedChoiState Φ).matrix *ᵥ
        controlVector (fun p => ICO.ReverseCompositionGram.reverseColumns U V p ij) true) =
      mapCoherence Φ.map false true
        ((V ij.2 : CMatrix A) * (U ij.1 : CMatrix A))
        ((U ij.1 : CMatrix A) * (V ij.2 : CMatrix A)) := by
  exact normalized_quadratic_eq_coherence Φ false true _ _

#print axioms normalizedChoiState
#print axioms normalized_quadratic_eq_coherence
#print axioms columns_cross_eq_coherence
end
end ICO.ChoiWitnessState
