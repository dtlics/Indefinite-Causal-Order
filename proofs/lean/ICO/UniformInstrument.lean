import ICO.InstrumentCompression
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # A physical uniform classical draw that preserves the quantum register -/

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression

namespace ICO.UniformInstrument
set_option maxHeartbeats 400000
noncomputable section
universe u
variable {H I : Type u} [Fintype H] [Fintype I] [DecidableEq H] [Nonempty I]

def amplitude : ℂ := ((Real.sqrt ((Fintype.card I : ℝ)⁻¹) : ℝ) : ℂ)

theorem amplitude_square : star (amplitude (I := I)) * amplitude (I := I) =
    (Fintype.card I : ℂ)⁻¹ := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (Fintype.card I : ℝ)⁻¹ by positivity)
  simp only [amplitude, Complex.star_def, Complex.conj_ofReal,
    ← pow_two, ← Complex.ofReal_pow, hs, Complex.ofReal_inv, Complex.ofReal_natCast]

def op : Matrix H H ℂ := amplitude (I := I) • 1

theorem op_complete : (op (H := H) (I := I)).conjTranspose * op (H := H) (I := I) =
    (Fintype.card I : ℂ)⁻¹ • (1 : CMatrix H) := by
  simp only [op, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  rw [mul_comm, amplitude_square]

def instrument : Instrument H H I where
  op := fun _ => op (H := H) (I := I)
  complete := by
    simp only [op_complete, Finset.sum_const, Finset.card_univ]
    have hd : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hd]

theorem branch_apply (i : I) (X : CMatrix H) :
    branchMap (instrument (H := H) (I := I)) i X = (Fintype.card I : ℂ)⁻¹ • X := by
  classical
  rw [branchMap_apply]
  simp only [instrument, op, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [amplitude_square]

theorem channel_map {O : Type u} [Fintype O] [DecidableEq O] [DecidableEq I]
    (next : I → Channel H O) :
    (adaptiveChannel (instrument (H := H) (I := I)) next).map =
      (Fintype.card I : ℂ)⁻¹ • ∑ i, (next i).map := by
  classical
  ext X a b
  simp [adaptiveChannel, adaptiveMap, branch_apply, map_smul, Finset.smul_sum]

end
end ICO.UniformInstrument
