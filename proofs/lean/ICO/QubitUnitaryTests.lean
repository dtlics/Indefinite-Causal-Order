import ICO.UnitaryTestDefinitions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace ICO.QubitUnitaryTests
open ICO.UnitaryTestCertificates
open scoped BigOperators ComplexConjugate Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

def pairComplex (a : GPair) : ℂ := (a.1 : ℂ) + (a.2 : ℂ) * Complex.I

theorem pairComplex_add (a b : GPair) :
    pairComplex (gpAdd a b) = pairComplex a + pairComplex b := by
  simp [pairComplex, gpAdd, Int.cast_add]
  ring

theorem pairComplex_mul (a b : GPair) :
    pairComplex (gpMul a b) = pairComplex a * pairComplex b := by
  simp [pairComplex, gpMul, Int.cast_add, Int.cast_sub, Int.cast_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

def qMatrix (q : QData) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => pairComplex (qEntry q i.val j.val)

theorem qMatrix_adjoint_mul (q : QData) :
    (qMatrix q)ᴴ * qMatrix q = (qNorm q : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      qMatrix, pairComplex, qEntry, qNorm, Matrix.one_apply, Complex.conj_ofReal,
      star_add, star_mul, Int.cast_add, Int.cast_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def normalization (q : QData) : ℂ := ((Real.sqrt (qNorm q : ℝ))⁻¹ : ℝ)

def normalizedMatrix (q : QData) : Matrix (Fin 2) (Fin 2) ℂ :=
  normalization q • qMatrix q

theorem normalization_ne_zero (q : QData) (hq : 0 < qNorm q) :
    normalization q ≠ 0 := by
  have hqr : (0 : ℝ) < qNorm q := by exact_mod_cast hq
  simp [normalization, ne_of_gt (Real.sqrt_pos.2 hqr)]

theorem normalized_unitary (q : QData) (hq : 0 < qNorm q) :
    (normalizedMatrix q)ᴴ * normalizedMatrix q = 1 := by
  have hqr : (0 : ℝ) < qNorm q := by exact_mod_cast hq
  have hs : (Real.sqrt (qNorm q : ℝ))^2 = (qNorm q : ℝ) := Real.sq_sqrt hqr.le
  have hn : normalization q * normalization q * (qNorm q : ℂ) = 1 := by
    rw [normalization]
    norm_cast
    field_simp [ne_of_gt (Real.sqrt_pos.2 hqr)]
    nlinarith [hs]
  rw [normalizedMatrix, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, qMatrix_adjoint_mul, smul_smul, smul_smul]
  have hstar : star (normalization q) = normalization q := by
    exact Complex.conj_ofReal _
  rw [hstar]
  change (normalization q * normalization q * (qNorm q : ℂ)) •
    (1 : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [hn, one_smul]

end
end ICO.QubitUnitaryTests
