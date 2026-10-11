import ICO.QubitUnitaryTests
import ICO.ExactSupportSpace
import ICO.UnitaryTestCertificates

namespace ICO.QubitLink
open ICO.ExactTensorCertificates ICO.UnitaryTestCertificates
open ICO.QubitUnitaryTests ICO.ExactSupportSpace
open Matrix
open scoped BigOperators ComplexConjugate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

def bit (i k : Nat) : Fin 2 := ⟨i / k % 2, Nat.mod_lt _ (by decide)⟩
def outputIndex (i : Fin 128) : Fin 8 := ⟨outIndex i.val, by
  unfold outIndex
  omega⟩

/-- Ordinary Choi-vector linking, with no conjugation of oracle entries. -/
def linkMatrix (U V : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 8) (Fin 128) ℂ :=
  fun o i => if o = outputIndex i then
    U (bit i.val 16) (bit i.val 32) * V (bit i.val 4) (bit i.val 8) else 0

/-- The four switch output vectors: I/I, U/I, I/V, U/V. The common factor
1/sqrt(2) from the fixed control state does not affect their support. -/
def outputVector (U V : Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 4) (o : Fin 8) : ℂ :=
  let p := bit o.val 4
  let t := bit o.val 1
  if b.val = 0 then (if p = t then 1 else 0)
  else if b.val = 1 then U t p
  else if b.val = 2 then V t p
  else if o.val / 2 % 2 = 0 then (V * U) t p else (U * V) t p

def outputScale (s t : ℂ) (b : Fin 4) : ℂ :=
  if b.val = 0 then 1 else if b.val = 1 then s else if b.val = 2 then t else s*t

theorem link_scaled (s t : ℂ) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    linkMatrix (s • U) (t • V) = (s*t) • linkMatrix U V := by
  ext o i
  simp only [linkMatrix, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem output_scaled (s t : ℂ) (U V : Matrix (Fin 2) (Fin 2) ℂ) (b : Fin 4) :
    outputVector (s • U) (t • V) b = outputScale s t b • outputVector U V b := by
  funext o
  fin_cases b <;>
    norm_num [outputVector, outputScale, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem pairComplex_sum (n : Nat) (f : Nat → GPair) :
    pairComplex (gpSum n f) = ∑ i : Fin n, pairComplex (f i.val) := by
  simp only [pairComplex, gpSum, sumBelow_complex, Finset.sum_add_distrib,
    Finset.sum_mul]

theorem pairComplex_qProduct (q s : QData) (i j : Fin 2) :
    pairComplex (qProduct q s i.val j.val) = (qMatrix q * qMatrix s) i j := by
  simp only [qProduct, pairComplex_sum, pairComplex_mul, Matrix.mul_apply, qMatrix]

theorem fourOutput_complex (r : Nat) (b : Fin 4) (o : Fin 8) :
    pairComplex (fourOutput r b.val o.val) =
      outputVector (qMatrix (uData r)) (qMatrix (vData r)) b o := by
  fin_cases b <;> fin_cases o <;>
    simp [fourOutput, outputVector, bit, pairComplex_qProduct,
      qProduct, pairComplex_sum, pairComplex_mul, Matrix.mul_apply,
      Fin.sum_univ_two, qMatrix, pairComplex, qEntry, gpSum, sumBelow, gpMul] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

def annihilator (r : Fin 103) (o : Fin 8) : ℂ := pairComplex (annData r.val o.val)

theorem annihilator_output (r : Fin 103) (b : Fin 4) :
    annihilator r ⬝ᵥ outputVector (qMatrix (uData r.val)) (qMatrix (vData r.val)) b = 0 := by
  calc
    _ = pairComplex (annihilation r.val b.val) := by
      unfold annihilation
      rw [pairComplex_sum]
      simp only [pairComplex_mul, fourOutput_complex, dotProduct, annihilator]
    _ = 0 := by rw [all_ann_zero]; simp [pairComplex]

def headIndex (r : Fin 103) : Fin 128 := ⟨r.val, by omega⟩

theorem pairComplex_double (a : GPair) :
    pairComplex (2*a.1, 2*a.2) = 2*pairComplex a := by
  simp [pairComplex, Int.cast_mul]
  ring

theorem annihilator_link (r : Fin 103) :
    annihilator r ᵥ* linkMatrix (qMatrix (uData r.val)) (qMatrix (vData r.val)) =
      fun i => 2 * complexStack (headIndex r) i := by
  funext i
  have h := congrArg pairComplex (all_test_rows r i)
  rw [pairComplex_double] at h
  simp only [testRow, pairComplex_mul] at h
  simpa [Matrix.vecMul, dotProduct, linkMatrix, mul_ite, outputIndex,
    annihilator, qMatrix, bit, headIndex, stack_entry, pairComplex] using h

theorem annihilator_normalized_output (r : Fin 103) (b : Fin 4) :
    annihilator r ⬝ᵥ outputVector (normalizedMatrix (uData r.val))
      (normalizedMatrix (vData r.val)) b = 0 := by
  rw [normalizedMatrix, normalizedMatrix, output_scaled, dotProduct_smul,
    annihilator_output, smul_zero]

theorem annihilator_normalized_link (r : Fin 103) (v : Fin 128 → ℂ) :
    annihilator r ⬝ᵥ (linkMatrix (normalizedMatrix (uData r.val))
      (normalizedMatrix (vData r.val)) *ᵥ v) =
      (normalization (uData r.val) * normalization (vData r.val)) *
        (2 * (complexStack *ᵥ v) (headIndex r)) := by
  rw [normalizedMatrix, normalizedMatrix, link_scaled, Matrix.smul_mulVec,
    dotProduct_smul, dotProduct_mulVec, annihilator_link]
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

end
end ICO.QubitLink

