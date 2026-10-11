import ICO.SwitchObservable
import ICO.SwitchSampling
import QIT.Core.POVMProbability
import QIT.Util.BlockMatrix

/-! The actual binary control measurement and its Born-rule probability. -/

namespace ICO.SwitchExperiment

open Matrix QIT
open ICO.SwitchObservable
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {n ι κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [Fintype κ]

def plusEffect : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  (1 / 2 : ℂ) • (1 + controlX)

theorem controlX_hermitian : (controlX (n := n))ᴴ = controlX := by
  simp [controlX, Matrix.fromBlocks_conjTranspose]

theorem controlX_square : (controlX (n := n)) * controlX = 1 := by
  simp [controlX, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem plusEffect_hermitian : (plusEffect (n := n))ᴴ = plusEffect := by
  simp [plusEffect, Matrix.conjTranspose_smul, controlX_hermitian]

theorem plusEffect_square : (plusEffect (n := n)) * plusEffect = plusEffect := by
  simp only [plusEffect, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    controlX_square]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply]
  ring

theorem plusEffect_pos : (plusEffect (n := n)).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (plusEffect (n := n))
  simpa only [plusEffect_hermitian, plusEffect_square] using h

def controlMeasurement : QIT.POVM Bool (n ⊕ n) where
  effects b := cond b plusEffect (1 - plusEffect)
  pos b := by
    cases b
    · exact MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent
        plusEffect plusEffect_pos plusEffect_square
    · exact plusEffect_pos
  sum_eq_one := by simp

theorem plusTarget_pos (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) :
    (plusTarget ρ).PosSemidef := by
  have hd := Matrix.fromBlocks_diagonal_posSemidef hρ hρ
  have h := hd.mul_mul_conjTranspose_same (plusEffect (n := n))
  have heq : plusEffect * Matrix.fromBlocks ρ 0 0 ρ * plusEffectᴴ = plusTarget ρ := by
    rw [plusEffect_hermitian]
    simp only [plusEffect, controlX, plusTarget]
    rw [← Matrix.fromBlocks_one]
    simp only [Matrix.fromBlocks_add, Matrix.fromBlocks_multiply,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.zero_mul,
      Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.smul_apply] <;> ring
  rw [heq] at h
  exact h

def plusState (ρ : QIT.State n) : QIT.State (n ⊕ n) where
  matrix := plusTarget ρ.matrix
  pos := plusTarget_pos ρ.matrix ρ.pos
  trace_eq_one := by
    simp [plusTarget, Matrix.trace_smul, trace_fromBlocks, ρ.trace_eq_one]
    norm_num

def switchedState (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (ρ : QIT.State n) : QIT.State (n ⊕ n) where
  matrix := switchOutput A B ρ.matrix
  pos := by
    have h := MatrixMap.ofKraus_mapsPositive
      (fun p : ι × κ => switchKraus (A p.1) (B p.2))
      (plusState ρ).matrix (plusState ρ).pos
    simpa only [MatrixMap.ofKraus, plusState, switchOutput, Fintype.sum_prod_type] using h
  trace_eq_one := by
    have hn : MatrixMap.krausAdjoint
        (fun p : ι × κ => switchKraus (A p.1) (B p.2)) 1 = 1 := by
      simpa [MatrixMap.krausAdjoint, Fintype.sum_prod_type] using
        switch_kraus_complete A B hA hB
    have ht := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _ hn
      (plusState ρ).matrix
    change (∑ p : ι × κ, switchKraus (A p.1) (B p.2) *
      (plusState ρ).matrix * (switchKraus (A p.1) (B p.2))ᴴ).trace =
        (plusState ρ).matrix.trace at ht
    rw [Fintype.sum_prod_type] at ht
    exact ht.trans (plusState ρ).trace_eq_one

theorem plus_probability (ρ : QIT.State (n ⊕ n)) :
    ((controlMeasurement (n := n)).prob ρ true : ℝ) =
      (1 + (controlX * ρ.matrix).trace.re) / 2 := by
  rw [QIT.POVM.prob_eq_trace_re]
  simp only [controlMeasurement, Bool.cond_true, plusEffect, Matrix.mul_smul,
    Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add,
    ρ.trace_eq_one]
  rw [Matrix.trace_mul_comm ρ.matrix controlX]
  simp [Complex.mul_re]
  ring

def mixedState [Nonempty n] : QIT.State n where
  matrix := (Fintype.card n : ℂ)⁻¹ • (1 : Matrix n n ℂ)
  pos := Matrix.PosSemidef.smul Matrix.PosSemidef.one (by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card n)) :
      (0 : ℝ) ≤ (Fintype.card n : ℝ)⁻¹))
  trace_eq_one := by
    simp [Matrix.trace_smul, Matrix.trace_one, Fintype.card_ne_zero]

theorem switch_plus_probability [Nonempty n]
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1) :
    ((controlMeasurement (n := n)).prob
      (switchedState A B hA hB mixedState) true : ℝ) =
        (1 + interference A B) / 2 := by
  rw [plus_probability]
  change (1 + (controlX * switchOutput A B
    ((Fintype.card n : ℂ)⁻¹ • (1 : Matrix n n ℂ))).trace.re) / 2 = _
  rw [switch_X_mean]

theorem switch_eighty_high_error [Nonempty n]
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (hvis : (2 / 3 : ℝ) ≤ interference A B) :
    let p := (controlMeasurement (n := n)).prob
      (switchedState A B hA hB mixedState) true
    (SwitchSampling.repetitions 80 p (by
      exact_mod_cast QIT.POVM.prob_le_one controlMeasurement
        (switchedState A B hA hB mixedState) true)).real
      {ω | (∑ i, SwitchSampling.outcome i ω) < 60} < 1 / 3 := by
  dsimp only
  apply SwitchSampling.eighty_high_error
  rw [switch_plus_probability]
  linarith

theorem switch_eighty_low_error [Nonempty n]
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1) (hB : ∑ j, (B j)ᴴ * B j = 1)
    (hvis : interference A B ≤ (1 / 3 : ℝ)) :
    let p := (controlMeasurement (n := n)).prob
      (switchedState A B hA hB mixedState) true
    (SwitchSampling.repetitions 80 p (by
      exact_mod_cast QIT.POVM.prob_le_one controlMeasurement
        (switchedState A B hA hB mixedState) true)).real
      {ω | 60 ≤ ∑ i, SwitchSampling.outcome i ω} < 1 / 3 := by
  dsimp only
  apply SwitchSampling.eighty_low_error
  rw [switch_plus_probability]
  linarith

#print axioms plus_probability
#print axioms switchedState
#print axioms switch_eighty_high_error
#print axioms switch_eighty_low_error

end
end ICO.SwitchExperiment
