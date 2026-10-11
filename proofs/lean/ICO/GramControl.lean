import ICO.GramNorm
import ICO.ControlCoherence

namespace ICO.GramWitness
open Matrix QIT ICO.CausalReverse ICO.ControlCoherence
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 0
variable {H I : Type} [Fintype H] [DecidableEq H] [Nonempty H]
  [Fintype I] [DecidableEq I] [Nonempty I]

def switchCoefficient : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

theorem switchCoefficient_square : switchCoefficient * switchCoefficient = (1 / 2 : ℂ) := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have he : (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt (2 : ℝ))⁻¹ = 1 / 2 := by
    field_simp
    nlinarith
  unfold switchCoefficient
  rw [← Complex.ofReal_mul, he]
  norm_num

def switchColumns (X Y : Matrix H I ℂ) : Matrix (H × Bool) I ℂ :=
  fun hb i => switchCoefficient * if hb.2 then Y hb.1 i else X hb.1 i

theorem frame_eq_sum_columns (Z : Matrix H I ℂ) :
    frame Z = ∑ i : I, rankOneMatrix (fun h => Z h i) := by
  ext u v
  simp [frame, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    rankOneMatrix_apply]

theorem switch_column (X Y : Matrix H I ℂ) (i : I) :
    (fun hb => switchColumns X Y hb i) = switchCoefficient •
      (controlVector (fun h => X h i) false + controlVector (fun h => Y h i) true) := by
  ext hb
  rcases hb with ⟨h, b⟩
  cases b <;> simp [switchColumns, controlVector]

theorem hermitian_cross_star (ρ : CMatrix H) (hρ : ρ.IsHermitian) (x y : H → ℂ) :
    star (star x ⬝ᵥ (ρ *ᵥ y)) = star y ⬝ᵥ (ρ *ᵥ x) := by
  calc
    _ = star (ρ *ᵥ y) ⬝ᵥ x := by
      simpa using (Matrix.star_dotProduct_star (ρ *ᵥ y) (star x)).symm
    _ = _ := by rw [Matrix.star_mulVec, hρ.eq, Matrix.dotProduct_mulVec]

theorem switch_quadratic (ρ : CMatrix H) (hρ : ρ.IsHermitian) (x y : H → ℂ) :
    (star (switchCoefficient • (x + y)) ⬝ᵥ
      (ρ *ᵥ (switchCoefficient • (x + y)))).re =
      (1 / 2 : ℝ) * (star x ⬝ᵥ (ρ *ᵥ x)).re +
      (1 / 2 : ℝ) * (star y ⬝ᵥ (ρ *ᵥ y)).re +
      (star x ⬝ᵥ (ρ *ᵥ y)).re := by
  have hc : star switchCoefficient = switchCoefficient := by simp [switchCoefficient]
  have hyx := hermitian_cross_star ρ hρ x y
  simp only [star_smul, star_add, Matrix.mulVec_smul, Matrix.mulVec_add,
    dotProduct_smul, smul_dotProduct, dotProduct_add, add_dotProduct, smul_eq_mul, hc]
  rw [← mul_add, ← mul_assoc, switchCoefficient_square]
  rw [← hyx]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, zero_mul, sub_zero]
  norm_num
  ring

def block (ρ : CMatrix (H × Bool)) (b : Bool) : CMatrix H :=
  ρ.submatrix (fun h => (h, b)) (fun h => (h, b))

def crossScore (X Y : Matrix H I ℂ) (ρ : CMatrix (H × Bool)) : ℝ :=
  ∑ i : I, (star (controlVector (fun h => X h i) false) ⬝ᵥ
    (ρ *ᵥ controlVector (fun h => Y h i) true)).re

theorem tracePair_sum (ρ : CMatrix H) (W : I → CMatrix H) :
    tracePair ρ (∑ i, W i) = ∑ i, tracePair ρ (W i) := by
  simp [tracePair, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

theorem switch_frame_score (X Y : Matrix H I ℂ) (ρ : CMatrix (H × Bool))
    (hρ : ρ.IsHermitian) :
    tracePair ρ (frame (switchColumns X Y)) =
      (1 / 2 : ℝ) * tracePair (block ρ false) (frame X) +
      (1 / 2 : ℝ) * tracePair (block ρ true) (frame Y) + crossScore X Y ρ := by
  rw [frame_eq_sum_columns, tracePair_sum]
  simp_rw [tracePair_rankOne_eq_quadratic, switch_column,
    switch_quadratic ρ hρ, controlVector_quadratic]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [frame_eq_sum_columns X, tracePair_sum, frame_eq_sum_columns Y, tracePair_sum]
  simp_rw [tracePair_rankOne_eq_quadratic]
  rfl

#print axioms switch_quadratic
#print axioms switch_frame_score

theorem block_pos (ρ : CMatrix (H × Bool)) (hρ : ρ.PosSemidef) (b : Bool) :
    (block ρ b).PosSemidef := hρ.submatrix _

theorem block_mass_nonneg (ρ : CMatrix (H × Bool)) (hρ : ρ.PosSemidef) (b : Bool) :
    0 ≤ (block ρ b).trace.re := by
  exact Complex.nonneg_iff.mp (block_pos ρ hρ b).trace_nonneg |>.1

theorem block_mass_sum (ρ : CMatrix (H × Bool)) :
    (block ρ false).trace.re + (block ρ true).trace.re = ρ.trace.re := by
  simp [block, Matrix.trace, Matrix.diag_apply, Matrix.submatrix,
    Fintype.sum_prod_type, Finset.sum_add_distrib, Complex.re_sum, add_comm]

theorem frame_pair_le_one_add_defect (Z : Matrix H I ℂ) (ρ : CMatrix H)
    (hρ : ρ.PosSemidef) :
    tracePair ρ (frame Z) ≤ (1 + ‖gram Z - 1‖) * ρ.trace.re := by
  have hh := positive_pair_le_norm_trace (frame Z) ρ (frame_pos Z) hρ
  have hb : ‖frame Z‖ ≤ 1 + ‖gram Z - 1‖ :=
    (le_max_right _ _).trans (scale_le_one_add_defect Z)
  have ht : 0 ≤ ρ.trace.re := Complex.nonneg_iff.mp hρ.trace_nonneg |>.1
  exact hh.trans (mul_le_mul_of_nonneg_right hb ht)

theorem crossScore_le_norms (X Y : Matrix H I ℂ) (ρ : CMatrix (H × Bool)) :
    crossScore X Y ρ ≤ ∑ i : I,
      ‖star (controlVector (fun h => X h i) false) ⬝ᵥ
        (ρ *ᵥ controlVector (fun h => Y h i) true)‖ := by
  apply Finset.sum_le_sum
  intro i hi
  exact Complex.re_le_norm _

/-- Pointwise bound for the actual normalized Gram witness. The diagonal
blocks contribute one half plus their Gram defects; only genuine control
coherences remain in the cross term. -/
theorem switch_witness_acceptance_le (X Y : Matrix H I ℂ)
    (ρ : State (H × Bool)) :
    ((witnessTest (switchColumns X Y)).acceptProb ρ : ℝ) ≤
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * ‖gram X - 1‖ +
        (1 / 2 : ℝ) * ‖gram Y - 1‖ + ∑ i : I,
          ‖star (controlVector (fun h => X h i) false) ⬝ᵥ
            (ρ.matrix *ᵥ controlVector (fun h => Y h i) true)‖ := by
  rw [BinaryHypothesisTest.acceptProb_eq_trace_re]
  change tracePair ρ.matrix (effect (switchColumns X Y)) ≤ _
  have he := tracePair_mono_right ρ.pos (effect_le_frame (switchColumns X Y))
  rw [switch_frame_score X Y ρ.matrix ρ.pos.isHermitian] at he
  have hx := frame_pair_le_one_add_defect X (block ρ.matrix false)
    (block_pos ρ.matrix ρ.pos false)
  have hy := frame_pair_le_one_add_defect Y (block ρ.matrix true)
    (block_pos ρ.matrix ρ.pos true)
  have hp := block_mass_sum ρ.matrix
  rw [ρ.trace_eq_one] at hp
  simp only [Complex.one_re] at hp
  have hp0 := block_mass_nonneg ρ.matrix ρ.pos false
  have hp1 := block_mass_nonneg ρ.matrix ρ.pos true
  have hp0le : (block ρ.matrix false).trace.re ≤ 1 := by linarith
  have hp1le : (block ρ.matrix true).trace.re ≤ 1 := by linarith
  have hd0 := mul_le_mul_of_nonneg_left hp0le (norm_nonneg (gram X - 1))
  have hd1 := mul_le_mul_of_nonneg_left hp1le (norm_nonneg (gram Y - 1))
  have hc := crossScore_le_norms X Y ρ.matrix
  nlinarith

#print axioms switch_witness_acceptance_le

theorem switchCoefficient_star : star switchCoefficient = switchCoefficient := by
  simp [switchCoefficient]

theorem switchCoefficient_pair (x y : ℂ) :
    star (switchCoefficient * x) * (switchCoefficient * y) =
      (1 / 2 : ℂ) * (star x * y) := by
  rw [star_mul, switchCoefficient_star]
  calc
    _ = (switchCoefficient * switchCoefficient) * (star x * y) := by ring
    _ = _ := by rw [switchCoefficient_square]

theorem gram_switchColumns (X Y : Matrix H I ℂ) :
    gram (switchColumns X Y) = (1 / 2 : ℂ) • (gram X + gram Y) := by
  ext i j
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, switchColumns]
  simp only [Bool.false_eq_true, if_false, if_true,
    switchCoefficient_pair, Fintype.sum_bool]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  ring

theorem switch_gram_diag_one (X Y : Matrix H I ℂ)
    (hX : ∀ i, gram X i i = 1) (hY : ∀ i, gram Y i i = 1) :
    ∀ i, gram (switchColumns X Y) i i = 1 := by
  intro i
  rw [gram_switchColumns]
  simp [hX, hY]
  norm_num

theorem switch_gram_defect_le (X Y : Matrix H I ℂ) :
    ‖gram (switchColumns X Y) - 1‖ ≤
      (1 / 2 : ℝ) * ‖gram X - 1‖ + (1 / 2 : ℝ) * ‖gram Y - 1‖ := by
  have he : gram (switchColumns X Y) - 1 =
      (1 / 2 : ℂ) • (gram X - 1) + (1 / 2 : ℂ) • (gram Y - 1) := by
    rw [gram_switchColumns]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  rw [he]
  have hh := norm_add_le ((1 / 2 : ℂ) • (gram X - 1)) ((1 / 2 : ℂ) • (gram Y - 1))
  norm_num [norm_smul] at hh
  exact hh

#print axioms gram_switchColumns
#print axioms switch_gram_defect_le
end
end ICO.GramWitness
