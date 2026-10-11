import ICO.MHHaarPurifiedMixture

/-! The literal uniform phase/permutation purification is continuous and
preserves the average squared norm of the physical responses. -/
namespace ICO.MHPurifiedResponseNorm
open Matrix QIT MeasureTheory ICO.MHHaarPurifiedMixture ICO.MHPhasePermutation
  ICO.MHTernaryCompression
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1600000
variable {A H : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype H] [DecidableEq H]

theorem uniformAmplitude_norm_sq : ‖uniformAmplitude (A := A)‖^2=
    (Fintype.card (Environment A) : ℝ)⁻¹ := by
  have hh := congrArg Complex.re (uniformAmplitude_square (A := A))
  rw [Complex.sq_norm]
  rw [← Complex.ofReal_re (Complex.normSq (uniformAmplitude (A := A)))]
  rw [Complex.normSq_eq_conj_mul_self]
  simpa only [← Complex.ofReal_natCast,← Complex.ofReal_inv,Complex.ofReal_re] using hh

theorem purifiedResponse_continuous
    (f : Matrix.unitaryGroup A ℂ → EuclideanSpace ℂ H) (hf : Continuous f) :
    Continuous (fun p : Matrix.unitaryGroup A ℂ × Matrix.unitaryGroup A ℂ =>
      purifiedResponse f p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro o
  exact continuous_const.mul (((PiLp.continuous_apply 2 (fun _ : H => ℂ) o.1).comp hf).comp
    ((continuous_snd.mul continuous_const).mul continuous_fst))

theorem purifiedResponse_norm_sq
    (f : Matrix.unitaryGroup A ℂ → EuclideanSpace ℂ H) (C D : Matrix.unitaryGroup A ℂ) :
    ‖purifiedResponse f C D‖^2=(Fintype.card (Environment A) : ℝ)⁻¹*
      ∑ e : Environment A, ‖f (D*phaseOracleUnitary e*C)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ o : H×Environment A, ‖uniformAmplitude (A := A)*f (D*phaseOracleUnitary o.2*C) o.1‖^2)=_
  rw [Fintype.sum_prod_type]
  simp only [norm_mul,mul_pow]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,uniformAmplitude_norm_sq]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact (PiLp.norm_sq_eq_of_L2 (fun _ : H => ℂ) (f (D*phaseOracleUnitary e*C))).symm

theorem purifiedResponse_norm_le
    (f : Matrix.unitaryGroup A ℂ → EuclideanSpace ℂ H) (hf : ∀ U, ‖f U‖≤1)
    (C D : Matrix.unitaryGroup A ℂ) : ‖purifiedResponse f C D‖≤1 := by
  have hh : ‖purifiedResponse f C D‖^2≤1 := by
    rw [purifiedResponse_norm_sq]
    calc
      _ ≤ (Fintype.card (Environment A) : ℝ)⁻¹*∑ _e : Environment A, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro e _
        exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hf _) |>.trans (by norm_num)
      _ = 1 := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
        exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := Environment A))
  nlinarith [norm_nonneg (purifiedResponse f C D)]

theorem purifiedResponse_norm_one
    (f : Matrix.unitaryGroup A ℂ → EuclideanSpace ℂ H) (hf : ∀ U, ‖f U‖=1)
    (C D : Matrix.unitaryGroup A ℂ) : ‖purifiedResponse f C D‖=1 := by
  have hh : ‖purifiedResponse f C D‖^2=1 := by
    rw [purifiedResponse_norm_sq]
    simp only [hf,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := Environment A))
  nlinarith [norm_nonneg (purifiedResponse f C D)]

#print axioms purifiedResponse_norm_one
#print axioms purifiedResponse_continuous
end
end ICO.MHPurifiedResponseNorm