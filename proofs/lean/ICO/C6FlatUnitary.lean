import ICO.LudersPromise

/-! Explicit mutually unbiased witnesses in every qubit dimension.  The proof
constructs tensor powers of the normalized two-dimensional Walsh matrix. -/
namespace ICO.C6FlatUnitary
open Matrix QIT ICO.SwitchObservable ICO.LudersPromise
open scoped BigOperators ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 1000000
set_option Elab.async false

def walsh2 : CMatrix (Fin 2) :=
  (Real.sqrt 2 : ℂ)⁻¹ • !![1, 1; 1, -1]

theorem sqrt_two_mul : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  norm_cast
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem walsh2_isometry : walsh2.conjTranspose * walsh2 = 1 := by
  have hb : (!![1, 1; 1, -1] : CMatrix (Fin 2)).conjTranspose *
      !![1, 1; 1, -1] = (2 : ℂ) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply]
  have hs : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, sqrt_two_mul]
  have hstar : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    simp
  simp only [walsh2, Matrix.conjTranspose_smul, map_inv₀, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hstar, hs, hb]
  change ((Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ * 2)) •
    (1 : CMatrix (Fin 2)) = 1
  rw [← mul_assoc, hs]
  norm_num

theorem walsh2_normSq (i j : Fin 2) : Complex.normSq (walsh2 i j) = 1/2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  fin_cases i <;> fin_cases j <;>
    simp [walsh2, Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_ofReal, hs]

theorem flat_fin (n : ℕ) :
    ∃ H : Matrix.unitaryGroup (Fin (2^n)) ℂ,
      ∀ i j, Complex.normSq ((H : CMatrix (Fin (2^n))) i j) = 1/(2^n : ℝ) := by
  induction n with
  | zero =>
      simp only [pow_zero, div_one]
      refine ⟨1, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num
  | succ n ih =>
      obtain ⟨H,hH⟩ := ih
      let e : Fin (2^(n+1)) ≃ Fin 2 × Fin (2^n) :=
        Fintype.equivOfCardEq (by simp [pow_succ, Nat.mul_comm])
      let W := (Matrix.kronecker walsh2 (H : CMatrix (Fin (2^n)))).submatrix e e
      have hk := Matrix.kronecker_mem_unitary
        (Matrix.mem_unitaryGroup_iff'.mpr walsh2_isometry) H.property
      have hk' : (Matrix.kronecker walsh2 (H : CMatrix (Fin (2^n)))).conjTranspose *
        Matrix.kronecker walsh2 (H : CMatrix (Fin (2^n))) = 1 := hk.1
      have hW : W.conjTranspose * W = 1 := by
        dsimp only [W]
        rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
          hk', Matrix.submatrix_one_equiv]
      refine ⟨⟨W, Matrix.mem_unitaryGroup_iff'.mpr hW⟩, ?_⟩
      intro i j
      change Complex.normSq (walsh2 (e i).1 (e j).1 *
        (H : CMatrix (Fin (2^n))) (e i).2 (e j).2) = _
      rw [Complex.normSq_mul, walsh2_normSq, hH]
      simp [pow_succ, div_eq_mul_inv, mul_comm]

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem flat_unitary (n : ℕ) (hd : Fintype.card A = 2^n) :
    ∃ H : Matrix.unitaryGroup A ℂ,
      ∀ i j, Complex.normSq ((H : CMatrix A) i j) = 1/(Fintype.card A : ℝ) := by
  obtain ⟨H,hH⟩ := flat_fin n
  let e : A ≃ Fin (2^n) := Fintype.equivOfCardEq (by simpa using hd)
  let W := (H : CMatrix (Fin (2^n))).submatrix e e
  have hH' : (H : CMatrix (Fin (2^n))).conjTranspose * (H : CMatrix (Fin (2^n))) = 1 :=
    H.property.1
  have hW : W.conjTranspose * W = 1 := by
    dsimp only [W]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      hH', Matrix.submatrix_one_equiv]
  refine ⟨⟨W, Matrix.mem_unitaryGroup_iff'.mpr hW⟩, ?_⟩
  intro i j
  change Complex.normSq ((H : CMatrix (Fin (2^n))) (e i) (e j)) = _
  simpa [hd] using hH (e i) (e j)

#print axioms flat_unitary
end
end ICO.C6FlatUnitary
