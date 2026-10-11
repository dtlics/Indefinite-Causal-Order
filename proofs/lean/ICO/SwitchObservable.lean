import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
The switch interference observable as actual finite-dimensional matrix algebra.
Unlike the scalar lower-bound consequences, this module proves identities for
the Kraus operators themselves. Statistical and arbitrary-query lower bounds
are separate obligations.
-/

namespace ICO.SwitchObservable

open Matrix

variable {n ι κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [Fintype κ]

noncomputable def rawInterference
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ) : ℂ :=
  ∑ i, ∑ j, Matrix.trace (B j * A i * (B j)ᴴ * (A i)ᴴ)

/-- One switched Kraus operator, with the two control states indexed by `Sum`. -/
noncomputable def switchKraus (A B : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks (B * A) 0 0 (A * B)

/-- Input control fixed to plus; the target input is the arbitrary matrix `ρ`. -/
noncomputable def plusTarget (ρ : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks ((1 / 2 : ℂ) • ρ) ((1 / 2 : ℂ) • ρ)
    ((1 / 2 : ℂ) • ρ) ((1 / 2 : ℂ) • ρ)

omit [DecidableEq n] in
theorem switch_one_kraus_control_block (A B ρ : Matrix n n ℂ) :
    Matrix.toBlocks₁₂ (switchKraus A B * plusTarget ρ * (switchKraus A B)ᴴ) =
      (1 / 2 : ℂ) • (B * A * ρ * Bᴴ * Aᴴ) := by
  simp only [switchKraus, plusTarget, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.conjTranspose_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_zero, Matrix.mul_assoc]

/-- A complete orthogonal projection family gives interference equal to `dim`. -/
theorem projection_family_raw_interference [DecidableEq ι]
    (P : ι → Matrix n n ℂ)
    (hstar : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hcomplete : ∑ i, P i = 1) :
    rawInterference P P = (Fintype.card n : ℂ) := by
  have hterm (i j : ι) :
      Matrix.trace (P j * P i * (P j)ᴴ * (P i)ᴴ) =
      if i = j then Matrix.trace (P i) else 0 := by
    by_cases h : i = j
    · subst j
      simp [hstar, hmul]
    · have hji : j ≠ i := Ne.symm h
      simp [hstar, hmul, h, hji]
  have htr : (∑ i, Matrix.trace (P i)) = (Fintype.card n : ℂ) := by
    rw [← Matrix.trace_sum, hcomplete]
    simp
  simpa [rawInterference, hterm] using htr

noncomputable def basisProjection (U : Matrix n n ℂ) (i : n) : Matrix n n ℂ :=
  U * Matrix.single i i 1 * Uᴴ

theorem sum_diagonal_matrix_units :
    (∑ i : n, Matrix.single i i (1 : ℂ)) = (1 : Matrix n n ℂ) := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [Matrix.sum_apply, Matrix.single, Matrix.one_apply]
  · have hh : ∀ x : n, ¬(x = a ∧ x = b) := by
      intro x hx
      exact h (hx.1.symm.trans hx.2)
    simp [Matrix.sum_apply, Matrix.single, Matrix.one_apply, h, hh]

theorem basisProjection_hermitian (U : Matrix n n ℂ) (i : n) :
    (basisProjection U i)ᴴ = basisProjection U i := by
  simp [basisProjection, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem basisProjection_mul (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (i j : n) :
    basisProjection U i * basisProjection U j =
      if i = j then basisProjection U i else 0 := by
  have hreduce : basisProjection U i * basisProjection U j =
      U * (Matrix.single i i 1 * Matrix.single j j 1) * Uᴴ := by
    unfold basisProjection
    calc
      _ = U * Matrix.single i i 1 * (Uᴴ * U) *
          Matrix.single j j 1 * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]; simp [Matrix.mul_assoc]
  rw [hreduce]
  by_cases h : i = j
  · subst j
    simp [Matrix.single_mul_single_same, basisProjection]
  · have hz : Matrix.single i i (1 : ℂ) *
        Matrix.single j j 1 = 0 :=
      Matrix.single_mul_single_of_ne (1 : ℂ) i i j h 1
    simp [hz, h]

theorem basisProjection_complete (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) :
    (∑ i, basisProjection U i) = 1 := by
  simp only [basisProjection, ← Matrix.sum_mul, ← Matrix.mul_sum]
  rw [sum_diagonal_matrix_units, Matrix.mul_one, hU]

theorem hidden_basis_high_raw (U : Matrix n n ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    rawInterference (basisProjection U) (basisProjection U) =
      (Fintype.card n : ℂ) :=
  projection_family_raw_interference (basisProjection U)
    (basisProjection_hermitian U) (basisProjection_mul U hleft)
    (basisProjection_complete U hright)

noncomputable def interference
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ) : ℝ :=
  (rawInterference A B).re / Fintype.card n

theorem hidden_basis_high [Nonempty n] (U : Matrix n n ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    interference (basisProjection U) (basisProjection U) = 1 := by
  unfold interference
  rw [hidden_basis_high_raw U hleft hright]
  simp

theorem hidden_basis_kraus_complete (U : Matrix n n ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    (∑ i, (basisProjection U i)ᴴ * basisProjection U i) = 1 := by
  simpa only [basisProjection_hermitian, basisProjection_mul U hleft, if_pos rfl]
    using basisProjection_complete U hright

omit [Fintype n] [DecidableEq n] in
theorem fromBlocks_sum
    (F G H J : ι → Matrix n n ℂ) :
    (∑ i, Matrix.fromBlocks (F i) (G i) (H i) (J i)) =
      Matrix.fromBlocks (∑ i, F i) (∑ i, G i) (∑ i, H i) (∑ i, J i) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.sum_apply, Matrix.fromBlocks]

theorem switch_kraus_complete
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ)
    (hA : ∑ i, (A i)ᴴ * A i = 1)
    (hB : ∑ j, (B j)ᴴ * B j = 1) :
    (∑ i, ∑ j, (switchKraus (A i) (B j))ᴴ * switchKraus (A i) (B j)) = 1 := by
  have hAB (i : ι) : (∑ j, (B j * A i)ᴴ * (B j * A i)) = (A i)ᴴ * A i := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_sum]
    simp only [← Matrix.mul_assoc]
    rw [← Matrix.sum_mul, hB]
    simp
  have hBA (j : κ) : (∑ i, (A i * B j)ᴴ * (A i * B j)) = (B j)ᴴ * B j := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_sum]
    simp only [← Matrix.mul_assoc]
    rw [← Matrix.sum_mul, hA]
    simp
  simp only [switchKraus, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [show (∑ i, ∑ j, Matrix.fromBlocks
      ((B j * A i)ᴴ * (B j * A i)) 0 0 ((A i * B j)ᴴ * (A i * B j))) =
      Matrix.fromBlocks (∑ i, ∑ j, (B j * A i)ᴴ * (B j * A i)) 0 0
        (∑ i, ∑ j, (A i * B j)ᴴ * (A i * B j)) by
    simp_rw [fromBlocks_sum]
    simp]
  simp_rw [hAB]
  rw [Finset.sum_comm]
  simp_rw [hBA]
  rw [hA, hB]
  exact Matrix.fromBlocks_one

noncomputable def matrixUnit (a b : n) : Matrix n n ℂ :=
  Matrix.single a b 1

theorem matrixUnit_quartic_trace (a b c e : n) :
    Matrix.trace (matrixUnit c e * matrixUnit a b *
      (matrixUnit c e)ᴴ * (matrixUnit a b)ᴴ) =
      if e = a then (if b = e then (if c = b then 1 else 0) else 0) else 0 := by
  by_cases hea : e = a
  · subst e
    by_cases hba : b = a
    · subst b
      by_cases hca : c = a
      · subst c
        simp [matrixUnit, Matrix.single_mul_single_same]
      · have hz : Matrix.single c c (1 : ℂ) *
            Matrix.single a a 1 = 0 :=
          Matrix.single_mul_single_of_ne (1 : ℂ) c c a hca 1
        simp [matrixUnit, Matrix.single_mul_single_same, hz, hca]
    · have hz : Matrix.single c b (1 : ℂ) *
          Matrix.single a c 1 = 0 :=
        Matrix.single_mul_single_of_ne (1 : ℂ) c b a hba 1
      simp [matrixUnit, Matrix.single_mul_single_same, hz, hba]
  · have hz : Matrix.single c e (1 : ℂ) *
        Matrix.single a b 1 = 0 :=
      Matrix.single_mul_single_of_ne (1 : ℂ) c e a hea 1
    simp [matrixUnit, hz, hea]

theorem matrix_units_raw_interference :
    rawInterference (fun p : n × n => matrixUnit p.1 p.2)
      (fun p : n × n => matrixUnit p.1 p.2) = (Fintype.card n : ℂ) := by
  unfold rawInterference
  simp only [Fintype.sum_prod_type, matrixUnit_quartic_trace]
  simp

omit [DecidableEq n] in
theorem rawInterference_scaled
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ) (a b : ℂ) :
    rawInterference (fun i => a • A i) (fun j => b • B j) =
      (b * a * star b * star a) * rawInterference A B := by
  simp only [rawInterference, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

#print axioms switch_one_kraus_control_block
#print axioms projection_family_raw_interference
#print axioms hidden_basis_high_raw
#print axioms hidden_basis_high
#print axioms switch_kraus_complete
#print axioms matrix_units_raw_interference

theorem matrix_units_kraus_sum :
    (∑ p : n × n, (matrixUnit p.1 p.2)ᴴ * matrixUnit p.1 p.2) =
      (Fintype.card n : ℂ) • (1 : Matrix n n ℂ) := by
  simp only [Fintype.sum_prod_type, matrixUnit, Matrix.conjTranspose_single,
    star_one, Matrix.single_mul_single_same, mul_one]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Finset.smul_sum, sum_diagonal_matrix_units]
  exact (Nat.cast_smul_eq_nsmul ℂ (Fintype.card n) (1 : Matrix n n ℂ)).symm

theorem matrix_units_channel (ρ : Matrix n n ℂ) :
    (∑ p : n × n, matrixUnit p.1 p.2 * ρ * (matrixUnit p.1 p.2)ᴴ) =
      Matrix.trace ρ • (1 : Matrix n n ℂ) := by
  ext x y
  simp only [Matrix.sum_apply, Fintype.sum_prod_type,
    Matrix.mul_apply, matrixUnit, Matrix.conjTranspose_single,
    Matrix.single, star_one, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Matrix.trace]
  by_cases hxy : x = y
  · subst y
    simp [ite_and, eq_comm]
  · simp [ite_and, eq_comm, hxy, Ne.symm hxy]

noncomputable def depolarizingKraus (p : n × n) : Matrix n n ℂ :=
  ((Real.sqrt (Fintype.card n : ℝ))⁻¹ : ℂ) • matrixUnit p.1 p.2

theorem depolarizing_low [Nonempty n] :
    interference (depolarizingKraus : n × n → Matrix n n ℂ)
      depolarizingKraus = 1 / (Fintype.card n : ℝ) ^ 2 := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  have hsq := Real.sq_sqrt (le_of_lt hd)
  unfold interference depolarizingKraus
  rw [rawInterference_scaled, matrix_units_raw_interference]
  simp only [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal,
    Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_mul, sub_zero]
  field_simp
  nlinarith

#print axioms matrix_units_channel
#print axioms depolarizing_low

omit [DecidableEq n] in
theorem kraus_sum_scaled (A : ι → Matrix n n ℂ) (a : ℂ) :
    (∑ i, (a • A i)ᴴ * (a • A i)) =
      (star a * a) • (∑ i, (A i)ᴴ * A i) := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Finset.smul_sum, mul_comm]

omit [DecidableEq n] in
theorem channel_sum_scaled (A : ι → Matrix n n ℂ) (a : ℂ) (ρ : Matrix n n ℂ) :
    (∑ i, (a • A i) * ρ * (a • A i)ᴴ) =
      (a * star a) • (∑ i, A i * ρ * (A i)ᴴ) := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Finset.smul_sum]
  congr 1
  ring

omit [DecidableEq n] in
theorem sqrt_inverse_product [Nonempty n] :
    (((Real.sqrt (Fintype.card n : ℝ))⁻¹ : ℂ) *
      star ((Real.sqrt (Fintype.card n : ℝ))⁻¹ : ℂ)) =
      ((Fintype.card n : ℝ)⁻¹ : ℂ) := by
  have hs : Real.sqrt (Fintype.card n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos))
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card n by positivity)
  have hcsq : (Real.sqrt (Fintype.card n : ℝ) : ℂ) ^ 2 =
      ((Fintype.card n : ℝ) : ℂ) := by exact_mod_cast hsq
  rw [star_inv₀]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← pow_two, hcsq]

theorem depolarizing_kraus_complete [Nonempty n] :
    (∑ p : n × n, (depolarizingKraus p)ᴴ * depolarizingKraus p) =
      (1 : Matrix n n ℂ) := by
  unfold depolarizingKraus
  rw [kraus_sum_scaled, mul_comm, sqrt_inverse_product, matrix_units_kraus_sum,
    smul_smul]
  have hd : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card n ≠ 0)
  simp [hd]

theorem depolarizing_channel [Nonempty n] (ρ : Matrix n n ℂ) :
    (∑ p : n × n, depolarizingKraus p * ρ * (depolarizingKraus p)ᴴ) =
      (Matrix.trace ρ / (Fintype.card n : ℂ)) • (1 : Matrix n n ℂ) := by
  unfold depolarizingKraus
  rw [channel_sum_scaled, sqrt_inverse_product, matrix_units_channel, smul_smul]
  simp [div_eq_mul_inv, mul_comm]

#print axioms depolarizing_kraus_complete
#print axioms depolarizing_channel

noncomputable def controlX : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 1 1 0

omit [DecidableEq n] in
theorem trace_fromBlocks (R S T W : Matrix n n ℂ) :
    Matrix.trace (Matrix.fromBlocks R S T W) = Matrix.trace R + Matrix.trace W := by
  simp [Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem controlX_trace_fromBlocks (R S T W : Matrix n n ℂ) :
    Matrix.trace (controlX * Matrix.fromBlocks R S T W) =
      Matrix.trace T + Matrix.trace S := by
  simp [controlX, Matrix.fromBlocks_multiply, trace_fromBlocks]

theorem switch_one_kraus_X_trace (A B ρ : Matrix n n ℂ) :
    Matrix.trace (controlX *
      (switchKraus A B * plusTarget ρ * (switchKraus A B)ᴴ)) =
      (1 / 2 : ℂ) *
        (Matrix.trace (A * B * ρ * Aᴴ * Bᴴ) +
          Matrix.trace (B * A * ρ * Bᴴ * Aᴴ)) := by
  simp only [switchKraus, plusTarget, Matrix.fromBlocks_conjTranspose,
    Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_zero, Matrix.mul_assoc]
  rw [controlX_trace_fromBlocks]
  simp [Matrix.trace_smul, mul_add]

omit [DecidableEq n] in
theorem rawInterference_swap (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ) :
    rawInterference B A = star (rawInterference A B) := by
  unfold rawInterference
  rw [Finset.sum_comm]
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.trace_conjTranspose]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

noncomputable def switchOutput
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  ∑ i, ∑ j, switchKraus (A i) (B j) * plusTarget ρ *
    (switchKraus (A i) (B j))ᴴ

/-- The actual X expectation on the switch output with a maximally mixed
target is the interference statistic. This is the estimator's observable
identity; concentration is a separate theorem. -/
theorem switch_X_mean [Nonempty n]
    (A : ι → Matrix n n ℂ) (B : κ → Matrix n n ℂ) :
    (Matrix.trace (controlX * switchOutput A B
      ((Fintype.card n : ℂ)⁻¹ • (1 : Matrix n n ℂ)))).re =
      interference A B := by
  have hc : ∀ (X Y : Matrix n n ℂ),
      Matrix.trace (X * Y * ((Fintype.card n : ℂ)⁻¹ • (1 : Matrix n n ℂ)) *
        Xᴴ * Yᴴ) = (Fintype.card n : ℂ)⁻¹ * Matrix.trace (X * Y * Xᴴ * Yᴴ) := by
    intro X Y
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_assoc]
  unfold switchOutput
  simp only [Matrix.mul_sum, Matrix.trace_sum, switch_one_kraus_X_trace, hc,
    mul_add, Finset.sum_add_distrib]
  simp only [← mul_assoc, ← Finset.mul_sum]
  rw [show (∑ i, ∑ j, Matrix.trace (A i * B j * (A i)ᴴ * (B j)ᴴ)) =
      rawInterference B A by rw [Finset.sum_comm]; rfl]
  change (((1 / 2 : ℂ) * (Fintype.card n : ℂ)⁻¹) * rawInterference B A +
    ((1 / 2 : ℂ) * (Fintype.card n : ℂ)⁻¹) * rawInterference A B).re = _
  rw [rawInterference_swap]
  simp [interference, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    div_eq_mul_inv]
  ring

#print axioms switch_X_mean

end ICO.SwitchObservable

