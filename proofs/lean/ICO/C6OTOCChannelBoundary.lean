import ICO.C6SwitchTest

/-! Both sides of SAME-versus-MUB have commuting channel superoperators.
The switch observable therefore tests a finer operator-algebra relation. -/
namespace ICO.C6OTOCChannelBoundary
open Matrix QIT ICO.SwitchObservable ICO.C6SwitchTest
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem single_sandwich (Y : CMatrix A) (i : A) :
    Matrix.single i i 1 * Y * Matrix.single i i 1 =
      Y i i • Matrix.single i i 1 := by
  ext a b
  by_cases ha : i=a <;> by_cases hb : i=b <;>
    simp [Matrix.mul_apply, Matrix.single, Matrix.smul_apply, ite_and, ha, hb]

theorem dephasing_expansion (U X : CMatrix A) :
    MatrixMap.ofKraus (basisProjection U) X =
      ∑ i, (Uᴴ*X*U) i i • basisProjection U i := by
  change (∑ i, basisProjection U i * X * (basisProjection U i)ᴴ) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [basisProjection_hermitian]
  calc
    _ = U * (Matrix.single i i 1 * (Uᴴ*X*U) * Matrix.single i i 1) * Uᴴ := by
      simp only [basisProjection, Matrix.mul_assoc]
    _ = _ := by rw [single_sandwich]; simp only [Matrix.mul_smul, Matrix.smul_mul, basisProjection]

theorem projection_overlap_entry (U V : CMatrix A) (i j : A) :
    (Uᴴ*basisProjection V j*U) i i =
      (Complex.normSq ((Uᴴ*V) i j) : ℂ) := by
  have hm : Uᴴ*basisProjection V j*U =
      (Uᴴ*V)*Matrix.single j j 1*(Uᴴ*V)ᴴ := by
    simp only [basisProjection, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hm]
  simp [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply,
    ite_and, Complex.normSq_eq_conj_mul_self, mul_comm]

theorem mub_erases_basis (U V : Matrix.unitaryGroup A ℂ)
    (h : MutuallyUnbiased U V) (j : A) :
    MatrixMap.ofKraus (basisProjection (U : CMatrix A)) (basisProjection V j) =
      (Fintype.card A : ℂ)⁻¹ • (1 : CMatrix A) := by
  rw [dephasing_expansion]
  dsimp only [MutuallyUnbiased] at h
  simp only [projection_overlap_entry, h, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast, one_div]
  rw [← Finset.smul_sum, basisProjection_complete _ U.property.2]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]

theorem mub_composition (U V : Matrix.unitaryGroup A ℂ)
    (h : MutuallyUnbiased U V) (X : CMatrix A) :
    MatrixMap.ofKraus (basisProjection (U : CMatrix A))
      (MatrixMap.ofKraus (basisProjection (V : CMatrix A)) X) =
        ((Fintype.card A : ℂ)⁻¹ * X.trace) • (1 : CMatrix A) := by
  rw [dephasing_expansion (V : CMatrix A)]
  simp only [map_sum, map_smul, mub_erases_basis U V h, smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_mul]
  have ht : (∑ i, ((V : CMatrix A)ᴴ*X*V) i i) = X.trace := by
    change ((V : CMatrix A)ᴴ*X*V).trace = X.trace
    have hv : (V : CMatrix A)*(V : CMatrix A)ᴴ=1 := V.property.2
    rw [Matrix.trace_mul_cycle, hv, Matrix.one_mul]
  rw [ht, mul_comm]

theorem mutuallyUnbiased_symm (U V : Matrix.unitaryGroup A ℂ)
    (h : MutuallyUnbiased U V) : MutuallyUnbiased V U := by
  intro i j
  have ht : ((V : CMatrix A)ᴴ * (U : CMatrix A)) i j = star (((U : CMatrix A)ᴴ * (V : CMatrix A)) j i) := by
    have hh : (V : CMatrix A)ᴴ * (U : CMatrix A) = ((U : CMatrix A)ᴴ * (V : CMatrix A))ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hh]
    rfl
  rw [ht]
  simpa only [Complex.star_def, Complex.normSq_conj] using h j i

theorem mub_channels_commute (U V : Matrix.unitaryGroup A ℂ)
    (h : MutuallyUnbiased U V) (X : CMatrix A) :
    MatrixMap.ofKraus (basisProjection (U : CMatrix A))
      (MatrixMap.ofKraus (basisProjection (V : CMatrix A)) X) =
    MatrixMap.ofKraus (basisProjection (V : CMatrix A))
      (MatrixMap.ofKraus (basisProjection (U : CMatrix A)) X) := by
  rw [mub_composition U V h, mub_composition V U (mutuallyUnbiased_symm U V h)]

theorem same_channels_commute (U V : Matrix.unitaryGroup A ℂ)
    (h : MatrixMap.ofKraus (basisProjection (U : CMatrix A)) =
      MatrixMap.ofKraus (basisProjection (V : CMatrix A))) (X : CMatrix A) :
    MatrixMap.ofKraus (basisProjection (U : CMatrix A))
      (MatrixMap.ofKraus (basisProjection (V : CMatrix A)) X) =
    MatrixMap.ofKraus (basisProjection (V : CMatrix A))
      (MatrixMap.ofKraus (basisProjection (U : CMatrix A)) X) := by rw [h]

#print axioms mub_composition
#print axioms mub_channels_commute
end
end ICO.C6OTOCChannelBoundary
