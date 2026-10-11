import ICO.ChoiWitnessState
import ICO.SwitchObservable

/-! Actual plus-control switched Kraus operators for uniform unitary
mixtures. Their normalized Choi state is the switch Gram witness's ideal state. -/
namespace ICO.SwitchChoiWitness
open Matrix QIT ICO.GramWitness ICO.CompositionGram ICO.CircuitOutput
open ICO.ChoiWitnessState ICO.TreeCoherence
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def pairRows (T S : CMatrix A) : Matrix (A × Bool) A ℂ :=
  fun ab x => switchCoefficient *
    if ab.2 then S ab.1 x else T ab.1 x

theorem pairRows_gram (T S : CMatrix A) :
    (pairRows T S).conjTranspose * pairRows T S =
      (1/2 : ℂ) • (T.conjTranspose*T) + (1/2 : ℂ) • (S.conjTranspose*S) := by
  have hc : star switchCoefficient = switchCoefficient := by simp [switchCoefficient]
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pairRows,
    Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
    if_false, if_true, star_mul, hc, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  linear_combination (star (T a x)*T a y + star (S a x)*S a y)*switchCoefficient_square

def pairKraus (U V : Matrix.unitaryGroup A ℂ) : Matrix (A × Bool) A ℂ :=
  pairRows ((V : CMatrix A)*(U : CMatrix A)) ((U : CMatrix A)*(V : CMatrix A))

theorem pairKraus_complete (U V : Matrix.unitaryGroup A ℂ) :
    (pairKraus U V).conjTranspose * pairKraus U V = 1 := by
  rw [pairKraus, pairRows_gram]
  have hVU := Matrix.UnitaryGroup.star_mul_self (V*U)
  have hUV := Matrix.UnitaryGroup.star_mul_self (U*V)
  change (((V : CMatrix A)*(U : CMatrix A)).conjTranspose) *
    ((V : CMatrix A)*(U : CMatrix A)) = 1 at hVU
  change (((U : CMatrix A)*(V : CMatrix A)).conjTranspose) *
    ((U : CMatrix A)*(V : CMatrix A)) = 1 at hUV
  rw [hVU, hUV, ← add_smul]
  norm_num

def uniformCoefficient (r s : ℕ) : ℂ :=
  (((Real.sqrt ((r : ℝ)*(s : ℝ)))⁻¹ : ℝ) : ℂ)

theorem uniformCoefficient_star (r s : ℕ) :
    star (uniformCoefficient r s) = uniformCoefficient r s := by simp [uniformCoefficient]

theorem uniformCoefficient_square (r s : ℕ) :
    uniformCoefficient r s * uniformCoefficient r s = ((r : ℂ)*(s : ℂ))⁻¹ := by
  have hs := Real.sq_sqrt (show 0 ≤ (r : ℝ)*(s : ℝ) by positivity)
  have he : (Real.sqrt ((r : ℝ)*(s : ℝ)))⁻¹ *
      (Real.sqrt ((r : ℝ)*(s : ℝ)))⁻¹ = ((r : ℝ)*(s : ℝ))⁻¹ := by
    rw [← mul_inv, ← pow_two, hs]
  simp only [uniformCoefficient, ← Complex.ofReal_mul, he]
  simp

def mixtureKraus {r s : ℕ} (U : Fin r → Matrix.unitaryGroup A ℂ)
    (V : Fin s → Matrix.unitaryGroup A ℂ) (ij : Fin r × Fin s) :
    Matrix (A × Bool) A ℂ := uniformCoefficient r s • pairKraus (U ij.1) (V ij.2)

theorem mixtureKraus_complete {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (U : Fin r → Matrix.unitaryGroup A ℂ) (V : Fin s → Matrix.unitaryGroup A ℂ) :
    (∑ ij : Fin r × Fin s, (mixtureKraus U V ij).conjTranspose * mixtureKraus U V ij) = 1 := by
  have hentry (ij : Fin r × Fin s) :
      (mixtureKraus U V ij).conjTranspose * mixtureKraus U V ij =
        ((r : ℂ)*(s : ℂ))⁻¹ • (1 : CMatrix A) := by
    simp only [mixtureKraus, Matrix.conjTranspose_smul, uniformCoefficient_star,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, uniformCoefficient_square,
      pairKraus_complete]
  simp_rw [hentry]
  rw [← Finset.sum_smul, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  simp [hr', hs', Nat.cast_mul]
  have hc : (r : ℂ)*(s : ℂ)*((s : ℂ)⁻¹*(r : ℂ)⁻¹) = 1 := by
    field_simp
  rw [hc, one_smul]

def mixtureSwitchChannel {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (U : Fin r → Matrix.unitaryGroup A ℂ) (V : Fin s → Matrix.unitaryGroup A ℂ) :
    Channel A (A × Bool) where
  map := MatrixMap.ofKraus (mixtureKraus U V)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
    (by simpa [MatrixMap.krausAdjoint] using mixtureKraus_complete hr hs U V)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

#print axioms pairKraus_complete
#print axioms mixtureSwitchChannel

theorem normalized_kraus_column {r s : ℕ}
    (U : Fin r → Matrix.unitaryGroup A ℂ) (V : Fin s → Matrix.unitaryGroup A ℂ)
    (ij : Fin r × Fin s) (p : (A × A) × Bool) :
    coefficient (A := A) * mixtureKraus U V ij (p.1.2,p.2) p.1.1 =
      uniformCoefficient r s * switchColumns (columns U V)
        (ICO.ReverseCompositionGram.reverseColumns U V) p ij := by
  rcases p with ⟨⟨x,y⟩,b⟩
  cases b <;>
    simp [mixtureKraus, pairKraus, pairRows, switchColumns, columns,
      ICO.ReverseCompositionGram.reverseColumns, targetVector, smul_eq_mul] <;> ring

theorem normalizedChoi_matrix_eq {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (U : Fin r → Matrix.unitaryGroup A ℂ) (V : Fin s → Matrix.unitaryGroup A ℂ) :
    (normalizedChoiState (mixtureSwitchChannel hr hs U V)).matrix =
      (((Fintype.card (Fin r × Fin s) : ℝ)⁻¹ : ℝ) : ℂ) •
        frame (switchColumns (columns U V) (ICO.ReverseCompositionGram.reverseColumns U V)) := by
  ext p q
  simp only [normalizedChoiState, mixtureSwitchChannel, groupedMapChoi,
    MatrixMap.choi_ofKraus, Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply, frame, Matrix.mul_apply,
    Matrix.conjTranspose_apply, smul_eq_mul]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Complex.ofReal_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← coefficient_square (A := A)]
  have hp := normalized_kraus_column U V ij p
  have hq := congrArg star (normalized_kraus_column U V ij q)
  simp only [star_mul, coefficient_star, uniformCoefficient_star] at hq
  calc
    _ = (coefficient (A := A) * mixtureKraus U V ij (p.1.2,p.2) p.1.1) *
        (star (mixtureKraus U V ij (q.1.2,q.2) q.1.1) * coefficient (A := A)) := by ring
    _ = _ := by rw [hp, hq]; rw [← uniformCoefficient_square]; ring

theorem normalizedChoi_eq_ideal {r s : ℕ}
    (U : Fin (r+1) → Matrix.unitaryGroup A ℂ)
    (V : Fin (s+1) → Matrix.unitaryGroup A ℂ) :
    normalizedChoiState (mixtureSwitchChannel (Nat.zero_lt_succ r) (Nat.zero_lt_succ s) U V) =
      idealState (switchColumns (columns U V) (ICO.ReverseCompositionGram.reverseColumns U V))
        (switch_gram_diag_one _ _ (gram_diagonal U V)
          (ICO.ReverseCompositionGram.reverse_gram_diagonal U V)) := by
  apply State.ext
  exact normalizedChoi_matrix_eq _ _ U V

#print axioms normalizedChoi_eq_ideal
end
end ICO.SwitchChoiWitness
