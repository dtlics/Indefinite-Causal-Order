import ICO.LudersPromise

/-! A genuine low-promise pair of hidden-outcome rank-one measurements in
every dimension at least four. Dimension four uses a literal rational Walsh
matrix; in larger dimensions the minimum is at most the checked Haar mean. -/
namespace ICO.LudersLowWitness
open Matrix QIT MeasureTheory ICO.SwitchObservable ICO.LudersPromise
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false

def walsh4 : CMatrix (Fin 4) :=
  !![1/2, 1/2, 1/2, 1/2;
     1/2, -(1/2), 1/2, -(1/2);
     1/2, 1/2, -(1/2), -(1/2);
     1/2, -(1/2), -(1/2), 1/2]

theorem walsh4_isometry : walsh4.conjTranspose * walsh4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [walsh4, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.one_apply, map_ofNat]

theorem walsh4_normSq (i j : Fin 4) : Complex.normSq (walsh4 i j) = 1/4 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [walsh4, Complex.normSq_apply, Complex.mul_re]

variable {A : Type*} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem low_pair_card_four (hd : Fintype.card A = 4) :
    ∃ U V : Matrix.unitaryGroup A ℂ,
      interference (basisProjection (U : CMatrix A))
        (basisProjection (V : CMatrix A)) ≤ 1/3 := by
  let e : A ≃ Fin 4 := Fintype.equivOfCardEq (by simpa using hd)
  let W : CMatrix A := walsh4.submatrix e e
  have hW : W.conjTranspose * W = 1 := by
    change (walsh4.submatrix e e).conjTranspose * walsh4.submatrix e e = 1
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      walsh4_isometry, Matrix.submatrix_one_equiv]
  let V : Matrix.unitaryGroup A ℂ := ⟨W, Matrix.mem_unitaryGroup_iff'.mpr hW⟩
  refine ⟨1,V,?_⟩
  rw [basis_interference]
  have he (i j : A) :
      Complex.normSq ((((1 : Matrix.unitaryGroup A ℂ) : CMatrix A).conjTranspose *
        (V : CMatrix A)) i j) ^ 2 = 1/16 := by
    change Complex.normSq (((1 : CMatrix A).conjTranspose * W) i j) ^ 2 = 1/16
    simp only [Matrix.conjTranspose_one, Matrix.one_mul]
    change Complex.normSq (walsh4 (e i) (e j)) ^ 2 = 1/16
    rw [walsh4_normSq]
    norm_num
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hd]
  norm_num

theorem low_pair_card_ge_five (hd : 5 ≤ Fintype.card A) :
    ∃ U V : Matrix.unitaryGroup A ℂ,
      interference (basisProjection (U : CMatrix A))
        (basisProjection (V : CMatrix A)) ≤ 1/3 := by
  let f : Matrix.unitaryGroup A ℂ → ℝ := fun V =>
    interference (basisProjection ((1 : Matrix.unitaryGroup A ℂ) : CMatrix A))
      (basisProjection (V : CMatrix A))
  have hg : Continuous (fun V : Matrix.unitaryGroup A ℂ =>
      ((1 : Matrix.unitaryGroup A ℂ),V)) := continuous_const.prodMk continuous_id
  have hc₀ := (basis_interference_continuous (A := A)).comp hg
  have hc : Continuous f := by
    simpa only [Function.comp_def, f] using hc₀
  obtain ⟨V, _, hV⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := unitaryHaarMeasure (a := A))
  have hb := integral_mono (integrable_const (f V)) hi (fun W => hV (Set.mem_univ W))
  have hm : (∫ W, f W ∂unitaryHaarMeasure (a := A)) =
      2 / ((Fintype.card A : ℝ)+1) := fixed_basis_interference_average 1
  rw [integral_const, probReal_univ, one_smul, hm] at hb
  refine ⟨1,V,hb.trans ?_⟩
  have hdim : (5 : ℝ) ≤ Fintype.card A := by exact_mod_cast hd
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card A + 1)).mpr
  linarith

theorem low_pair (hd : 4 ≤ Fintype.card A) :
    ∃ U V : Matrix.unitaryGroup A ℂ,
      interference (basisProjection (U : CMatrix A))
        (basisProjection (V : CMatrix A)) ≤ 1/3 := by
  by_cases h4 : Fintype.card A = 4
  · exact low_pair_card_four h4
  · exact low_pair_card_ge_five (by omega)

#print axioms low_pair
end
end ICO.LudersLowWitness
