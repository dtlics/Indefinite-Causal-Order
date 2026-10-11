import ICO.TwoQueryTree

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.TwoQueryTree

namespace ICO.UniformQueryMixture
set_option maxHeartbeats 300000
noncomputable section
universe u
variable {P H O J : Type u} [Fintype P] [Fintype H] [Fintype O] [Fintype J]
  [DecidableEq P] [DecidableEq H] [DecidableEq O] [DecidableEq J]

theorem sqrt_mul (w : ℝ) (hw : 0≤w) :
    (Real.sqrt w : ℂ)*(Real.sqrt w : ℂ) = (w : ℂ) := by
  exact_mod_cast Real.mul_self_sqrt hw

def choiceInstrument (w : J → ℝ) (hw : ∀ j, 0≤w j) (hs : ∑ j,w j=1) :
    Instrument P P J where
  op j := (Real.sqrt (w j) : ℂ) • (1 : CMatrix P)
  complete := by
    simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_one,Matrix.smul_mul,
      Matrix.mul_smul,Matrix.one_mul,smul_smul,Complex.star_def,Complex.conj_ofReal]
    simp_rw [sqrt_mul _ (hw _)]
    rw [← Finset.sum_smul,← Complex.ofReal_sum,hs]
    simp

theorem choice_sandwich (w : J → ℝ) (hw : ∀ j, 0≤w j) (hs : ∑ j,w j=1)
    (j : J) (X : CMatrix P) :
    (choiceInstrument (P:=P) w hw hs).op j * X * ((choiceInstrument (P:=P) w hw hs).op j)ᴴ =
      (w j : ℂ) • X := by
  simp only [choiceInstrument,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul,
    Complex.star_def,Complex.conj_ofReal,sqrt_mul _ (hw _)]

def mixture (w : J → ℝ) (hw : ∀ j,0≤w j) (hs : ∑ j,w j=1)
    (trees : J → QueryTree H O P) : QueryTree H O P :=
  .node (choiceInstrument w hw hs) trees

theorem mixture_apply (w : J → ℝ) (hw : ∀ j,0≤w j) (hs : ∑ j,w j=1)
    (trees : J → QueryTree H O P) (U V : Channel H H) (X : CMatrix P) :
    ((mixture w hw hs trees).channel U V).map X =
      ∑ j, (w j : ℂ) • (((trees j).channel U V).map X) := by
  change (adaptiveChannel (choiceInstrument w hw hs) (fun j => (trees j).channel U V)).map X = _
  rw [ICO.OneQueryTree.adaptiveChannel_apply]
  simp_rw [choice_sandwich,map_smul]

def uniformWeights (J : Type u) [Fintype J] : J → ℝ := fun _ => 1/(Fintype.card J : ℝ)

theorem uniform_nonneg (j : J) : 0≤uniformWeights J j := by unfold uniformWeights; positivity

theorem uniform_sum [Nonempty J] : (∑ j : J,uniformWeights J j)=1 := by
  have hn : (Fintype.card J : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uniformWeights,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

def uniformMixture [Nonempty J] (trees : J → QueryTree H O P) : QueryTree H O P :=
  mixture (uniformWeights J) uniform_nonneg uniform_sum trees

theorem uniformMixture_choi [Nonempty J] (trees : J → QueryTree H O P) (U V : Channel H H) :
    MatrixMap.choi (((uniformMixture trees).channel U V).map) =
      (1/(Fintype.card J : ℝ)) • ∑ j, MatrixMap.choi (((trees j).channel U V).map) := by
  ext x y
  simp only [MatrixMap.choi,uniformMixture,mixture_apply,uniformWeights,
    Matrix.sum_apply,Matrix.smul_apply,Finset.mul_sum]
  simp [Complex.real_smul,Finset.mul_sum]

#print axioms uniformMixture_choi
end
end ICO.UniformQueryMixture
