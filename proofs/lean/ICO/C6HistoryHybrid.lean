import ICO.C6HistoryControlled
import ICO.C6MatrixLocalHybrid

/-! The history-dependent inverse replacement is controlled by the actual
private outcome history. The support premise is the literal prefix projection,
kept explicit here for the separate physical support induction. -/
namespace ICO.C6HistoryHybrid
open Matrix QIT ICO.C6RetainedHistory ICO.C6HistoryControlled
  ICO.C6PairedTrajectory ICO.C6PolarFock ICO.C6PolarTrajectory
  ICO.C6PolarReplacement ICO.C6MatrixTrajectory ICO.C6MatrixLocalHybrid
  ICO.MHBoundedRecording ICO.MHRectangularAction ICO.MHFockKnownOperation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2300000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

theorem controlled_inverse_error {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (hi:i<Fintype.card A) :
    ‖(Matrix.kronecker (polarOracle h)ᴴ (1:CMatrix (Public (A:=A) μ i))-
        controlled (M:=μ i) (inverseBlock h H i))*
      controlled (M:=μ i) (prefixMask H i T)‖≤freshCost (Fintype.card A) i := by
  rw [←controlled_const,←controlled_sub,controlled_mul]
  exact controlled_bound _ _ (freshCost_nonneg _ _) (inverseBlock_error h ht H i hi)

theorem supported_stage_error {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (i:ℕ) (hi:i<Fintype.card A)
    (v:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ i)) (hv:‖v‖≤1)
    (hs:rectAct (controlled (M:=μ i) (prefixMask H i T)) v=v) :
    ‖rectAct (freshStage h H K i-
      polarStage h (middleStage T H) (publicStage T K) i) v‖≤freshCost (Fintype.card A) i := by
  let L:=publicStage T K i*Matrix.kronecker (polarLeftOnFock h)
    (1:CMatrix (Middle (A:=A) μ i))*middleStage T H i
  let B:=Matrix.kronecker (polarOracle h)ᴴ (1:CMatrix (Public (A:=A) μ i))-
    controlled (M:=μ i) (inverseBlock h H i)
  have hL:‖L‖≤1 := by
    apply ICO.C6FockPairs.mul_norm_le_one
    · apply ICO.C6FockPairs.mul_norm_le_one
      · exact publicStage_norm T K hK i
      · exact (tensor_identity_norm_le _).trans (polarLeftOnFock_norm_le h ht)
    · exact middleStage_norm T H i
  have he:freshStage h H K i-polarStage h (middleStage T H) (publicStage T K) i= -(L*B) := by
    simp only [freshStage,polarStage,polarPair,L,B,Matrix.mul_sub,Matrix.mul_assoc]
    abel
  have hb:‖rectAct B v‖≤freshCost (Fintype.card A) i := by
    have he':rectAct B v=rectAct (B*controlled (M:=μ i) (prefixMask H i T)) v := by
      rw [rectAct_mul,hs]
    rw [he']
    exact (rectAct_norm_le _ _).trans (by
      have hh:=mul_le_mul (controlled_inverse_error (μ:=μ) h ht H i hi) hv
        (norm_nonneg _) (freshCost_nonneg _ _)
      simpa using hh)
  rw [he]
  have hn:rectAct (-(L*B)) v= -rectAct (L*B) v := by
    change WithLp.toLp 2 ((-(L*B))*ᵥWithLp.ofLp v)=_
    rw [Matrix.neg_mulVec]
    rfl
  rw [hn,norm_neg,rectAct_mul]
  exact (rectAct_norm_le _ _).trans (by
    have hh:=mul_le_mul_of_nonneg_right hL (norm_nonneg (rectAct B v))
    have hh':‖L‖*‖rectAct B v‖≤‖rectAct B v‖ := by simpa using hh
    exact hh'.trans hb)

theorem fresh_polar_distance {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0)) (hz:‖z‖≤1)
    (n:ℕ) (hn:n≤Fintype.card A)
    (hs:∀i<n,rectAct (controlled (M:=μ i) (prefixMask H i T))
      (run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (freshStage h H K) z i)=
      run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (freshStage h H K) z i) :
    ‖run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (freshStage h H K) z n-
      run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
        (polarStage h (middleStage T H) (publicStage T K)) z n‖≤
      ∑i∈Finset.range n,freshCost (Fintype.card A) i := by
  apply run_distance_upto
  · intro i hi
    exact polarStage_norm h ht (middleStage T H) (publicStage T K)
      (middleStage_norm T H) (publicStage_norm T K hK) i
  · intro i hi
    exact supported_stage_error h ht H K hK i (by omega) _
      (run_norm (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i)
        (freshStage h H K) (freshStage_norm h ht H K hK) z hz i) (hs i hi)

#print axioms controlled_inverse_error
#print axioms supported_stage_error
#print axioms fresh_polar_distance
end
end ICO.C6HistoryHybrid
