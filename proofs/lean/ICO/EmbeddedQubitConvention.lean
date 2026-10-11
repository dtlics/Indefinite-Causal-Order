import ICO.EmbeddedSwitch
import ICO.DilutedSwitchSemantics

namespace ICO.EmbeddedQubitConvention
open Matrix ICO.EmbeddedSwitch ICO.QubitCircuitLink ICO.QubitLink
open ICO.PositiveSupport ICO.DilutedSwitchTarget
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section

def outputPermutation : Matrix (Fin 4) (Fin 2 × Fin 2) ℂ :=
  fun f ct => if f=finProdFinEquiv ct then 1 else 0

theorem outputPermutation_isometry : outputPermutationᴴ*outputPermutation=1 := by
  ext a b
  simp [outputPermutation,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
    apply_ite,ite_mul,mul_ite,(finProdFinEquiv (m:=2) (n:=2)).injective.eq_iff,eq_comm]

theorem vectorize_switch (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    vectorize (outputPermutation*switchKraus U V) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • outputVector U V 3 := by
  funext o
  fin_cases o <;>
    norm_num [vectorize,outputPermutation,switchKraus,orderedPair,outputVector,bit,
      Matrix.mul_apply,Matrix.smul_apply,Pi.smul_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,finProdFinEquiv,Fin.divNat,Fin.modNat,show (3 : Fin 4).val=3 by decide] <;> ring

theorem rankOne_vectorize_switch (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    rankOne (vectorize (outputPermutation*switchKraus U V)) =
      (1/2 : ℂ) • rankOne (outputVector U V 3) := by
  rw [vectorize_switch]
  have hs : (Real.sqrt 2)⁻¹=Real.sqrt (1/2 : ℝ) := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1)]
    norm_num
  rw [hs,rankOne_sqrt_scale (1/2) (by norm_num)]
  norm_num

theorem switch_choi_convention {I J : Type*} [Fintype I] [Fintype J]
    (U : I → Matrix (Fin 2) (Fin 2) ℂ) (V : J → Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i,∑ j,rankOne (vectorize (outputPermutation*switchKraus (U i) (V j)))) = switchChoi U V := by
  simp_rw [rankOne_vectorize_switch]
  simp only [switchChoi,Finset.smul_sum]

#print axioms switch_choi_convention
end
end ICO.EmbeddedQubitConvention

