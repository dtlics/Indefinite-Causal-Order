import ICO.DilutedSwitchSemantics

namespace ICO.SwitchMixture
open Matrix ICO.QubitLink ICO.PositiveSupport ICO.DilutedSwitchTarget
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section

def mixtureKraus {I : Type*} (t : ℝ) (U : I → Matrix (Fin 2) (Fin 2) ℂ) :
    Option I → Matrix (Fin 2) (Fin 2) ℂ
  | none => (Real.sqrt (1-t) : ℂ) • 1
  | some i => (Real.sqrt t : ℂ) • U i

theorem output_identity_left (U : Matrix (Fin 2) (Fin 2) ℂ) :
    outputVector 1 U 3 = queryOutput U := by
  funext o
  simp [outputVector,queryOutput,show (3 : Fin 4).val=3 by decide]

theorem output_identity_right (U : Matrix (Fin 2) (Fin 2) ℂ) :
    outputVector U 1 3 = queryOutput U := by
  funext o
  simp [outputVector,queryOutput,show (3 : Fin 4).val=3 by decide]

theorem query_identity : queryOutput (1 : Matrix (Fin 2) (Fin 2) ℂ) = identityOutput := by
  funext o
  simp [queryOutput,identityOutput,outputVector,Matrix.one_apply,eq_comm]

theorem rankOne_output_scaled (x y : ℝ) (hx : 0≤x) (hy : 0≤y)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    rankOne (outputVector ((Real.sqrt x : ℂ) • U) ((Real.sqrt y : ℂ) • V) 3) =
      ((x*y : ℝ) : ℂ) • rankOne (outputVector U V 3) := by
  rw [output_scaled]
  norm_num only [outputScale,show (3 : Fin 4).val=3 by decide,
    show (3 : Nat)≠0 by decide,show (3 : Nat)≠1 by decide,
    show (3 : Nat)≠2 by decide,if_false]
  rw [← smul_smul,rankOne_sqrt_scale x hx,rankOne_sqrt_scale y hy,smul_smul]
  congr 1
  push_cast
  rfl

/-- The physical switch is affine in both channel mixtures with identity;
this is proved from its actual Kraus output vectors. -/
theorem switch_mixture {I J : Type*} [Fintype I] [Fintype J]
    (t s : ℝ) (ht : t∈Set.Icc 0 1) (hs : s∈Set.Icc 0 1)
    (U : I → Matrix (Fin 2) (Fin 2) ℂ) (V : J → Matrix (Fin 2) (Fin 2) ℂ) :
    switchChoi (mixtureKraus t U) (mixtureKraus s V) =
      (((1-t)*(1-s) : ℝ) : ℂ) • identityChoi +
      ((t*(1-s) : ℝ) : ℂ) • queryChoi U +
      (((1-t)*s : ℝ) : ℂ) • queryChoi V +
      ((t*s : ℝ) : ℂ) • switchChoi U V := by
  unfold switchChoi
  simp only [Fintype.sum_option,mixtureKraus]
  simp_rw [rankOne_output_scaled (1-t) (1-s) (by linarith [ht.2]) (by linarith [hs.2]),
    rankOne_output_scaled t (1-s) ht.1 (by linarith [hs.2]),
    rankOne_output_scaled (1-t) s (by linarith [ht.2]) hs.1,
    rankOne_output_scaled t s ht.1 hs.1,
    output_identity_left,output_identity_right,query_identity]
  ext o p
  simp only [identityChoi,queryChoi,Matrix.sum_apply,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  ring

#print axioms switch_mixture
end
end ICO.SwitchMixture
