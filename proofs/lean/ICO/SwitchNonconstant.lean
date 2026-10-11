import ICO.SwitchMixture

namespace ICO.SwitchNonconstant
open Matrix ICO.QubitLink ICO.PositiveSupport ICO.DilutedSwitchTarget
open scoped BigOperators
set_option maxHeartbeats 500000
noncomputable section

def identityFamily : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 1
def flip : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i=j then 0 else 1
def flipFamily : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ := fun _ => flip

theorem identity_complete : (∑ i,(identityFamily i)ᴴ * identityFamily i)=1 := by
  simp [identityFamily]

theorem flip_complete : (∑ i,(flipFamily i)ᴴ * flipFamily i)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flipFamily,flip,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.conjTranspose_apply,Matrix.one_apply]

theorem switch_changes_first :
    switchChoi identityFamily identityFamily ≠ switchChoi flipFamily identityFamily := by
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [switchChoi,identityFamily,flipFamily,flip,rankOne,Matrix.vecMulVec_apply,
    Matrix.sum_apply,Matrix.smul_apply,outputVector,bit,Matrix.mul_apply,Matrix.one_apply,
    Fin.sum_univ_two,show (3 : Fin 4).val=3 by decide] at he

theorem switch_changes_second :
    switchChoi identityFamily identityFamily ≠ switchChoi identityFamily flipFamily := by
  intro h
  have he := congrFun (congrFun h 0) 0
  norm_num [switchChoi,identityFamily,flipFamily,flip,rankOne,Matrix.vecMulVec_apply,
    Matrix.sum_apply,Matrix.smul_apply,outputVector,bit,Matrix.mul_apply,Matrix.one_apply,
    Fin.sum_univ_two,show (3 : Fin 4).val=3 by decide] at he

#print axioms switch_changes_first
end
end ICO.SwitchNonconstant
