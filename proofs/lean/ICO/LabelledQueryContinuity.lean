import ICO.LabelledQueryTree
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.LabelledQueryTree

namespace ICO.LabelledQueryTree
set_option maxHeartbeats 600000
noncomputable section
universe u v
variable {L H O A : Type u} [DecidableEq L] [Fintype H] [Fintype O]
  [DecidableEq H] [DecidableEq O] [Fintype A] [DecidableEq A]

theorem continuous_ofChoi_apply {T : Type v} [TopologicalSpace T]
    (J : T → CMatrix (H × H)) (X : T → CMatrix H)
    (hJ : Continuous J) (hX : Continuous X) :
    Continuous (fun t => MatrixMap.ofChoiMatrix (J t) (X t)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [MatrixMap.ofChoiMatrix_apply]
  apply continuous_finset_sum
  intro a ha
  apply continuous_finset_sum
  intro b hb
  exact ((continuous_apply b).comp ((continuous_apply a).comp hX)).mul
    ((continuous_apply (b,j)).comp ((continuous_apply (a,i)).comp hJ))

theorem Tree.eval_continuous {s : Finset L} (tree : Tree L H O s A)
    {T : Type v} [TopologicalSpace T]
    (J : T → L → CMatrix (H × H)) (hJ : Continuous J)
    (X : T → CMatrix A) (hX : Continuous X) :
    Continuous (fun t => tree.map (fun i => MatrixMap.ofChoiMatrix (J t i)) (X t)) := by
  induction tree with
  | terminal channel =>
    exact channel.map.continuous_of_finiteDimensional.comp hX
  | query i hi after ih =>
    apply ih
    exact continuous_ofChoi_apply (fun t => J t i) X ((continuous_apply i).comp hJ) hX
  | node instrument next ih =>
    simp only [Tree.map_node, LinearMap.sum_apply, LinearMap.comp_apply]
    apply continuous_finset_sum
    intro k hk
    exact ih k (fun t => branchMap instrument k (X t))
      ((branchMap instrument k).continuous_of_finiteDimensional.comp hX)

def ofChoiLinear : CMatrix (H × H) →ₗ[ℂ] MatrixMap H H where
  toFun := MatrixMap.ofChoiMatrix
  map_add' X Y := by
    ext Z i j
    simp [MatrixMap.ofChoiMatrix_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c X := by
    ext Z i j
    simp [MatrixMap.ofChoiMatrix_apply,Finset.mul_sum,mul_left_comm]

def choiLinear : MatrixMap A O →ₗ[ℂ] CMatrix (A × O) where
  toFun := MatrixMap.choi
  map_add' X Y := rfl
  map_smul' c X := rfl

/-- Actual circuit output Choi matrix, as a continuous multilinear function
of the distinct slot Choi matrices. Positivity is not assumed for this algebraic
extension; actual channels agree by `Tree.channel_map`. -/
def Tree.continuousMultilinear [Fintype L] (tree : Tree L H O Finset.univ A) :
    ContinuousMultilinearMap ℂ (fun _ : L => CMatrix (H × H)) (CMatrix (A × O)) where
  toMultilinearMap := choiLinear.compMultilinearMap
    (tree.multilinear.compLinearMap (fun _ => ofChoiLinear))
  cont := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply j.2).comp ((continuous_apply i.2).comp
      (tree.eval_continuous (fun J => J) continuous_id
        (fun _ => Matrix.single i.1 j.1 (1 : ℂ)) continuous_const))

#print axioms Tree.continuousMultilinear
end
end ICO.LabelledQueryTree
