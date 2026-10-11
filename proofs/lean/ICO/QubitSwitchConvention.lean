import ICO.EmbeddedQubitConvention
import ICO.EmbeddingSwitchChannels
import ICO.QubitChoiIndex

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.EmbeddedQubitConvention ICO.QubitChoiIndex
open ICO.QubitCircuitLink ICO.PositiveSupport ICO.DilutedSwitchTarget

namespace ICO.QubitSwitchConvention
set_option maxRecDepth 100000
set_option maxHeartbeats 700000
noncomputable section

def permutationChannel : Channel (Fin 2 × Fin 2) (Fin 4) :=
  ICO.ClassicalDilation.isometryChannel outputPermutation outputPermutation_isometry

theorem flattened_switch {I J : Type} [Fintype I] [Fintype J]
    (U : I → CMatrix (Fin 2)) (V : J → CMatrix (Fin 2)) :
    flatten (MatrixMap.choi (permutationChannel.map.comp
      (ICO.EmbeddingSwitchChannels.switchMap U V))) = switchChoi U V := by
  rw [← switch_choi_convention U V]
  simp only [permutationChannel,ICO.ClassicalDilation.isometryChannel,
    ICO.EmbeddingSwitchChannels.switchMap,MatrixMap.ofKraus_comp_ofKraus,
    MatrixMap.choi_ofKraus]
  ext i j
  simp [flatten,Matrix.sum_apply,Fintype.sum_prod_type,rankOne,
    Matrix.vecMulVec_apply,vectorize]

#print axioms flattened_switch
end
end ICO.QubitSwitchConvention
