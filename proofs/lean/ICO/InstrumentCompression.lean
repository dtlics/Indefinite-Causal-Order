import QIT.Core.Channel

/-! # Finite adaptive instrument trees between oracle queries

Every node may select a different continuation from a classical measurement
outcome. The exact summed map is a channel, and therefore has a finite
Stinespring realization. This justifies compressing an arbitrary finite block
of adaptive operations that contains no oracle use.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT

namespace ICO.InstrumentCompression

set_option maxHeartbeats 200000
noncomputable section

universe u
variable {A B C L : Type u}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype L]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq L]

/-- Refine classical outcomes to individual Kraus outcomes. An arbitrary finite
instrument has this representation by retaining its Kraus index privately. -/
structure Instrument (A B L : Type u) [Fintype A] [Fintype B] [Fintype L]
    [DecidableEq A] [DecidableEq B] where
  op : L → Matrix B A ℂ
  complete : ∑ l : L, (op l).conjTranspose * op l = 1

def branchMap (I : Instrument A B L) (l : L) : MatrixMap A B :=
  MatrixMap.ofKraus (fun (_ : Unit) => I.op l)

theorem branchMap_apply (I : Instrument A B L) (l : L) (X : CMatrix A) :
    branchMap I l X = I.op l * X * (I.op l).conjTranspose := by
  simp [branchMap, MatrixMap.ofKraus]

def adaptiveMap (I : Instrument A B L) (next : L → Channel B C) : MatrixMap A C :=
  ∑ l : L, (next l).map.comp (branchMap I l)

theorem adaptiveMap_apply (I : Instrument A B L) (next : L → Channel B C) (X : CMatrix A) :
    adaptiveMap I next X = ∑ l : L, (next l).map (I.op l * X * (I.op l).conjTranspose) := by
  simp [adaptiveMap, branchMap_apply]

theorem choi_adaptiveMap (I : Instrument A B L) (next : L → Channel B C) :
    MatrixMap.choi (adaptiveMap I next) =
      ∑ l : L, MatrixMap.choi ((next l).map.comp (branchMap I l)) := by
  ext i j
  simp [MatrixMap.choi, adaptiveMap, Matrix.sum_apply]

theorem adaptiveMap_cp (I : Instrument A B L) (next : L → Channel B C) :
    MatrixMap.IsCompletelyPositive (adaptiveMap I next) := by
  rw [MatrixMap.IsCompletelyPositive, choi_adaptiveMap]
  apply Matrix.posSemidef_sum Finset.univ
  intro l hl
  exact MatrixMap.isCompletelyPositive_comp (next l).map (branchMap I l)
    (next l).completelyPositive (MatrixMap.ofKraus_completelyPositive _)

theorem adaptiveMap_tp (I : Instrument A B L) (next : L → Channel B C) :
    MatrixMap.IsTracePreserving (adaptiveMap I next) := by
  intro X
  rw [adaptiveMap_apply, Matrix.trace_sum]
  have hp (l : L) : ((next l).map (I.op l * X * (I.op l).conjTranspose)).trace =
      (I.op l * X * (I.op l).conjTranspose).trace := (next l).tracePreserving _
  simp_rw [hp]
  have hI : MatrixMap.krausAdjoint I.op (1 : CMatrix B) = 1 := by
    simpa [MatrixMap.krausAdjoint] using I.complete
  have h := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one I.op hI X
  simpa [MatrixMap.ofKraus, Matrix.trace_sum] using h

def adaptiveChannel (I : Instrument A B L) (next : L → Channel B C) : Channel A C where
  map := adaptiveMap I next
  completelyPositive := adaptiveMap_cp I next
  tracePreserving := adaptiveMap_tp I next
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ (adaptiveMap_cp I next)

/-- A finite adaptive classical-control tree. Internal memory spaces and
outcome sets can differ at every node; no fixed depth or branch count is imposed. -/
inductive Tree (C : Type u) [Fintype C] [DecidableEq C] :
    (A : Type u) → [Fintype A] → [DecidableEq A] → Type (u + 1) where
  | terminal {A : Type u} [Fintype A] [DecidableEq A] (channel : Channel A C) : Tree C A
  | node {A B L : Type u} [Fintype A] [Fintype B] [Fintype L]
      [DecidableEq A] [DecidableEq B] [DecidableEq L]
      (instrument : Instrument A B L) (next : L → Tree C B) : Tree C A

def Tree.toChannel {C : Type u} [Fintype C] [DecidableEq C]
    {A : Type u} [Fintype A] [DecidableEq A] (tree : Tree C A) : Channel A C := by
  induction tree with
  | terminal channel => exact channel
  | node instrument next ih => exact adaptiveChannel instrument ih

theorem Tree.node_map {C : Type u} [Fintype C] [DecidableEq C]
    {A B L : Type u} [Fintype A] [Fintype B] [Fintype L]
    [DecidableEq A] [DecidableEq B] [DecidableEq L]
    (instrument : Instrument A B L) (next : L → Tree C B) (X : CMatrix A) :
    (Tree.node instrument next).toChannel.map X =
      ∑ l : L, (next l).toChannel.map
        (instrument.op l * X * (instrument.op l).conjTranspose) :=
  adaptiveMap_apply instrument (fun l => (next l).toChannel) X

/-- Every compiled finite adaptive block has a finite Kraus dilation whose
isometry equation follows from the proved trace-preservation law. -/
theorem Tree.exists_isometric_kraus {C : Type u} [Fintype C] [DecidableEq C]
    {A : Type u} [Fintype A] [DecidableEq A] (tree : Tree C A) :
    ∃ K : (A × C) → Matrix C A ℂ,
      tree.toChannel.map = MatrixMap.ofKraus K ∧
        (MatrixMap.krausStinespringMatrix K).conjTranspose *
          MatrixMap.krausStinespringMatrix K = 1 := by
  obtain ⟨K, hK⟩ := MatrixMap.exists_kraus_of_choi_psd
    tree.toChannel.map tree.toChannel.completelyPositive
  refine ⟨K, hK, ?_⟩
  have hTP : MatrixMap.IsTracePreserving (MatrixMap.ofKraus K) := by
    rw [← hK]
    exact tree.toChannel.tracePreserving
  exact MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K
    (MatrixMap.krausAdjoint_one_of_tracePreserving K hTP)

end
end ICO.InstrumentCompression
