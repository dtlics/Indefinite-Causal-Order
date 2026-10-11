import ICO.AllChannelPadding
import ICO.AtMostLabelledQueryTree
import ICO.LabelledCircuitComposition

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.MemoryEmbedding ICO.OraclePadding ICO.ClassicalDilation
open ICO.AllChannelPadding ICO.LabelledCircuitComposition

namespace ICO.PadLabelledCircuit
set_option maxHeartbeats 1000000
noncomputable section
variable {L A M O B I : Type} [DecidableEq L]
  [Fintype A] [Fintype M] [Fintype O] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq M] [DecidableEq O] [DecidableEq B] [DecidableEq I]

def leftMemory : M ↪ M ⊕ O := ⟨Sum.inl,Sum.inl_injective⟩
def rightMemory : O ↪ M ⊕ O := ⟨Sum.inr,Sum.inr_injective⟩

def dummyPre (a₀ : A) : Channel O (A × (M ⊕ O)) :=
  (queryEmbedChannel rightMemory).comp (isometryChannel (pad a₀) (pad_isometry a₀))

def dummyPost (a₀ : A) (o₀ : O) : Channel (A × (M ⊕ O)) O :=
  discardChannel.comp (queryRetraction rightMemory a₀ o₀)

theorem dummy_identity (a₀ : A) (o₀ : O) (U : I → CMatrix A)
    (hU : ∑ i,(U i)ᴴ*U i=1) :
    (dummyPost (M:=M) a₀ o₀).map.comp
      ((ICO.AllChannelDilation.oracleMap U).comp (dummyPre a₀).map) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply,dummyPost,dummyPre,Channel.comp,
    queryEmbedChannel,isometryChannel_apply,LinearMap.id_apply]
  rw [retracted_oracle,ICO.AllChannelPadding.discarded_oracle_identity U hU]

/-- After producing the output, all unused labels are physically queried on
fresh discarded registers; the output is retained in a separate memory summand. -/
def remaining (a₀ : A) (o₀ : O) (s : Finset L) :
    ICO.LabelledQueryTree.Tree L (A × (M ⊕ O)) O s O :=
  if hs : s.Nonempty then
    prepend (dummyPre a₀)
      (.query hs.choose hs.choose_spec
        (prepend (dummyPost a₀ o₀) (remaining a₀ o₀ (s.erase hs.choose))))
  else
    (Finset.not_nonempty_iff_eq_empty.mp hs).symm ▸ .terminal (Channel.idChannel O)
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem hs.choose_spec

theorem remaining_map (a₀ : A) (o₀ : O) (s : Finset L)
    (U : L → I → CMatrix A) (hU : ∀ l,∑ i,(U l i)ᴴ*U l i=1) :
    (remaining (M:=M) a₀ o₀ s).map (fun l => ICO.AllChannelDilation.oracleMap (U l)) =
      LinearMap.id := by
  rw [remaining]
  split_ifs with hs
  · rw [prepend_map,ICO.LabelledQueryTree.Tree.map_query,prepend_map,
      remaining_map a₀ o₀ (s.erase hs.choose) U hU]
    simpa only [LinearMap.id_comp,LinearMap.comp_assoc] using
      dummy_identity (M:=M) a₀ o₀ (U hs.choose) (hU hs.choose)
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    change (Channel.idChannel O).map = LinearMap.id
    ext X i j
    simp [Channel.idChannel,MatrixMap.ofKraus]
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem hs.choose_spec

def compile (a₀ : A) (m₀ : M) (o₀ : O) {s : Finset L}
    (tree : ICO.AtMostLabelledQueryTree.Tree L (A × M) O s B) :
    ICO.LabelledQueryTree.Tree L (A × (M ⊕ O)) O s B := by
  induction tree with
  | terminal channel => exact prepend channel (remaining a₀ o₀ _)
  | query i hi after ih =>
    exact prepend (queryEmbedChannel leftMemory)
      (.query i hi (prepend (queryRetraction leftMemory a₀ m₀) ih))
  | node instrument next ih => exact .node instrument ih

/-- Kernel-checked padding of arbitrary branch-dependent stopping, valid for
all noisy trace-preserving oracle families. The common memory is explicitly
the finite direct sum of the original query memory and the retained output. -/
theorem compile_map (a₀ : A) (m₀ : M) (o₀ : O) {s : Finset L}
    (tree : ICO.AtMostLabelledQueryTree.Tree L (A × M) O s B)
    (U : L → I → CMatrix A) (hU : ∀ l,∑ i,(U l i)ᴴ*U l i=1) :
    (compile a₀ m₀ o₀ tree).map (fun l => ICO.AllChannelDilation.oracleMap (U l)) =
      tree.map (fun l => ICO.AllChannelDilation.oracleMap (U l)) := by
  induction tree with
  | terminal channel =>
    change (prepend channel (remaining a₀ o₀ _)).map _ = _
    rw [prepend_map,remaining_map a₀ o₀ _ U hU,LinearMap.id_comp]
    rfl
  | query i hi after ih =>
    change (prepend (queryEmbedChannel leftMemory)
      (ICO.LabelledQueryTree.Tree.query i hi
        (prepend (queryRetraction leftMemory a₀ m₀) (compile a₀ m₀ o₀ after)))).map _ = _
    rw [prepend_map,ICO.LabelledQueryTree.Tree.map_query,prepend_map,ih]
    simp only [ICO.AtMostLabelledQueryTree.Tree.map_query,LinearMap.comp_assoc]
    rw [retracted_oracle_map]
  | node instrument next ih =>
    change (∑ k,((compile a₀ m₀ o₀ (next k)).map _).comp
      (ICO.InstrumentCompression.branchMap instrument k)) = _
    simp_rw [ih]
    rfl

#print axioms compile_map
end
end ICO.PadLabelledCircuit
