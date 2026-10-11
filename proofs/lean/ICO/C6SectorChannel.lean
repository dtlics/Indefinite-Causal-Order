import ICO.C6CacheMap
import ICO.C6MatrixCovariance

/-! Genuine CPTP extension of channels on private finite sectors. Cross-sector
coherences are discarded; no reachable-history assumption enters the channel. -/
namespace ICO.C6SectorChannel
open QIT Matrix ICO.C6CacheMap ICO.C6MatrixCovariance ICO.RecordingCopyIdentity
open scoped BigOperators Matrix ComplexOrder MatrixOrder
noncomputable section
set_option maxHeartbeats 2200000
universe u v w x y
variable {I : Type v} {B : Type w} [Fintype I] [DecidableEq I]
  {H : I → Type u} [∀i,Fintype (H i)] [∀i,DecidableEq (H i)]
  [Fintype B] [DecidableEq B]

def inclusion (i : I) : Matrix (Σj,H j) (H i) ℂ :=
  basisEmbedding (Sigma.mk i)

theorem inclusion_gram (i : I) : (inclusion (H := H) i).conjTranspose*inclusion (H := H) i=1 :=
  basisEmbedding_gram _ (by intro x y h; exact eq_of_heq (Sigma.mk.inj h).2)

theorem inclusion_complete : (∑i : I,inclusion (H := H) i*(inclusion i).conjTranspose)=1 := by
  ext x y
  have hs : (∑i : I,∑a : H i,(if x=⟨i,a⟩ then (1:ℂ) else 0)*
      star (if y=⟨i,a⟩ then (1:ℂ) else 0)) = if x=y then 1 else 0 := by
    rw [← Fintype.sum_sigma (fun z : Σi,H i =>
      (if x=z then (1:ℂ) else 0)*star (if y=z then (1:ℂ) else 0))]
    simp [apply_ite, eq_comm]
  simpa only [inclusion, basisEmbedding, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.one_apply,
    Function.id_def] using hs

def sectorMap (Φ : ∀i,Channel (H i) B) : MatrixMap (Σi,H i) B :=
  ∑i,(Φ i).map.comp (conjugate (inclusion i).conjTranspose)

theorem cp_sum {a : Type x} {b : Type y} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (s : Finset I) (Φ : I → MatrixMap a b)
    (h : ∀i∈s,MatrixMap.IsCompletelyPositive (Φ i)) :
    MatrixMap.IsCompletelyPositive (∑i∈s,Φ i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (MatrixMap.choi (0 : MatrixMap a b)).PosSemidef
    have hz : MatrixMap.choi (0 : MatrixMap a b)=0 := by ext i j; rfl
    rw [hz]
    exact Matrix.PosSemidef.zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact cp_add (h i (Finset.mem_insert_self _ _))
      (ih (by intro j hj; exact h j (Finset.mem_insert_of_mem hj)))

theorem sector_cp (Φ : ∀i,Channel (H i) B) : MatrixMap.IsCompletelyPositive (sectorMap Φ) := by
  apply cp_sum
  intro i _
  exact MatrixMap.isCompletelyPositive_comp _ _ (Φ i).completelyPositive (conjugate_cp _)

theorem sector_trace (Φ : ∀i,Channel (H i) B) :
    MatrixMap.IsTracePreserving (sectorMap Φ) := by
  intro X
  simp only [sectorMap, LinearMap.sum_apply, LinearMap.comp_apply, Matrix.trace_sum]
  have ht (i : I) : ((Φ i).map (conjugate (inclusion (H := H) i).conjTranspose X)).trace =
      (inclusion i*(inclusion i).conjTranspose*X).trace := by
    rw [(Φ i).tracePreserving, conjugate_trace, Matrix.conjTranspose_conjTranspose]
  simp_rw [ht]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, inclusion_complete, Matrix.one_mul]

def sectorChannel (Φ : ∀i,Channel (H i) B) : Channel (Σi,H i) B where
  map := sectorMap Φ
  completelyPositive := sector_cp Φ
  tracePreserving := sector_trace Φ
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ (sector_cp Φ)

theorem sector_apply (Φ : ∀i,Channel (H i) B) (X : CMatrix (Σi,H i)) :
    (sectorChannel Φ).map X=∑i,(Φ i).map ((inclusion i).conjTranspose*X*inclusion i) := by
  simp only [sectorChannel, sectorMap, LinearMap.sum_apply, LinearMap.comp_apply,
    conjugate_apply, Matrix.conjTranspose_conjTranspose]

#print axioms inclusion_complete
#print axioms sectorChannel
end
end ICO.C6SectorChannel
