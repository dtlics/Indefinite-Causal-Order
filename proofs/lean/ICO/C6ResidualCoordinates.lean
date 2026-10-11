import ICO.C6ResidualSpan

/-! A single adapted basis represents every actual historyPrefix projection. -/
namespace ICO.C6ResidualCoordinates
open Matrix QIT ICO.C6ResidualModes ICO.C6ResidualSpan ICO.C6CacheSpanProjection
  ICO.C6CacheHistorySpan
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

def historyPrefix {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (s:ℕ) (hs:s≤q) :
    Fin s→EuclideanSpace ℂ A := fun i=>v ⟨i.val,lt_of_lt_of_le i.isLt hs⟩

theorem prefixSpan_eq {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (s:ℕ) (hs:s≤q) :
    prefixSpan v s=historySpan (historyPrefix v s hs) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨⟨i.val.val,i.property⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span ⟨⟨⟨i.val,lt_of_lt_of_le i.isLt hs⟩,i.isLt⟩,rfl⟩

theorem activeIndices_mono {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (labels:Active v→A)
    {s t:ℕ} (hst:s≤t) : activeIndices v labels s⊆activeIndices v labels t := by
  apply Finset.image_subset_image
  intro i hi
  obtain ⟨hi,his⟩:=Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hi,lt_of_lt_of_le his hst⟩

theorem own_label_fresh {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (labels:Active v→A)
    (hl:Function.Injective labels) (i:Active v) :
    labels i∉activeIndices v labels i.val.val := by
  intro hi
  obtain ⟨j,hj,hji⟩:=Finset.mem_image.mp hi
  have he:=hl hji
  subst j
  exact (Nat.lt_irrefl _) (Finset.mem_filter.mp hj).2

theorem own_label_recorded {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (labels:Active v→A)
    (i:Active v) : labels i∈activeIndices v labels (i.val.val+1) := by
  exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.lt_succ_self _⟩,rfl⟩

theorem all_prefix_projections {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) :
    ∃(U:Matrix.unitaryGroup A ℂ)(labels:Active v→A),Function.Injective labels ∧
      (∀i x,(U:CMatrix A) x (labels i)=mode v i x) ∧
      ∀s (hs:s≤q),historyProjection (historyPrefix v s hs)=
        spanProjection U (activeIndices v labels s) := by
  obtain ⟨U,f,hf,he,hspan⟩:=all_prefixes_adapted v
  refine ⟨U,f,hf,he,?_⟩
  intro s hs
  apply projection_unique
  rw [(history_realization _).1,hspan,prefixSpan_eq v s hs]

#print axioms all_prefix_projections
end
end ICO.C6ResidualCoordinates
