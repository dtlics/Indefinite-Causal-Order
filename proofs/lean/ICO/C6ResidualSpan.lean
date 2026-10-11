import ICO.C6ResidualModes

/-! One adapted mode basis simultaneously resolves every prefix span of the
complete private outcome history. -/
namespace ICO.C6ResidualSpan
open Matrix QIT ICO.C6ResidualModes ICO.C6CacheHistorySpan ICO.C6CacheSpanProjection
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

def prefixSpan {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (s:ℕ) : Submodule ℂ (EuclideanSpace ℂ A) :=
  Submodule.span ℂ (Set.range (fun i:{i:Fin q // i.val<s}=>v i))

theorem prior_le_prefix {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (s:ℕ)
    (i:Fin q) (hi:i.val≤s) : historySpan (prior v i)≤prefixSpan v s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact Submodule.subset_span ⟨⟨⟨j.val,lt_trans j.isLt i.isLt⟩,lt_of_lt_of_le j.isLt hi⟩,rfl⟩

theorem raw_mem_residual_prefix {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (s:ℕ)
    (i:Fin q) (hi:i.val<s) : v i∈prefixSpan (residual v) s := by
  suffices hh:∀n,∀i:Fin q,i.val=n→i.val<s→v i∈prefixSpan (residual v) s from hh i.val i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hin his
    have hp:historySpan (prior v i)≤prefixSpan (residual v) s := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      apply ih j.val (by omega) ⟨j.val,lt_trans j.isLt i.isLt⟩ rfl
      exact lt_trans j.isLt his
    have hproj:=hp (projection_mem_prior v i)
    have hr:residual v i∈prefixSpan (residual v) s :=
      Submodule.subset_span ⟨⟨i,his⟩,rfl⟩
    simpa only [ICO.C6ResidualModes.residual,sub_add_cancel] using Submodule.add_mem _ hr hproj

theorem prefixSpan_residual {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (s:ℕ) :
    prefixSpan (residual v) s=prefixSpan v s := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨i,rfl⟩)
      (prior_le_prefix v s i i.property.le (projection_mem_prior v i))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact raw_mem_residual_prefix v s i i.property

theorem residual_mem_mode_span {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (s:ℕ)
    (i:Fin q) (hi:i.val<s) : residual v i∈prefixSpan (mode v) s := by
  by_cases hz:residual v i=0
  · rw [hz]; exact Submodule.zero_mem _
  · have hm:mode v i∈prefixSpan (mode v) s := Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩
    have hn:(‖residual v i‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    have he:(‖residual v i‖:ℂ) • mode v i=residual v i := by
      rw [mode,smul_smul,mul_inv_cancel₀ hn,one_smul]
    rw [←he]
    exact Submodule.smul_mem _ _ hm

theorem prefixSpan_mode {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (s:ℕ) :
    prefixSpan (mode v) s=prefixSpan v s := by
  rw [←prefixSpan_residual v s]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact residual_mem_mode_span v s i i.property

def activeIndices {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (labels:Active v→A) (s:ℕ) : Finset A :=
  (Finset.univ.filter (fun i:Active v=>i.val.val<s)).image labels

theorem selectedSpan_active {q:ℕ} (v:Fin q→EuclideanSpace ℂ A)
    (U:Matrix.unitaryGroup A ℂ) (labels:Active v→A)
    (he:∀i x,(U:CMatrix A) x (labels i)=mode v i x) (s:ℕ) :
    selectedSpan U (activeIndices v labels s)=prefixSpan v s := by
  rw [←prefixSpan_mode v s]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    obtain ⟨i,hi,hia⟩:=Finset.mem_image.mp a.property
    have his:i.val.val<s := (Finset.mem_filter.mp hi).2
    have hc:column U a=mode v i := by
      ext x
      change (U:CMatrix A) x a=mode v i x
      rw [←hia]
      exact he i x
    change column U a ∈ prefixSpan (mode v) s
    rw [hc]
    exact Submodule.subset_span ⟨⟨i.val,his⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hz:residual v i=0
    · simp only [mode,hz,smul_zero]
      exact Submodule.zero_mem _
    · let a:Active v:=⟨i,hz⟩
      have ha:labels a∈activeIndices v labels s :=
        Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩,rfl⟩
      have hc:column U (labels a)=mode v i := by ext x; exact he a x
      change mode v i ∈ selectedSpan U (activeIndices v labels s)
      rw [←hc]
      exact Submodule.subset_span ⟨⟨labels a,ha⟩,rfl⟩

theorem all_prefixes_adapted {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) :
    ∃(U:Matrix.unitaryGroup A ℂ)(labels:Active v→A),Function.Injective labels ∧
      (∀i x,(U:CMatrix A) x (labels i)=mode v i x) ∧
      ∀s,selectedSpan U (activeIndices v labels s)=prefixSpan v s := by
  obtain ⟨U,f,hf,he⟩:=adapted_unitary v
  exact ⟨U,f,hf,he,selectedSpan_active v U f he⟩

#print axioms prefixSpan_residual
#print axioms all_prefixes_adapted
end
end ICO.C6ResidualSpan
