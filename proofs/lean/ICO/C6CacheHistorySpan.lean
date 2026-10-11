import ICO.C6BosonicFockRotated
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A literal finite history determines a geometric label span of dimension
at most the history length. Its unitary-coordinate realization is derived. -/
namespace ICO.C6CacheHistorySpan
open QIT Module Submodule
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
variable {A : Type*} [Fintype A] [DecidableEq A]

def historySpan {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) :
    Submodule ℂ (EuclideanSpace ℂ A) := Submodule.span ℂ (Set.range v)

theorem historySpan_rank {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) :
    Module.finrank ℂ (historySpan v)≤s := by
  simpa [historySpan] using (finrank_range_le_card (R:=ℂ) v)

theorem historySpan_contains {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) (i : Fin s) :
    v i ∈ historySpan v := Submodule.subset_span (Set.mem_range_self i)

theorem historySpan_snoc {s : ℕ} (v : Fin s → EuclideanSpace ℂ A)
    (x : EuclideanSpace ℂ A) :
    historySpan (Fin.snoc v x)=historySpan v ⊔ Submodule.span ℂ {x} := by
  unfold historySpan
  rw [Fin.range_snoc,Submodule.span_insert]
  exact sup_comm _ _

theorem subspace_basis (K : Submodule ℂ (EuclideanSpace ℂ A)) :
    ∃ (b : OrthonormalBasis A ℂ (EuclideanSpace ℂ A)) (S : Finset A),
      Submodule.span ℂ (Set.range (fun i : S => b i))=K ∧ S.card=Module.finrank ℂ K := by
  classical
  let bK := stdOrthonormalBasis ℂ K
  let v := K.subtypeₗᵢ ∘ bK
  have hv : Orthonormal ℂ v := bK.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hvr : Orthonormal ℂ ((↑) : Set.range v → EuclideanSpace ℂ A) :=
    (orthonormal_subtype_range hv.linearIndependent.injective).2 hv
  obtain ⟨Y,bY,hY,hbY⟩ := hvr.exists_orthonormalBasis_extension
  have hcard : Fintype.card A=Fintype.card Y := by
    rw [←finrank_euclideanSpace (𝕜:=ℂ)]
    exact Module.finrank_eq_card_basis bY.toBasis
  let e : A ≃ Y := Fintype.equivOfCardEq hcard
  let b : OrthonormalBasis A ℂ (EuclideanSpace ℂ A) := bY.reindex e.symm
  let S : Finset A := Finset.univ.filter (fun i => b i ∈ K)
  have hb (i : A) : b i=(e i : EuclideanSpace ℂ A) := by
    simpa only [b,OrthonormalBasis.reindex_apply,Equiv.symm_symm] using congrFun hbY (e i)
  have hvspan : Submodule.span ℂ (Set.range v)=K := by
    change Submodule.span ℂ (Set.range (K.subtype ∘ bK.toBasis))=K
    rw [Set.range_comp,Submodule.span_image,bK.toBasis.span_eq,Submodule.map_subtype_top]
  have hs : Submodule.span ℂ (Set.range (fun i : S => b i))=K := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact (Finset.mem_filter.mp i.property).2
    · rw [←hvspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      have hj : v j ∈ Y := hY (Set.mem_range_self j)
      let i : A := e.symm ⟨v j,hj⟩
      have hi : b i=v j := by rw [hb]; simp only [i,Equiv.apply_symm_apply]
      have him : i∈S := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        rw [hi]
        exact (bK j).property
      exact Submodule.subset_span ⟨⟨i,him⟩,hi⟩
  refine ⟨b,S,hs,?_⟩
  have hr := finrank_span_eq_card (b.orthonormal.comp (fun i : S => (i:A)) Subtype.val_injective).linearIndependent
  have hf := congrArg (fun L : Submodule ℂ (EuclideanSpace ℂ A) => Module.finrank ℂ L) hs
  exact (Fintype.card_coe S).symm.trans (hr.symm.trans hf)

def column (U : Matrix.unitaryGroup A ℂ) (j : A) : EuclideanSpace ℂ A :=
  WithLp.toLp 2 (fun i => (U : CMatrix A) i j)

theorem unitary_coordinates (K : Submodule ℂ (EuclideanSpace ℂ A)) :
    ∃ (U : Matrix.unitaryGroup A ℂ) (S : Finset A),
      Submodule.span ℂ (Set.range (fun i : S => column U i))=K ∧
      S.card=Module.finrank ℂ K := by
  obtain ⟨b,S,hspan,hcard⟩ := subspace_basis K
  let U : Matrix.unitaryGroup A ℂ :=
    ⟨(EuclideanSpace.basisFun A ℂ).toBasis.toMatrix b,
      (EuclideanSpace.basisFun A ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hc (j : A) : column U j=b j := by
    ext i
    rfl
  exact ⟨U,S,by simpa only [hc] using hspan,hcard⟩

theorem history_coordinates {s : ℕ} (v : Fin s → EuclideanSpace ℂ A) :
    ∃ (U : Matrix.unitaryGroup A ℂ) (S : Finset A),
      Submodule.span ℂ (Set.range (fun i : S => column U i))=historySpan v ∧ S.card≤s := by
  obtain ⟨U,S,hspan,hcard⟩ := unitary_coordinates (historySpan v)
  exact ⟨U,S,hspan,hcard.le.trans (historySpan_rank v)⟩

#print axioms unitary_coordinates
#print axioms history_coordinates
end
end ICO.C6CacheHistorySpan
