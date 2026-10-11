import ICO.C6ModeEncoding

/-! An arbitrary finite orthonormal mode family has an actual unitary
coordinate realization.  The modes need not be computational basis vectors. -/
namespace ICO.C6OrthogonalFrame
open QIT
noncomputable section
set_option maxHeartbeats 1800000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

theorem unitary_extension {n:ℕ} (v:Fin n→EuclideanSpace ℂ A) (hv:Orthonormal ℂ v) :
    ∃ (U:Matrix.unitaryGroup A ℂ) (labels:Fin n→A), Function.Injective labels ∧
      ∀i x,(U:CMatrix A) x (labels i)=v i x := by
  have hvr : Orthonormal ℂ ((↑):Set.range v→EuclideanSpace ℂ A) :=
    (orthonormal_subtype_range hv.linearIndependent.injective).2 hv
  obtain ⟨Y,bY,hY,hbY⟩ := hvr.exists_orthonormalBasis_extension
  have hcard : Fintype.card A=Fintype.card Y := by
    rw [←finrank_euclideanSpace (𝕜:=ℂ)]
    exact Module.finrank_eq_card_basis bY.toBasis
  let e:A≃Y := Fintype.equivOfCardEq hcard
  let b:OrthonormalBasis A ℂ (EuclideanSpace ℂ A) := bY.reindex e.symm
  let labels:Fin n→A := fun i=>e.symm ⟨v i,hY (Set.mem_range_self i)⟩
  have he (i:Fin n) : b (labels i)=v i := by
    simp only [b,labels,OrthonormalBasis.reindex_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
    exact congrFun hbY ⟨v i,hY (Set.mem_range_self i)⟩
  let U:Matrix.unitaryGroup A ℂ :=
    ⟨(EuclideanSpace.basisFun A ℂ).toBasis.toMatrix b,
      (EuclideanSpace.basisFun A ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  refine ⟨U,labels,?_,?_⟩
  · intro i j hij
    apply hv.linearIndependent.injective
    rw [←he i,←he j,hij]
  · intro i x
    change b (labels i) x=v i x
    rw [he]

#print axioms unitary_extension
end
end ICO.C6OrthogonalFrame
