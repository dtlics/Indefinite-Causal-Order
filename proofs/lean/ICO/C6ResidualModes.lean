import ICO.C6CacheSpanProjection
import ICO.C6OrthogonalFrame

/-! The actual accepted fresh directions of a finite outcome history are
orthogonal. The adapted unitary basis is constructed, not assumed. -/
namespace ICO.C6ResidualModes
open Matrix QIT ICO.C6CacheHistorySpan ICO.C6CacheSpanProjection ICO.MHProtocolOverlap
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

def prior {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) : Fin i.val→EuclideanSpace ℂ A :=
  fun j=>v ⟨j.val,lt_trans j.isLt i.isLt⟩

def residual {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) : EuclideanSpace ℂ A :=
  v i-act (historyProjection (prior v i)) (v i)

theorem residual_eq_projection {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) :
    residual v i=act (1-historyProjection (prior v i)) (v i) := by
  rw [act_sub]
  have he:act (1:CMatrix A) (v i)=v i := by
    change WithLp.toLp 2 ((1:CMatrix A)*ᵥWithLp.ofLp (v i))=v i
    rw [Matrix.one_mulVec,WithLp.toLp_ofLp]
  rw [he]
  rfl

theorem prior_mono {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) {i j:Fin q} (h:i≤j) :
    historySpan (prior v i)≤historySpan (prior v j) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨k.val,lt_of_lt_of_le k.isLt h⟩,rfl⟩

theorem current_mem_prior {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) {i j:Fin q} (h:i<j) :
    v i∈historySpan (prior v j) :=
  Submodule.subset_span ⟨⟨i.val,h⟩,rfl⟩

theorem projection_mem_prior {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) :
    act (historyProjection (prior v i)) (v i)∈historySpan (prior v i) := by
  rw [←(history_realization (prior v i)).1]
  exact projection_mem _ _ _

theorem residual_mem_later {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) {i j:Fin q} (h:i<j) :
    residual v i∈historySpan (prior v j) :=
  Submodule.sub_mem _ (current_mem_prior v h)
    (prior_mono v h.le (projection_mem_prior v i))

theorem residual_orthogonal_prior {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q)
    (x:EuclideanSpace ℂ A) (hx:x∈historySpan (prior v i)) :
    ⟪x,residual v i⟫_ℂ=0 := by
  have hfix:act (historyProjection (prior v i)) x=x := by
    apply projection_fixes
    rwa [(history_realization (prior v i)).1]
  have hstar:(historyProjection (prior v i))ᴴ=historyProjection (prior v i) :=
    (spanProjection_projection _ _).isSelfAdjoint.star_eq
  have he:=act_adjoint_inner (historyProjection (prior v i)) x (v i)
  rw [hfix,hstar] at he
  rw [residual,inner_sub_right,he,sub_self]

theorem residual_orthogonal {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) {i j:Fin q} (h:i≠j) :
    ⟪residual v i,residual v j⟫_ℂ=0 := by
  rcases lt_or_gt_of_ne h with hlt|hgt
  · exact residual_orthogonal_prior v j _ (residual_mem_later v hlt)
  · rw [←inner_conj_symm]
    rw [residual_orthogonal_prior v i _ (residual_mem_later v hgt)]
    simp

def mode {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) : EuclideanSpace ℂ A :=
  (‖residual v i‖:ℂ)⁻¹ • residual v i

abbrev Active {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) := {i:Fin q // residual v i≠0}

instance activeFintype {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) : Fintype (Active v) :=
  Fintype.ofFinite _
instance activeDecidableEq {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) : DecidableEq (Active v) :=
  Classical.decEq _

theorem mode_orthonormal {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) :
    Orthonormal ℂ (fun i:Active v=>mode v i) := by
  constructor
  · intro i
    change ‖(‖residual v i.val‖:ℂ)⁻¹ • residual v i.val‖=1
    rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr i.property)]
  · intro i j hij
    have h:i.val≠j.val := fun he=>hij (Subtype.ext he)
    simp only [mode,inner_smul_left,inner_smul_right,residual_orthogonal v h,mul_zero]

theorem mode_mem_later {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) {i j:Fin q} (h:i<j) :
    mode v i∈historySpan (prior v j) :=
  Submodule.smul_mem _ _ (residual_mem_later v h)

/-- One unitary realizes every nonzero accepted mode of the complete history. -/
theorem adapted_unitary {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) :
    ∃(U:Matrix.unitaryGroup A ℂ)(labels:Active v→A),Function.Injective labels ∧
      ∀i x,(U:CMatrix A) x (labels i)=mode v i x := by
  let e:Fin (Fintype.card (Active v))≃Active v := (Fintype.equivFin (Active v)).symm
  have ho:= (mode_orthonormal v).comp e e.injective
  obtain ⟨U,f,hf,he⟩:=ICO.C6OrthogonalFrame.unitary_extension (fun i=>mode v (e i)) ho
  refine ⟨U,fun i=>f (e.symm i),hf.comp e.symm.injective,?_⟩
  intro i x
  simpa only [e.apply_symm_apply] using he (e.symm i) x

#print axioms residual_orthogonal
#print axioms adapted_unitary
end
end ICO.C6ResidualModes
