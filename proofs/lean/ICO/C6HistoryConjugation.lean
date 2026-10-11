import ICO.C6ResidualModes
import ICO.C6CacheWeights
import ICO.MHProjectedMeanLoss

/-! Complex conjugation transports the actual history projection and fresh
residual. Right-label birth weights therefore equal left-label cache weights. -/
namespace ICO.C6HistoryConjugation
open QIT ICO.C6ResidualModes ICO.C6CacheSpanProjection ICO.C6CacheHistorySpan
  ICO.C6CacheWeights ICO.MHProtocolOverlap
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A]

def bar (x:EuclideanSpace ℂ A) : EuclideanSpace ℂ A :=
  WithLp.toLp 2 (fun i=>star (x i))

theorem bar_bar (x:EuclideanSpace ℂ A) : bar (bar x)=x := by
  ext i
  simp [bar]

theorem bar_sub (x y:EuclideanSpace ℂ A) : bar (x-y)=bar x-bar y := by
  ext i
  simp [bar]

theorem bar_inner (x y:EuclideanSpace ℂ A) : ⟪bar x,bar y⟫_ℂ=star ⟪x,y⟫_ℂ := by
  simp [bar,PiLp.inner_apply,RCLike.inner_apply,map_sum,map_mul,mul_comm]

theorem bar_norm (x:EuclideanSpace ℂ A) : ‖bar x‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq,bar]

theorem bar_mem_span {s:ℕ} (v:Fin s→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A)
    (hx:x∈historySpan v) : bar x∈historySpan (fun i=>bar (v i)) := by
  apply Submodule.span_induction (p:=fun x _=>bar x∈historySpan (fun i=>bar (v i))) _ _ _ _ hx
  · rintro _ ⟨i,rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  · have hz:bar (0:EuclideanSpace ℂ A)=0 := by ext i; simp [bar]
    rw [hz]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    have he:bar (x+y)=bar x+bar y := by ext i; simp [bar]
    rw [he]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    have he:bar (c • x)=star c • bar x := by ext i; simp [bar,mul_comm]
    rw [he]
    exact Submodule.smul_mem _ _ hx

theorem projected_mem {s:ℕ} (v:Fin s→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A) :
    act (historyProjection v) x∈historySpan v := by
  rw [←(history_realization v).1]
  exact projection_mem _ _ _

theorem projection_residual_orthogonal {s:ℕ} (v:Fin s→EuclideanSpace ℂ A)
    (x y:EuclideanSpace ℂ A) (hy:y∈historySpan v) :
    ⟪y,x-act (historyProjection v) x⟫_ℂ=0 := by
  have hf:act (historyProjection v) y=y := by
    apply projection_fixes
    rwa [(history_realization v).1]
  have hs:(historyProjection v).conjTranspose=historyProjection v :=
    (spanProjection_projection _ _).isSelfAdjoint.star_eq
  have he:=act_adjoint_inner (historyProjection v) y x
  rw [hf,hs] at he
  rw [inner_sub_right,he,sub_self]

theorem projection_bar {s:ℕ} (v:Fin s→EuclideanSpace ℂ A) (x:EuclideanSpace ℂ A) :
    act (historyProjection (fun i=>bar (v i))) (bar x)=bar (act (historyProjection v) x) := by
  let p:=act (historyProjection v) x
  let q:=act (historyProjection (fun i=>bar (v i))) (bar x)
  let z:=q-bar p
  have hp:bar p∈historySpan (fun i=>bar (v i)) := bar_mem_span v _ (projected_mem v x)
  have hq:q∈historySpan (fun i=>bar (v i)) := projected_mem _ _
  have hz:z∈historySpan (fun i=>bar (v i)) := Submodule.sub_mem _ hq hp
  have hbz:bar z∈historySpan v := by
    have hh:=bar_mem_span (fun i=>bar (v i)) z hz
    simpa only [bar_bar] using hh
  have h1:⟪z,bar x-bar p⟫_ℂ=0 := by
    have hh:=projection_residual_orthogonal v x (bar z) hbz
    have hc:=bar_inner (bar z) (x-p)
    rw [bar_bar,bar_sub] at hc
    change ⟪bar z,x-p⟫_ℂ=0 at hh
    rw [hh,star_zero] at hc
    exact hc
  have h2:⟪z,bar x-q⟫_ℂ=0 := projection_residual_orthogonal _ _ z hz
  have he:z=(bar x-bar p)-(bar x-q) := by dsimp only [z]; abel
  have hzero:z=0 := inner_self_eq_zero.mp (by
    conv_rhs => rw [←sub_self (0:ℂ)]
    calc
      ⟪z,z⟫_ℂ=⟪z,(bar x-bar p)-(bar x-q)⟫_ℂ := congrArg (fun w=>⟪z,w⟫_ℂ) he
      _ = 0-0 := by rw [inner_sub_right,h1,h2])
  exact sub_eq_zero.mp hzero

theorem residual_bar {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) :
    residual (fun j=>bar (v j)) i=bar (residual v i) := by
  unfold C6ResidualModes.residual
  change bar (v i)-act (historyProjection (fun j=>bar (prior v i j))) (bar (v i))=_
  rw [projection_bar,←bar_sub]

theorem residual_bar_norm {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q) :
    ‖residual (fun j=>bar (v j)) i‖=‖residual v i‖ := by
  rw [residual_bar,bar_norm]

variable [Nonempty A]

theorem projected_column_weight (U:Matrix.unitaryGroup A ℂ) (P:CMatrix A)
    (hP:IsStarProjection P) (j:A) :
    ‖act (1-P) (column U j)‖^2=overlapWeight U P j := by
  rw [ICO.MHProjectedMeanLoss.projection_norm_square _ hP.one_sub]
  unfold overlapWeight
  rw [Matrix.mul_assoc]
  congr 1
  change ⟪column U j,WithLp.toLp 2 ((1-P)*ᵥ(fun x=>(U:CMatrix A) x j))⟫_ℂ=_
  simp [column,PiLp.inner_apply,RCLike.inner_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.mulVec,dotProduct,Finset.mul_sum,
    Finset.sum_mul,mul_assoc,mul_left_comm,mul_comm]

theorem residual_weight {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q)
    (U:Matrix.unitaryGroup A ℂ) (j:A) (hj:v i=column U j) :
    ‖residual v i‖^2=overlapWeight U (historyProjection (prior v i)) j := by
  rw [residual_eq_projection,hj]
  exact projected_column_weight U _ (spanProjection_projection _ _) j

/-- The right-label residual uses conjugated history vectors; its weight
is exactly the left-label overlap weight used by the actual cache map. -/
theorem right_residual_weight {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q)
    (U:Matrix.unitaryGroup A ℂ) (j:A) (hj:v i=column U j) :
    ‖residual (fun k=>bar (v k)) i‖^2=overlapWeight U (historyProjection (prior v i)) j := by
  rw [residual_bar_norm,residual_weight v i U j hj]

#print axioms projection_bar
#print axioms residual_bar_norm
#print axioms right_residual_weight
end
end ICO.C6HistoryConjugation
