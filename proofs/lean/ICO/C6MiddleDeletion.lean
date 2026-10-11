import ICO.C6FockChoiceMeasurement

/-! The literal private middle of every shared-basis query satisfies the
forward-deletion estimate, including entanglement with the entire past. -/
namespace ICO.C6MiddleDeletion
open Matrix QIT ICO.C6ChoiceMeasurement ICO.C6FockChoiceMeasurement
  ICO.C6FockCompression ICO.C6FockCutoff ICO.C6LocalDeletion
  ICO.MHFockKnownOperation ICO.MHBoundedRecording ICO.MHFockSpace
  ICO.MHFockOracle ICO.MHBlockNorm ICO.MHRectangularAction
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option synthInstance.maxSize 1024
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def prepared {T:ℕ} (H:Matrix.unitaryGroup A ℂ)
    (v:InputCutoff (α:=A) T×(Bool×M)→ℂ) :
    (Bool×A)×(InputCutoff (α:=A) T×(Bool×M))→ℂ := fun z=>
  (Matrix.kronecker (fockQuery T (queryVector H z.1)) (1:CMatrix (Bool×M))*ᵥ
    coefficient H v z.1) z.2

theorem prepared_norm {T:ℕ} (H:Matrix.unitaryGroup A ℂ)
    (v:InputCutoff (α:=A) T×(Bool×M)→ℂ) :
    ‖WithLp.toLp 2 (prepared H v)‖=‖WithLp.toLp 2 v‖ := by
  have hM := rectAct_norm (ICO.MHFockKnownOperation.known T (middleQuery (M:=M) H))
    (ICO.MHFockKnownOperation.known_isometry T (middleQuery H) (middleQuery_isometry H))
    (WithLp.toLp 2 v)
  change ‖WithLp.toLp 2 (ICO.MHFockKnownOperation.known T (middleQuery H)*ᵥv)‖=
    ‖WithLp.toLp 2 v‖ at hM
  rw [actual_middle_branches] at hM
  have he := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (branchEquiv (A:=A) (M:=M) T).symm).norm_map
    (WithLp.toLp 2 (prepared H v))
  change ‖WithLp.toLp 2 (prepared H v ∘ branchEquiv T)‖=‖WithLp.toLp 2 (prepared H v)‖ at he
  exact he.symm.trans hM

theorem prepared_mass_le {T:ℕ} (H:Matrix.unitaryGroup A ℂ)
    (v:InputCutoff (α:=A) T×(Bool×M)→ℂ) (hv:‖WithLp.toLp 2 v‖≤1) :
    (∑p:Bool×A,∑i:InputCutoff (α:=A) T×(Bool×M),
      ‖(Matrix.kronecker (fockQuery T (queryVector H p)) (1:CMatrix (Bool×M))*ᵥ
        coefficient H v p) i‖^2)≤1 := by
  have hn := (prepared_norm H v).le.trans hv
  have hs : ‖WithLp.toLp 2 (prepared H v)‖^2≤1 := by nlinarith [norm_nonneg (WithLp.toLp 2 (prepared H v))]
  simpa only [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type,WithLp.ofLp_toLp,prepared] using hs

theorem coefficient_support {T s:ℕ} (H:Matrix.unitaryGroup A ℂ)
    (v:InputCutoff (α:=A) T×(Bool×M)→ℂ)
    (hv:∀i,¬ICO.MHFockProjection.grade i.1≤s+1→v i=0) :
    ∀p i,¬recordGrade i.1≤s+1→coefficient H v p i=0 := by
  intro p i hi
  unfold coefficient
  split_ifs
  · apply Finset.sum_eq_zero
    intro x hx
    rw [hv (withQuery i.1 x,i.2) (by exact hi),mul_zero]
  · rfl

theorem oracle_apply {T:ℕ} {N:Type} [Fintype N] [DecidableEq N]
    (O:CMatrix (InputCutoff (α:=A) T)) (v:InputCutoff (α:=A) T×N→ℂ)
    (i:InputCutoff (α:=A) T) (m:N) :
    (Matrix.kronecker O (1:CMatrix N)*ᵥv) (i,m)=∑j,O i j*v (j,m) := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem middle_error_branches {T:ℕ} (H:Matrix.unitaryGroup A ℂ)
    (v:InputCutoff (α:=A) T×(Bool×M)→ℂ) (O:CMatrix (InputCutoff (α:=A) T)) :
    (Matrix.kronecker O (1:CMatrix (Bool×((A×Bool)×M)))*ᵥ
      (ICO.MHFockKnownOperation.known T (middleQuery H)*ᵥv))=
    (fun z:(Bool×A)×(InputCutoff (α:=A) T×(Bool×M))=>
      (Matrix.kronecker O (1:CMatrix (Bool×M))*ᵥ
        (Matrix.kronecker (fockQuery T (queryVector H z.1)) (1:CMatrix (Bool×M))*ᵥ
          coefficient H v z.1)) z.2) ∘ branchEquiv T := by
  rw [actual_middle_branches]
  funext o
  rcases o with ⟨i,b,⟨j,c⟩,m⟩
  simp only [oracle_apply,Function.comp_apply,branchEquiv,Equiv.coe_fn_mk]

theorem actual_middle_deletion {s t T:ℕ} (hs:s+1≤T) (ht:t+1≤T) (hst:s≤t)
    (hd:t<Fintype.card A) (H:Matrix.unitaryGroup A ℂ)
    (v:InputCutoff (α:=A) T×(Bool×M)→ℂ) (hv:‖WithLp.toLp 2 v‖≤1)
    (hgrade:∀i,¬ICO.MHFockProjection.grade i.1≤s+1→v i=0) :
    ‖WithLp.toLp 2 ((Matrix.kronecker (fullOracle ht-leftOnFock ht)
      (1:CMatrix (Bool×((A×Bool)×M))))*ᵥ
      (ICO.MHFockKnownOperation.known T (middleQuery H)*ᵥv))‖≤
        Real.sqrt (2*(s+1:ℝ)/((Fintype.card A:ℝ)-s)) := by
  have hh := private_deletion_norm hs ht hst hd (queryVector H) (queryVector_normalized H)
    (coefficient H v) (coefficient_support H v hgrade) (prepared_mass_le H v hv)
  rw [middle_error_branches]
  let f : (Bool×A)×(InputCutoff (α:=A) T×(Bool×M))→ℂ := fun z=>
    (Matrix.kronecker (fullOracle ht-leftOnFock ht) (1:CMatrix (Bool×M))*ᵥ
      (Matrix.kronecker (fockQuery T (queryVector H z.1)) (1:CMatrix (Bool×M))*ᵥ
        coefficient H v z.1)) z.2
  have he := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (branchEquiv (A:=A) (M:=M) T).symm).norm_map
    (WithLp.toLp 2 f)
  change ‖WithLp.toLp 2 (f ∘ branchEquiv T)‖=‖WithLp.toLp 2 f‖ at he
  exact he.le.trans hh

#print axioms actual_middle_deletion
end
end ICO.C6MiddleDeletion
