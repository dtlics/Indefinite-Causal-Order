import ICO.C6MiddleDeletion
import ICO.C6SharedQuerySchedule
import ICO.MHFockRunIsometry

/-! One physical query pair on the literal Fock space, with inaccessible
choice/outcome history and arbitrary changing accessible memory. -/
namespace ICO.C6FockPairs
open Matrix QIT ICO.C6SharedStages ICO.C6FockChoiceMeasurement
  ICO.C6MiddleDeletion ICO.MHBoundedRecording ICO.MHFockKnownOperation
  ICO.MHFockSpace ICO.MHFockProjection ICO.MHFockAlgebra ICO.MHFockOracle ICO.MHFockTrajectory
  ICO.MHFockReachability ICO.MHBlockNorm ICO.MHRectangularAction ICO.RecordingPublicStep
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option synthInstance.maxSize 1024
variable {A M N E : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
  [Fintype E] [DecidableEq E]

def publicQuery (K:Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ) :
    Matrix (A×(Bool×(((A×Bool)×E)×N))) (A×(Bool×((A×Bool)×(E×M)))) ℂ :=
  (publicStep (h:=E) K).submatrix (regroup (((A×Bool)×E)×N)).symm
    (regroup ((A×Bool)×(E×M))).symm

theorem publicQuery_isometry (K:Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ)
    (hK:Kᴴ*K=1) : (publicQuery (E:=E) K)ᴴ*publicQuery (E:=E) K=1 := by
  simp only [publicQuery,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
    publicStep_isometry K hK,Matrix.submatrix_one_equiv]

def pair {T:ℕ} (F B:CMatrix (InputCutoff (α:=A) T)) (H:Matrix.unitaryGroup A ℂ)
    (K:Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ) :
    Matrix (InputCutoff (α:=A) T×(Bool×(((A×Bool)×E)×N)))
      (InputCutoff (α:=A) T×(Bool×(E×M))) ℂ :=
  ICO.MHFockKnownOperation.known T (publicQuery K)*
    Matrix.kronecker F (1:CMatrix (Bool×((A×Bool)×(E×M))))*
    ICO.MHFockKnownOperation.known T (middleQuery H)*
    Matrix.kronecker B (1:CMatrix (Bool×(E×M)))

theorem mul_norm_le_one {I J L:Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
    (X:Matrix I J ℂ) (Y:Matrix J L ℂ) (hX:‖X‖≤1) (hY:‖Y‖≤1) : ‖X*Y‖≤1 := by
  have hh := Matrix.l2_opNorm_mul X Y
  have hp : ‖X‖*‖Y‖≤1 := by nlinarith [norm_nonneg X,norm_nonneg Y]
  exact hh.trans hp

theorem pair_norm {T:ℕ} (F B:CMatrix (InputCutoff (α:=A) T)) (H:Matrix.unitaryGroup A ℂ)
    (K:Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ) (hK:Kᴴ*K=1) (hF:‖F‖≤1) (hB:‖B‖≤1) :
    ‖pair (E:=E) F B H K‖≤1 := by
  exact mul_norm_le_one _ _ (mul_norm_le_one _ _ (mul_norm_le_one _ _
    (ICO.MHFockKnownOperation.known_norm_le T _ (publicQuery_isometry K hK))
    ((tensor_identity_norm_le F).trans hF))
    (ICO.MHFockKnownOperation.known_norm_le T _ (middleQuery_isometry H)))
    ((tensor_identity_norm_le B).trans hB)

theorem pair_difference {T:ℕ} (F G B:CMatrix (InputCutoff (α:=A) T))
    (H:Matrix.unitaryGroup A ℂ) (K:Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ) :
    pair (E:=E) F B H K-pair (E:=E) G B H K=pair (E:=E) (F-G) B H K := by
  have hk : Matrix.kronecker (F-G) (1:CMatrix (Bool×((A×Bool)×(E×M))))=
      Matrix.kronecker F (1:CMatrix (Bool×((A×Bool)×(E×M))))-
      Matrix.kronecker G (1:CMatrix (Bool×((A×Bool)×(E×M)))) := by
    ext i j
    simp [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,sub_mul]
  simp only [pair,hk,Matrix.mul_sub,Matrix.sub_mul]

theorem inverse_norm {t T:ℕ} (ht:t+1≤T) (hd:t<Fintype.card A)
    (v:InputCutoff (α:=A) T×M→ℂ) (hv:‖WithLp.toLp 2 v‖≤1) :
    ‖WithLp.toLp 2 (Matrix.kronecker (fullOracle ht)ᴴ (1:CMatrix M)*ᵥv)‖≤1 := by
  have hn := (tensor_identity_norm_le (μ:=M) (fullOracle (α:=A) ht)ᴴ).trans
    (fullOracle_adjoint_norm_le ht hd)
  exact (rectAct_norm_le _ (WithLp.toLp 2 v)).trans
    (by nlinarith [norm_nonneg (WithLp.toLp 2 v),norm_nonneg (Matrix.kronecker (fullOracle (α:=A) ht)ᴴ (1:CMatrix M))])

theorem inverse_grade {s t T:ℕ} (ht:t+1≤T)
    (v:InputCutoff (α:=A) T×M→ℂ) (hv:Supported (fun i=>grade i.1≤s) v) :
    Supported (fun i=>grade i.1≤s+1) (Matrix.kronecker (fullOracle ht)ᴴ (1:CMatrix M)*ᵥv) := by
  refine ICO.MHFockTrajectory.mulVec_support
    (Matrix.kronecker (fullOracle (α:=A) ht)ᴴ (1:CMatrix M)) v
    (fun i:InputCutoff (α:=A) T×M=>grade i.1≤s)
    (fun i:InputCutoff (α:=A) T×M=>grade i.1≤s+1) hv ?_
  intro o i ho hi
  have hg := fullOracle_inverse_grade_step ht o.1 i.1 (oracle_memory_support _ o i ho)
  omega

theorem pair_deletion {s t T:ℕ} (hs:s+1≤T) (ht:t+1≤T) (hst:s≤t)
    (hd:t<Fintype.card A) (H:Matrix.unitaryGroup A ℂ)
    (K:Matrix ((A×Bool)×N) ((A×Bool)×M) ℂ) (hK:Kᴴ*K=1)
    (v:InputCutoff (α:=A) T×(Bool×(E×M))→ℂ) (hv:‖WithLp.toLp 2 v‖≤1)
    (hgrade:Supported (fun i=>grade i.1≤s) v) :
    ‖WithLp.toLp 2 ((pair (E:=E) (fullOracle ht) (fullOracle ht)ᴴ H K-
      pair (E:=E) (leftOnFock ht) (fullOracle ht)ᴴ H K)*ᵥv)‖≤
        Real.sqrt (2*(s+1:ℝ)/((Fintype.card A:ℝ)-s)) := by
  let w := Matrix.kronecker (fullOracle ht)ᴴ (1:CMatrix (Bool×(E×M)))*ᵥv
  have hw := inverse_norm ht hd v hv
  have hgw := inverse_grade ht v hgrade
  have he := actual_middle_deletion hs ht hst hd H w hw (fun i hi=>by
    by_contra hn
    exact hi (hgw i hn))
  rw [pair_difference]
  simp only [pair,←Matrix.mulVec_mulVec]
  change ‖rectAct (ICO.MHFockKnownOperation.known T (publicQuery K))
    (WithLp.toLp 2 (Matrix.kronecker (fullOracle ht-leftOnFock ht)
      (1:CMatrix (Bool×((A×Bool)×(E×M))))*ᵥ
      (ICO.MHFockKnownOperation.known T (middleQuery H)*ᵥw)))‖≤_
  rw [rectAct_norm _ (ICO.MHFockKnownOperation.known_isometry T _ (publicQuery_isometry K hK))]
  exact he

#print axioms pair_deletion
end
end ICO.C6FockPairs
