import ICO.C6FockPairs
import ICO.C6PolarTrajectory

namespace ICO.C6PairedTrajectory
open Matrix QIT ICO.C6FockPairs ICO.C6FockChoiceMeasurement ICO.C6MatrixTrajectory
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockProjection ICO.MHFockAlgebra
  ICO.MHFockOracle ICO.MHFockReachability ICO.MHFockTrajectory ICO.MHFockKnownOperation
  ICO.MHRectangularAction ICO.RecordingPurifiedProtocol
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
variable (μ:ℕ→Type) [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

abbrev Public (i:ℕ) := Bool×(History (A×Bool) i×μ i)
abbrev Middle (i:ℕ) := Bool×((A×Bool)×(History (A×Bool) i×μ i))

variable {μ}
def fullStage {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    Matrix (InputCutoff (α:=A) T×Public (A:=A) μ (i+1)) (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ :=
  pair (E:=History (A×Bool) i) (fullOracle h) (fullOracle h)ᴴ H (K i)

def deletedStage {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    Matrix (InputCutoff (α:=A) T×Public (A:=A) μ (i+1)) (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ :=
  pair (E:=History (A×Bool) i) (leftOnFock h) (fullOracle h)ᴴ H (K i)

def middleStage (T:ℕ) (H:Matrix.unitaryGroup A ℂ) (i:ℕ) :
    Matrix (InputCutoff (α:=A) T×Middle (A:=A) μ i) (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ :=
  ICO.MHFockKnownOperation.known T (middleQuery H)

def publicStage (T:ℕ) (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    Matrix (InputCutoff (α:=A) T×Public (A:=A) μ (i+1)) (InputCutoff (α:=A) T×Middle (A:=A) μ i) ℂ :=
  ICO.MHFockKnownOperation.known T (publicQuery (E:=History (A×Bool) i) (K i))

theorem middleStage_norm (T:ℕ) (H:Matrix.unitaryGroup A ℂ) (i:ℕ) :
    ‖middleStage (μ:=μ) T H i‖≤1 :=
  ICO.MHFockKnownOperation.known_norm_le T _ (middleQuery_isometry H)

theorem publicStage_norm (T:ℕ) (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (hK:∀i,(K i)ᴴ*K i=1) (i:ℕ) : ‖publicStage T K i‖≤1 :=
  ICO.MHFockKnownOperation.known_norm_le T _ (publicQuery_isometry (K i) (hK i))

theorem fullStage_norm {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (hK:∀i,(K i)ᴴ*K i=1) (i:ℕ) : ‖fullStage h H K i‖≤1 :=
  pair_norm _ _ H (K i) (hK i) (fullOracle_norm_le h hd) (fullOracle_adjoint_norm_le h hd)

theorem deletedStage_norm {t T:ℕ} (h:t+1≤T) (hd:t<Fintype.card A) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (hK:∀i,(K i)ᴴ*K i=1) (i:ℕ) : ‖deletedStage h H K i‖≤1 :=
  pair_norm _ _ H (K i) (hK i) (leftOnFock_norm_le h hd) (fullOracle_adjoint_norm_le h hd)

theorem deletedStage_eq_oldStage {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    deletedStage h H K i=ICO.C6PolarTrajectory.oldStage h (middleStage T H) (publicStage T K) i := by
  simp only [deletedStage,pair,ICO.C6PolarTrajectory.oldStage,ICO.C6PolarReplacement.oldPair,
    middleStage,publicStage,Matrix.mul_assoc]
  rfl

theorem known_support {T s:ℕ} {M N:Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    (K:Matrix (A×N) (A×M) ℂ) (v:InputCutoff (α:=A) T×M→ℂ)
    (hv:Supported (fun i=>grade i.1≤s) v) :
    Supported (fun i=>grade i.1≤s) (ICO.MHFockKnownOperation.known T K*ᵥv) := by
  refine ICO.MHFockTrajectory.mulVec_support (ICO.MHFockKnownOperation.known T K) v
    (fun i:InputCutoff (α:=A) T×M=>grade i.1≤s)
    (fun i:InputCutoff (α:=A) T×N=>grade i.1≤s) hv ?_
  intro o i ho hi
  rwa [known_grade T K o i ho]

theorem forward_grade {s t T:ℕ} {M:Type} [Fintype M] [DecidableEq M] (h:t+1≤T)
    (v:InputCutoff (α:=A) T×M→ℂ) (hv:Supported (fun i=>grade i.1≤s) v) :
    Supported (fun i=>grade i.1≤s+1) (Matrix.kronecker (fullOracle h) (1:CMatrix M)*ᵥv) := by
  refine ICO.MHFockTrajectory.mulVec_support
    (Matrix.kronecker (fullOracle (α:=A) h) (1:CMatrix M)) v
    (fun i:InputCutoff (α:=A) T×M=>grade i.1≤s)
    (fun i:InputCutoff (α:=A) T×M=>grade i.1≤s+1) hv ?_
  intro o i ho hi
  have hg := fullOracle_grade_step h o.1 i.1 (oracle_memory_support _ o i ho)
  omega

theorem fullStage_grade {s t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ)
    (v:InputCutoff (α:=A) T×Public (A:=A) μ i→ℂ)
    (hv:Supported (fun j=>grade j.1≤s) v) :
    Supported (fun j=>grade j.1≤s+2) (fullStage h H K i*ᵥv) := by
  simp only [fullStage,pair,←Matrix.mulVec_mulVec]
  have h1 := inverse_grade h v hv
  have h2 := known_support (middleQuery H) _ h1
  have h3 := forward_grade h _ h2
  have h4 := known_support (publicQuery (E:=History (A×Bool) i) (K i)) _ h3
  simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc,Nat.add_assoc] using h4

theorem fullRun_grade {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:EuclideanSpace ℂ (InputCutoff (α:=A) T×Public (A:=A) μ 0))
    (hz:Supported (fun i=>grade i.1≤0) (WithLp.ofLp z)) (n:ℕ) :
    Supported (fun i=>grade i.1≤2*n)
      (WithLp.ofLp (ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K) z n)) := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    change Supported (fun i=>grade i.1≤2*(n+1))
      (fullStage h H K n*ᵥWithLp.ofLp (ICO.C6MatrixTrajectory.run (H:=fun i=>InputCutoff (α:=A) T×Public (A:=A) μ i) (fullStage h H K) z n))
    simpa only [show 2*(n+1)=2*n+2 by omega] using fullStage_grade h H K n _ ih

#print axioms fullRun_grade
end
end ICO.C6PairedTrajectory
