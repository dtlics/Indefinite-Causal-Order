import ICO.MHDecompressionRotation
import ICO.MHDecompressionErasure
import ICO.MHRotatedTrajectory

/-! The actual Haar-rotated physical query and partial recording query have
precisely the mass-defect local error, with arbitrary entangled memory. -/
namespace ICO.MHRotatedDecompressionDefect
open Matrix QIT ICO.MHDecompressionKnown ICO.MHFockDecompressionDefect ICO.MHDecompressionRotation
  ICO.MHDecompressionDefect ICO.MHRectangularAction ICO.MHDecompressionErasure
  ICO.MHBoundedRecording ICO.MHFockSpace ICO.MHFockRotation ICO.MHWEmbedding
  ICO.MHWDomainProjection ICO.MHTernaryCompression ICO.MHPurifiedOracle
  ICO.MHRotatedTrajectory ICO.MHFockTrajectory ICO.MHFockKnownOperation
  ICO.MHFockSupportProjection ICO.MHFockLabels ICO.MHBijectionProfiles
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
variable {A μ : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype μ] [DecidableEq μ]

def physicalChoice (inverse : Bool) : Matrix.unitaryGroup (A×Environment A) ℂ :=
  if inverse then queryUnitary⁻¹ else queryUnitary

def physicalRotated (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool) :
    Matrix.unitaryGroup (A×Environment A) ℂ :=
  spectatorUnitary (after C D inverse) (Environment A)*physicalChoice inverse*
    spectatorUnitary (before C D inverse) (Environment A)

theorem query_preserves_bij (C : Matrix.unitaryGroup A ℂ) (T : ℕ)
    (x : InputCutoff (α := A) T×μ→ℂ)
    (hx : Matrix.kronecker (bijProjection T) (1 : CMatrix μ)*ᵥx=x) :
    Matrix.kronecker (bijProjection T) (1 : CMatrix μ)*ᵥ
      (Matrix.kronecker (fockQuery C T : CMatrix (InputCutoff (α := A) T)) (1 : CMatrix μ)*ᵥx)=
      Matrix.kronecker (fockQuery C T : CMatrix (InputCutoff (α := A) T)) (1 : CMatrix μ)*ᵥx := by
  apply bij_fixed _
  have hs : Supported (fun i : InputCutoff (α := A) T×μ =>
      BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2) x := by
    classical
    intro i hi
    by_contra hnot
    have hh := congrFun hx i
    simp only [bijProjection,Matrix.kronecker,← Matrix.diagonal_one,Matrix.diagonal_kronecker_diagonal,
      Matrix.mulVec_diagonal,mul_one,if_neg hnot,zero_mul] at hh
    exact hi hh.symm
  apply mulVec_support (Matrix.kronecker (fockQuery C T : CMatrix (InputCutoff (α := A) T)) (1 : CMatrix μ)) x
    (fun i => BijMultiset (fockLabel i.1).2.1 (fockLabel i.1).2.2)
    (fun o => BijMultiset (fockLabel o.1).2.1 (fockLabel o.1).2.2) hs
  intro o i hi hb
  exact (query_bij C T o.1 i.1 (oracle_memory_support _ o i hi)).mpr hb

theorem rotated_memory_defect {T : ℕ} (hT : 2*Fintype.card (A×A)≤T)
    (C D : Matrix.unitaryGroup A ℂ) (inverse : Bool)
    (x : EuclideanSpace ℂ (InputCutoff (α := A) T×μ))
    (hx : rectAct (Matrix.kronecker (bijProjection T) (1 : CMatrix μ)) x=x) (hn : ‖x‖≤1) :
    ‖rectAct (Matrix.kronecker (physicalRotated C D inverse : CMatrix (A×Environment A)) (1 : CMatrix μ))
      (rectAct (memoryD hT μ) x)-
      rectAct (memoryD hT μ) (rectAct (Matrix.kronecker (rotatedW hT C D inverse) (1 : CMatrix μ)) x)‖^2 ≤
      1-‖rectAct (Matrix.kronecker (rotatedW hT C D inverse) (1 : CMatrix μ)) x‖^2 := by
  let Vpre := spectatorUnitary (fockQuery (before C D inverse) T) μ
  let Vpost := spectatorUnitary (fockQuery (after C D inverse) T) μ
  let Upre := spectatorUnitary (spectatorUnitary (before C D inverse) (Environment A)) μ
  let Upost := spectatorUnitary (spectatorUnitary (after C D inverse) (Environment A)) μ
  let U := spectatorUnitary (physicalChoice (A := A) inverse) μ
  let W := Matrix.kronecker (Wchoice hT inverse) (1 : CMatrix μ)
  have hc : (Upre : CMatrix ((A×Environment A)×μ))*memoryD hT μ=
      memoryD hT μ*(Vpre : CMatrix (InputCutoff (α := A) T×μ)) := (memoryD_query (before C D inverse) hT).symm
  have hd : (Upost : CMatrix ((A×Environment A)×μ))*memoryD hT μ=
      memoryD hT μ*(Vpost : CMatrix (InputCutoff (α := A) T×μ)) := (memoryD_query (after C D inverse) hT).symm
  have hrot : Matrix.kronecker (rotatedW hT C D inverse) (1 : CMatrix μ)=
      (Vpost : CMatrix (InputCutoff (α := A) T×μ))*W*(Vpre : CMatrix (InputCutoff (α := A) T×μ)) := by
    simp only [rotatedW,Vpost,Vpre,W,spectatorUnitary,Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.mul_one]
  have hphy : Matrix.kronecker (physicalRotated C D inverse : CMatrix (A×Environment A)) (1 : CMatrix μ)=
      (Upost : CMatrix ((A×Environment A)×μ))*(U : CMatrix ((A×Environment A)×μ))*(Upre : CMatrix ((A×Environment A)×μ)) := by
    simp only [physicalRotated,Matrix.UnitaryGroup.mul_val,Upost,U,Upre,spectatorUnitary,
      Matrix.kronecker,← Matrix.mul_kronecker_mul,Matrix.mul_one]
  have he : ((Upost : CMatrix ((A×Environment A)×μ))*(U : CMatrix ((A×Environment A)×μ))*(Upre : CMatrix ((A×Environment A)×μ)))*memoryD hT μ-
      memoryD hT μ*((Vpost : CMatrix (InputCutoff (α := A) T×μ))*W*(Vpre : CMatrix (InputCutoff (α := A) T×μ)))=
      (Upost : CMatrix ((A×Environment A)×μ))*((U : CMatrix ((A×Environment A)×μ))*memoryD hT μ-memoryD hT μ*W)*
        (Vpre : CMatrix (InputCutoff (α := A) T×μ)) := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    rw [hc]
    have hdd : memoryD hT μ*((Vpost : CMatrix (InputCutoff (α := A) T×μ))*(W*(Vpre : CMatrix (InputCutoff (α := A) T×μ))))=
        (Upost : CMatrix ((A×Environment A)×μ))*(memoryD hT μ*(W*(Vpre : CMatrix (InputCutoff (α := A) T×μ)))) := by
      rw [← Matrix.mul_assoc,← hd,Matrix.mul_assoc]
    rw [hdd]
  rw [hrot,hphy,← rectAct_mul,← rectAct_mul,← rectAct_matrix_sub,he,rectAct_mul,rectAct_mul,
    rectAct_norm _ Upost.property.1]
  rw [rectAct_mul,rectAct_mul,rectAct_norm _ Vpost.property.1]
  have hxn : ‖rectAct (Vpre : CMatrix (InputCutoff (α := A) T×μ)) x‖≤1 := by
    rw [rectAct_norm _ Vpre.property.1]
    exact hn
  have hxb : rectAct (Matrix.kronecker (bijProjection T) (1 : CMatrix μ))
      (rectAct (Vpre : CMatrix (InputCutoff (α := A) T×μ)) x)=rectAct (Vpre : CMatrix (InputCutoff (α := A) T×μ)) x := by
    apply WithLp.ofLp_injective 2
    exact query_preserves_bij (before C D inverse) T (WithLp.ofLp x) (congrArg WithLp.ofLp hx)
  have hh := memory_defect inverse hT (rectAct (Vpre : CMatrix (InputCutoff (α := A) T×μ)) x) hxb hxn
  rw [rectAct_matrix_sub,rectAct_mul,rectAct_mul]
  cases inverse <;> simpa only [U,W,physicalChoice,Wchoice,Bool.false_eq_true,if_false,if_true,spectatorUnitary,Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose,memoryD] using hh

#print axioms rotated_memory_defect
end
end ICO.MHRotatedDecompressionDefect