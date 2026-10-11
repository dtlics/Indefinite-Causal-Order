import ICO.ProtocolLudersTrajectory
import ICO.RecordingVaryingTranscript

namespace ICO.ProtocolRecordingTrajectory
open Matrix QIT ICO.SequentialIsometry ICO.RecordingHistory
  ICO.RecordingPurifiedProtocol ICO.RecordingPublicStep ICO.RecordingProcess
  ICO.RecordingOperatorSupport ICO.PathRecordingSupport ICO.RecordingRetainedProcess
  ICO.RecordingOracleAlgebra ICO.RecordingCopyIdentity
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
universe u
set_option maxHeartbeats 2000000
variable {A M O : Type u} [Fintype A] [DecidableEq A]
  [Fintype M] [DecidableEq M] [Fintype O] [DecidableEq O]

def initial (v : A×M → ℂ) : Basis A×(History A 0×M) → ℂ :=
  fun i => if i.1.2.1=∅ ∧ i.1.2.2=∅ then v (i.1.1,i.2.2) else 0

def emptyEmbed : A×M → Basis A×(History A 0×M) :=
  fun i => ((i.1,∅,∅),(PUnit.unit,i.2))

theorem emptyEmbed_injective : Function.Injective (emptyEmbed (A:=A) (M:=M)) := by
  intro i j h
  exact Prod.ext (congrArg (fun x => x.1.1) h) (congrArg (fun x => x.2.2) h)

theorem initial_eq_embedding (v : A×M → ℂ) :
    initial v = basisEmbedding emptyEmbed *ᵥ v := by
  ext i
  rcases i with ⟨⟨a,l,r⟩,⟨h,m⟩⟩
  cases h
  simp [initial,basisEmbedding,emptyEmbed,Matrix.mulVec,dotProduct,
    Matrix.submatrix_apply,Matrix.one_apply,Fintype.sum_prod_type,Prod.mk.injEq,
    ite_and,ite_mul]

theorem initial_support (v : A×M → ℂ) (i) (hi : initial v i ≠ 0) :
    i.1.2.1=∅ ∧ i.1.2.2=∅ := by
  by_contra h
  exact hi (if_neg h)

theorem initial_norm_le (v : A×M → ℂ) :
    ‖WithLp.toLp 2 (initial v)‖ ≤ ‖WithLp.toLp 2 v‖ := by
  rw [initial_eq_embedding]
  have hJ := isometry_matrix_norm_le (basisEmbedding (emptyEmbed (A:=A) (M:=M)))
    (basisEmbedding_gram (emptyEmbed (A:=A) (M:=M)) emptyEmbed_injective)
  have hn := Matrix.l2_opNorm_mulVec (basisEmbedding emptyEmbed) (WithLp.toLp 2 v)
  exact hn.trans (by nlinarith [norm_nonneg (WithLp.toLp 2 v)])

theorem initial_visible (v : A×M → ℂ) : visible 0 (initial v)=rankOneMatrix v := by
  ext x y
  rcases x with ⟨a,m⟩
  rcases y with ⟨b,n⟩
  simp [visible,reduced,visibleMap_apply,eraseHistory_apply,rankOneMatrix_apply,
    initial,Fintype.sum_prod_type,apply_ite,ite_mul,mul_ite]
  simp [History,ite_and]

theorem initial_trace (v : A×M → ℂ) :
    (rankOneMatrix (initial v)).trace=(rankOneMatrix v).trace := by
  rw [← initial_visible v,visible,visibleMap_trace,reduced]
  exact (eraseHistory.tracePreserving _).symm

/-- Actual finite recording evolution with the same public schedule as the
physical purified Lüders circuit. G=forwardRecording gives V; G=leftInsertion
gives the growing modified process used in the depolarizing comparison. -/
def run {q : ℕ} (tail : Protocol A (A×M) O q) (G : CMatrix (Basis A))
    (v : A×M → ℂ) : (t : ℕ) → Basis A×(History A t×tail.tailMemory t) → ℂ
  | 0 => initial v
  | t+1 => stepMatrix G (publicStep (h:=History A t) (tail.tailKnown t)) *ᵥ run tail G v t

theorem run_recurrence {q : ℕ} (tail : Protocol A (A×M) O q) (G : CMatrix (Basis A))
    (v : A×M → ℂ) (t : ℕ) :
    run tail G v (t+1) =
      stepMatrix G (publicStep (h:=History A t) (tail.tailKnown t)) *ᵥ run tail G v t := rfl

theorem run_norm_le {q : ℕ} (tail : Protocol A (A×M) O q) (G : CMatrix (Basis A))
    (hG : IsStarProjection (G.conjTranspose*G)) (v : A×M → ℂ)
    (hv : ‖WithLp.toLp 2 v‖≤1) (t : ℕ) : ‖WithLp.toLp 2 (run tail G v t)‖≤1 := by
  apply process_norm_le (fun t => History A t×tail.tailMemory t) (run tail G v) G hG
    (fun t => publicStep (h:=History A t) (tail.tailKnown t))
    (fun t => publicStep_isometry _ (tail.tailKnown_isometry t))
    ((initial_norm_le v).trans hv) (fun t => rfl) t

#print axioms run_norm_le
#print axioms initial_norm_le
#print axioms initial_visible
#print axioms initial_trace
end
end ICO.ProtocolRecordingTrajectory
