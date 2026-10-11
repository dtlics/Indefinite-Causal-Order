import ICO.C6ModeFockStep
import ICO.C6EncodingSupport
import ICO.C6FlagLeftSupport
import ICO.C6ModeFockVacuum

namespace ICO.C6RawDecoded
open Matrix QIT ICO.C6ModeFockStep ICO.C6ModeFockEncoding ICO.C6ModeFockVacuum
  ICO.C6DecodedHistory ICO.C6EncodingSupport ICO.C6FlagLeftSupport
  ICO.C6RawSupportedStage ICO.C6RawFlagSlices ICO.C6RawFlags
  ICO.C6AcceptedModes ICO.C6ActualAcceptedModes ICO.C6FlagCount ICO.C6RetainedHistory
  ICO.C6BosonicHistorySupport ICO.C6PairedTrajectory ICO.C6CacheDecode
  ICO.MHBoundedRecording ICO.MHFockTrajectory ICO.MHRectangularAction
  ICO.RecordingPurifiedProtocol ICO.RecordingCopyIdentity
open scoped Matrix BigOperators
noncomputable section
set_option maxHeartbeats 1900000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def smallInput (z:A×Public (A:=A) μ 0→ℂ) : A×(Bool×μ 0)→ℂ :=
  fun x=>z (x.1,(x.2.1,(PUnit.unit,x.2.2)))

def decodedInitial (z:A×Public (A:=A) μ 0→ℂ) : ImageCache (A:=A) 0 (Bool×μ 0)→ℂ :=
  basisEmbedding vacuumInput*ᵥsmallInput z

theorem slice_initial (T:ℕ) (z:A×Public (A:=A) μ 0→ℂ)
    (η:History (A×Bool) 0) :
    WithLp.ofLp (slice (T:=T) η (WithLp.toLp 2 (initial T z)))=
      initial T (smallInput z) := by
  cases η
  ext x
  rcases x with ⟨f,b,m⟩
  simp only [slice,WithLp.ofLp_toLp,initial,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,basisEmbedding,Matrix.submatrix_apply,Matrix.one_apply,
    initialEmbed,id_eq,Prod.mk.injEq,mul_ite,ite_mul,zero_mul]
  simp [History,smallInput,Prod.mk.injEq]

theorem raw_decoded {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ)
    (z:A×Public (A:=A) μ 0→ℂ) (n:ℕ) (hn:2*n≤t)
    (η:History (A×Bool) n) (κ:History Bool n) :
    WithLp.ofLp (slice η (rawFlagRun h H K (WithLp.toLp 2 (initial T z)) n κ))=
      encoding T (flagCount n κ) (flagCount n κ)
        (by have hc:=flagCount_le n κ; omega)
        (modes (rightVectors H n η) κ)*ᵥC6DecodedHistory.run H K (decodedInitial z) n η κ := by
  induction n with
  | zero=>
    rw [show rawFlagRun h H K (WithLp.toLp 2 (initial T z)) 0 κ=WithLp.toLp 2 (initial T z) from rfl,
      slice_initial]
    exact (encoding_initial T (by omega) _ (smallInput z)).symm
  | succ n ih=>
    obtain ⟨⟨j,b⟩,η⟩:=η
    obtain ⟨f,κ⟩:=κ
    have hc:=flagCount_le n κ
    have hi:=ih (by omega) η κ
    have hS:=congrArg WithLp.ofLp (rawFlagRun_history_slice h ht H K z n κ η)
    change Matrix.kronecker (historySupport (vectors H n η) T) (1:CMatrix (Bool×μ n))*ᵥ
      WithLp.ofLp (slice η (rawFlagRun h H K (WithLp.toLp 2 (initial T z)) n κ))=_ at hS
    have hZ:Matrix.kronecker (historyZero H n T η) (1:CMatrix (Bool×μ n))*ᵥ
      WithLp.ofLp (slice η (rawFlagRun h H K (WithLp.toLp 2 (initial T z)) n κ))=
      WithLp.ofLp (slice η (rawFlagRun h H K (WithLp.toLp 2 (initial T z)) n κ)) := by
      rw [hi,Matrix.mulVec_mulVec,historyZero_encoding]
    rw [flagRun_slice_succ]
    change branchStage h H K n η j b f*ᵥ
      WithLp.ofLp (slice η (rawFlagRun h H K (WithLp.toLp 2 (initial T z)) n κ))=_
    rw [branchStage_on_supported h H K n η j b f _ hS hZ,hi,
      Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      step_encoding h H K η κ (by omega) b f j,←Matrix.mulVec_mulVec]
    rfl

#print axioms raw_decoded
end
end ICO.C6RawDecoded
