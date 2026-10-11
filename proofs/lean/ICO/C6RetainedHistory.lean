import ICO.C6NativePolar
import ICO.C6BosonicHistorySupport
import ICO.C6ResidualModes

/-! The history controlling fresh recording contains exactly the privately
copied box choice and measurement outcome of the physical schedule. -/
namespace ICO.C6RetainedHistory
open Matrix QIT ICO.C6PairedTrajectory ICO.C6ChoiceMeasurement ICO.C6PolarFock
  ICO.C6BosonicFreshContraction ICO.C6BosonicFockRotated ICO.C6BosonicHistorySupport
  ICO.C6CacheSpanProjection ICO.RecordingPurifiedProtocol ICO.MHBoundedRecording
  ICO.MHProfileBlocks ICO.MHBlockNorm ICO.MHFockKnownOperation
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def vectors (H:Matrix.unitaryGroup A ℂ) : (i:ℕ)→History (A×Bool) i→Fin i→EuclideanSpace ℂ A
  | 0,_=>Fin.elim0
  | i+1,η=>Fin.snoc (vectors H i η.2) (WithLp.toLp 2 (queryVector H (η.1.2,η.1.1)))

theorem vectors_snoc (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (η:History (A×Bool) i) (j:A) (b:Bool) :
    vectors H (i+1) ((j,b),η)=Fin.snoc (vectors H i η) (WithLp.toLp 2 (queryVector H (b,j))) := rfl

def inverseBlock {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ) (i:ℕ)
    (η:History (A×Bool) i) : CMatrix (InputCutoff (α:=A) T) :=
  freshInverse (polarLeftOnFock h) (polarRightOnFock h)
    (rotatedFresh (historyUnitary (vectors H i η)) (historyIndices (vectors H i η)) T)*
      historySupport (vectors H i η) T

theorem inverseBlock_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ) (i:ℕ) (η:History (A×Bool) i) :
    ‖inverseBlock h H i η‖≤1 := by
  rw [inverseBlock,historySupport_rotated]
  exact rotated_freshInverse_contraction _ _ h ht

def historyFirst (T i:ℕ) (M:Type) :
    (InputCutoff (α:=A) T×(Bool×(History (A×Bool) i×M)))≃
      ((InputCutoff (α:=A) T×(Bool×M))×History (A×Bool) i) where
  toFun x:=((x.1,(x.2.1,x.2.2.2)),x.2.2.1)
  invFun x:=(x.1.1,(x.1.2.1,(x.2,x.1.2.2)))
  left_inv _:=rfl
  right_inv _:=rfl

def controlled {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    (F:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T)) :
    CMatrix (InputCutoff (α:=A) T×(Bool×(History (A×Bool) i×M))) :=
  (Matrix.blockDiagonal (fun η=>Matrix.kronecker (F η) (1:CMatrix (Bool×M)))).submatrix
    (historyFirst T i M) (historyFirst T i M)

theorem controlled_norm {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    (F:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T)) (hF:∀η,‖F η‖≤1) :
    ‖controlled (M:=M) F‖≤1 := by
  apply (reindex_norm_le _ _).trans
  have hb:=blockDiagonal_norm_le (fun η=>Matrix.kronecker (F η) (1:CMatrix (Bool×M)))
    1 (by norm_num) (fun η=>by simpa using (tensor_identity_norm_le (μ:=Bool×M) (F η)).trans (hF η))
  simpa using hb

theorem controlled_entry {T i:ℕ} {M:Type} [Fintype M] [DecidableEq M]
    (F:History (A×Bool) i→CMatrix (InputCutoff (α:=A) T))
    (o j:InputCutoff (α:=A) T×(Bool×(History (A×Bool) i×M))) :
    controlled F o j=if o.2=j.2 then F o.2.2.1 o.1 j.1 else 0 := by
  simp only [controlled,Matrix.submatrix_apply,historyFirst,Equiv.coe_fn_mk,
    Matrix.blockDiagonal_apply',Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  by_cases h:o.2=j.2
  · have hb:=congrArg Prod.fst h
    have hh:=congrArg (fun x:Bool×(History (A×Bool) i×M)=>x.2.1) h
    have hm:=congrArg (fun x:Bool×(History (A×Bool) i×M)=>x.2.2) h
    simp [h,hb,hh,hm]
  · by_cases hh:o.2.2.1=j.2.2.1 <;>
      by_cases hb:o.2.1=j.2.1 <;> by_cases hm:o.2.2.2=j.2.2.2 <;>
      simp_all [Prod.ext_iff]

variable {μ:ℕ→Type} [∀i,Fintype (μ i)] [∀i,DecidableEq (μ i)]

def freshStage {t T:ℕ} (h:t+1≤T) (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (i:ℕ) :
    Matrix (InputCutoff (α:=A) T×Public (A:=A) μ (i+1))
      (InputCutoff (α:=A) T×Public (A:=A) μ i) ℂ :=
  publicStage T K i*Matrix.kronecker (polarLeftOnFock h) (1:CMatrix (Middle (A:=A) μ i))*
    middleStage T H i*controlled (M:=μ i) (inverseBlock h H i)

theorem freshStage_norm {t T:ℕ} (h:t+1≤T) (ht:t<Fintype.card A)
    (H:Matrix.unitaryGroup A ℂ)
    (K:∀i,Matrix ((A×Bool)×μ (i+1)) ((A×Bool)×μ i) ℂ) (hK:∀i,(K i)ᴴ*K i=1) (i:ℕ) :
    ‖freshStage h H K i‖≤1 := by
  apply ICO.C6FockPairs.mul_norm_le_one
  · apply ICO.C6FockPairs.mul_norm_le_one
    · apply ICO.C6FockPairs.mul_norm_le_one
      · exact publicStage_norm T K hK i
      · exact (tensor_identity_norm_le _).trans (polarLeftOnFock_norm_le h ht)
    · exact middleStage_norm T H i
  · exact controlled_norm _ (inverseBlock_norm h ht H i)

#print axioms freshStage_norm
#print axioms vectors_snoc
end
end ICO.C6RetainedHistory
