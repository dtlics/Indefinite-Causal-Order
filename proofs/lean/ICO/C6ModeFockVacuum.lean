import ICO.C6ModeFockEncoding
import ICO.MHFockTrajectory

/-! The empty accepted history is the actual empty two-record Fock state,
including arbitrary initial entanglement with the learner's memory. -/
namespace ICO.C6ModeFockVacuum
open QIT Matrix ICO.C6ModeFockEncoding ICO.C6TwoFockVisible
  ICO.C6TwoFockSector ICO.C6CacheDecode ICO.C6RightImageErasure
  ICO.C6ModeEncoding ICO.MHFockTrajectory ICO.MHFockLabels
  ICO.MHBoundedRecording ICO.RecordingCopyIdentity ICO.RecordingPureCorrespondence
  ICO.RecordingMultisetBridge ICO.MHOccupationCounts ICO.MHEmbeddingProjector
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def emptyProfile : TensorPowerProfile (A×A) 0 :=
  (occupationMultiset 0).symm (Sym.mk 0 rfl)

theorem profile_zero_unique (p q : TensorPowerProfile (A×A) 0) : p=q := by
  apply Subtype.ext
  funext z
  have hp := tensorPowerTypeProfile_sum_of_mem_profiles 0 p.property
  have hq := tensorPowerTypeProfile_sum_of_mem_profiles 0 q.property
  have hpz := Finset.single_le_sum (fun y _=>Nat.zero_le (p.val y)) (Finset.mem_univ z)
  have hqz := Finset.single_le_sum (fun y _=>Nat.zero_le (q.val y)) (Finset.mem_univ z)
  rw [hp] at hpz
  rw [hq] at hqz
  exact (Nat.eq_zero_of_le_zero hpz).trans (Nat.eq_zero_of_le_zero hqz).symm

def emptyImages : Fin 0→A := fun i=>i.elim0

def vacuumCache (z : A×M) : Cache (A:=A) (M:=M) 0 :=
  ((z.1,emptyProfile),z.2)

def vacuumInput (z : A×M) : Cache (A:=A) (M:=M) 0×(Fin 0→A) :=
  (vacuumCache z,emptyImages)

def vacuumRecords (z : A×M) : Cache (A:=A) (M:=M) 0×TensorPowerProfile (A×A) 0 :=
  (vacuumCache z,emptyProfile)

theorem directEncoding_empty (v : Fin 0→EuclideanSpace ℂ A)
    (p : TensorPowerProfile (A×A) 0) (images : Fin 0→A) :
    directEncoding v p images=1 := by
  simp only [directEncoding,directProduct,encode,basisEmbedding,Matrix.submatrix_apply,
    Matrix.one_apply,id_eq,
    if_pos (profile_zero_unique p (profile (fun i:Fin 0=>i.elim0) images))]

theorem empty_private_embedding (v : Fin 0→EuclideanSpace ℂ A) :
    Matrix.kronecker (1:CMatrix (Cache (A:=A) (M:=M) 0)) (directEncoding v)*
      basisEmbedding vacuumInput=basisEmbedding (vacuumRecords (A:=A) (M:=M)) := by
  rw [mul_basisEmbedding]
  ext x z
  have hp : x.2=emptyProfile := profile_zero_unique _ _
  have he : x=vacuumRecords z ↔ x.1=vacuumCache z := by
    constructor
    · exact fun h=>congrArg Prod.fst h
    · intro h; exact Prod.ext h hp
  simp only [Matrix.submatrix_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
    Matrix.one_apply,vacuumInput,directEncoding_empty,mul_one,basisEmbedding,id_eq,he]

theorem vacuumRecords_initial (T : ℕ) (h : 0+0≤T) :
    memoryEmbed (A:=A) (M:=M) T 0 0 h ∘ vacuumRecords=initialEmbed T := by
  funext z
  apply Prod.ext
  · apply fockLabel_injective T
    simp only [Function.comp_apply,memoryEmbed,vacuumRecords,vacuumCache,
      sectorEmbed,fockLabel,emptyProfile,Equiv.apply_symm_apply,empty_label,initialEmbed]
    rfl
  · rfl

theorem encoding_initial_matrix (T : ℕ) (h : 0+0≤T)
    (v : Fin 0→EuclideanSpace ℂ A) :
    encoding (M:=M) T 0 0 h v*basisEmbedding vacuumInput=
      basisEmbedding (initialEmbed (α:=A) T (μ:=M)) := by
  rw [encoding,Matrix.mul_assoc,empty_private_embedding,memoryJ,
    basisEmbedding_mul,vacuumRecords_initial]

theorem encoding_initial (T : ℕ) (h : 0+0≤T)
    (v : Fin 0→EuclideanSpace ℂ A) (z : A×M→ℂ) :
    encoding (M:=M) T 0 0 h v*ᵥ(basisEmbedding vacuumInput*ᵥz)=initial T z := by
  rw [Matrix.mulVec_mulVec,encoding_initial_matrix]
  rfl

theorem vacuumInput_vector (z : A×M→ℂ) :
    basisEmbedding vacuumInput*ᵥz=
      fun x : Cache (A:=A) (M:=M) 0×(Fin 0→A)=>(basisEmbedding vacuumCache*ᵥz) x.1 := by
  funext x
  have hx : x.2=emptyImages := by funext i; exact i.elim0
  have he (y : A×M) : x=vacuumInput y ↔ x.1=vacuumCache y := by
    constructor
    · exact fun h=>congrArg Prod.fst h
    · exact fun h=>Prod.ext h hx
  simp only [Matrix.mulVec,basisEmbedding,Matrix.submatrix_apply,
    Matrix.one_apply,id_eq,he]
  rfl

theorem vacuumInput_erasure (z : A×M→ℂ) :
    partialTraceB (rankOneMatrix (basisEmbedding vacuumInput*ᵥz))=
      rankOneMatrix (basisEmbedding (vacuumCache (A:=A) (M:=M))*ᵥz) := by
  rw [vacuumInput_vector]
  ext a b
  simp only [partialTraceB,rankOneMatrix,Matrix.vecMulVec_apply,Fintype.sum_unique]

theorem vacuumCache_gram :
    (basisEmbedding (vacuumCache (A:=A) (M:=M)))ᴴ*
      basisEmbedding (vacuumCache (A:=A) (M:=M))=(1:CMatrix (A×M)) := by
  apply basisEmbedding_gram
  intro x y hxy
  exact Prod.ext (congrArg (fun z : Cache (A:=A) (M:=M) 0=>z.1.1) hxy)
    (congrArg (fun z : Cache (A:=A) (M:=M) 0=>z.2) hxy)

theorem vacuumCache_trace (z : A×M→ℂ) :
    (rankOneMatrix (basisEmbedding (vacuumCache (A:=A) (M:=M))*ᵥz)).trace=
      (rankOneMatrix z).trace := by
  rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  simpa only [ICO.ClassicalDilation.isometryChannel_apply] using
    (ICO.ClassicalDilation.isometryChannel (basisEmbedding vacuumCache)
      vacuumCache_gram).tracePreserving (rankOneMatrix z)

#print axioms encoding_initial
#print axioms vacuumInput_erasure
#print axioms vacuumCache_trace
end
end ICO.C6ModeFockVacuum
