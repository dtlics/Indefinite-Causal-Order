import ICO.C6TwoFockVisible
import ICO.C6DirectBirthFactorization

namespace ICO.C6ModeFockEncoding
open Matrix QIT ICO.C6TwoFockVisible ICO.C6TwoFockSector ICO.C6CacheDecode
  ICO.C6CacheKnownOperation ICO.C6CacheVisible ICO.C6RightImageErasure
  ICO.C6PrivateIsometry ICO.MHBoundedRecording ICO.MHFockKnownOperation
  ICO.MHDecompressionErasure ICO.RecordingCopyIdentity ICO.RecordingPureCorrespondence
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M N:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem memoryJ_gram (T l r:ℕ) (h:l+r≤T) :
    (memoryJ (A:=A) (M:=M) T l r h)ᴴ*memoryJ (A:=A) (M:=M) T l r h=1 := by
  apply basisEmbedding_gram
  intro x y hxy
  have hf : (x.1.1,x.2)=(y.1.1,y.2) :=
    sectorEmbed_injective T l r h (congrArg Prod.fst hxy)
  have hm : x.1.2=y.1.2 := congrArg (fun z:InputCutoff (α:=A) T×M=>z.2) hxy
  have hleft : x.1.1=y.1.1 := congrArg (fun z:TwoSector (A:=A) l r=>z.1) hf
  have hright : x.2=y.2 := congrArg (fun z:TwoSector (A:=A) l r=>z.2) hf
  exact Prod.ext (Prod.ext hleft hm) hright

def encoding (T l r:ℕ) (h:l+r≤T) (v:Fin r→EuclideanSpace ℂ A) :
    Matrix (InputCutoff (α:=A) T×M) (Cache (A:=A) (M:=M) l×(Fin r→A)) ℂ :=
  memoryJ T l r h*Matrix.kronecker (1:CMatrix (Cache (A:=A) (M:=M) l)) (directEncoding v)

theorem encoding_gram (T l r:ℕ) (h:l+r≤T) (v:Fin r→EuclideanSpace ℂ A)
    (hv:Orthonormal ℂ v) :
    (encoding (M:=M) T l r h v)ᴴ*encoding (M:=M) T l r h v=1 := by
  rw [encoding,Matrix.conjTranspose_mul,Matrix.mul_assoc,
    ←Matrix.mul_assoc (memoryJ (A:=A) (M:=M) T l r h)ᴴ,memoryJ_gram,Matrix.one_mul]
  simp only [Matrix.kronecker,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  rw [←Matrix.mul_kronecker_mul,directEncoding_gram v hv,Matrix.one_mul,Matrix.one_kronecker_one]

theorem encoding_visible (T l r:ℕ) (h:l+r≤T) (v:Fin r→EuclideanSpace ℂ A)
    (hv:Orthonormal ℂ v) (z:Cache (A:=A) (M:=M) l×(Fin r→A)→ℂ) :
    fockVisible T (encoding T l r h v*ᵥz)=
      (sectorVisible l).map (partialTraceB (rankOneMatrix z)) := by
  rw [encoding,←Matrix.mulVec_mulVec,visible_memoryJ,
    rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
    directEncoding_erasure v hv]

theorem encoding_known (T l r:ℕ) (h:l+r≤T) (v:Fin r→EuclideanSpace ℂ A)
    (K:Matrix (A×N) (A×M) ℂ) :
    ICO.MHFockKnownOperation.known T K*encoding T l r h v=
      encoding T l r h v*Matrix.kronecker (externalLift l K) (1:CMatrix (Fin r→A)) := by
  rw [encoding,encoding,←Matrix.mul_assoc,memoryJ_known,cacheKnown_eq]
  simp only [Matrix.mul_assoc]
  apply congrArg (fun D=>memoryJ (A:=A) (M:=N) T l r h*D)
  simp only [Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,Matrix.mul_one,Matrix.one_mul]

#print axioms encoding_visible
#print axioms encoding_known
end
end ICO.C6ModeFockEncoding
