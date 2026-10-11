import ICO.C6ModeFockEncoding
import ICO.C6TwoFockMemory
import ICO.C6RetainedSectorOperations

/-! Actual retrieval acts on the left cache and leaves every stored private
image intact. The reduced channel identity holds for arbitrary entanglement. -/
namespace ICO.C6ModeFockRetrieval
open QIT Matrix ICO.C6ModeFockEncoding ICO.C6TwoFockMemory ICO.C6TwoFockVisible
  ICO.C6CacheDecode ICO.C6CacheQueryBound ICO.C6PolarFock ICO.C6RetainedSectorOperations
  ICO.C6RetainedCacheLocal ICO.C6RightImageErasure ICO.MHBoundedRecording
  ICO.MHFockKnownOperation ICO.RecordingPureCorrespondence ICO.MHDecompressionErasure
  ICO.C6CacheVisible ICO.C6CacheMap
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M N:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]

theorem encoding_transport (T l k r:ℕ) (hl:l+r≤T) (hk:k+r≤T)
    (D:Matrix (InputCutoff (α:=A) T×N) (InputCutoff (α:=A) T×M) ℂ)
    (L:Matrix (Cache (A:=A) (M:=N) k) (Cache (A:=A) (M:=M) l) ℂ)
    (hD:D*memoryJ T l r hl=memoryJ T k r hk*
      Matrix.kronecker L (1:CMatrix (TensorPowerProfile (A×A) r)))
    (v:Fin r→EuclideanSpace ℂ A) :
    D*encoding T l r hl v=encoding T k r hk v*
      Matrix.kronecker L (1:CMatrix (Fin r→A)) := by
  rw [encoding,encoding,←Matrix.mul_assoc,hD]
  simp only [Matrix.mul_assoc]
  apply congrArg (fun X=>memoryJ (A:=A) (M:=N) T k r hk*X)
  simp only [Matrix.kronecker]
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,
    Matrix.mul_one,Matrix.one_mul,Matrix.one_mul,Matrix.mul_one]

def retrieval {t T:ℕ} (h:t+1≤T) (U:Matrix.unitaryGroup A ℂ) (j:A) :
    CMatrix (InputCutoff (α:=A) T×M) :=
  Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M)*
    known T (Matrix.kronecker (ICO.SwitchObservable.basisProjection (U:CMatrix A) j)
      (1:CMatrix M))*(Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M))ᴴ

def cacheRetrieval (U:Matrix.unitaryGroup A ℂ) (l:ℕ) (j:A) :
    CMatrix (Cache (A:=A) (M:=M) (l+1)) :=
  memoryPolar l*projection (M:=M) U l j*(memoryPolar l)ᴴ

theorem retrieval_encoding {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t)
    (U:Matrix.unitaryGroup A ℂ) (j:A) (v:Fin r→EuclideanSpace ℂ A) :
    retrieval (M:=M) h U j*encoding T (l+1) r (by omega) v=
      encoding T (l+1) r (by omega) v*
        Matrix.kronecker (cacheRetrieval (M:=M) U l j) (1:CMatrix (Fin r→A)) :=
  encoding_transport T (l+1) (l+1) r _ _ _ _ (memoryJ_retrieval h hs U j) v

theorem retrieval_reduced {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t)
    (U:Matrix.unitaryGroup A ℂ) (j:A) (v:Fin r→EuclideanSpace ℂ A)
    (hv:Orthonormal ℂ v) (z:Cache (A:=A) (M:=M) (l+1)×(Fin r→A)→ℂ) :
    fockVisible T (retrieval h U j*ᵥ(encoding T (l+1) r (by omega) v*ᵥz))=
      (sectorVisible (l+1)).map
        (ICO.C6RetainedCacheLocal.retrieve U l j (partialTraceB (rankOneMatrix z))) := by
  rw [Matrix.mulVec_mulVec,retrieval_encoding h hs U j v,
    ←Matrix.mulVec_mulVec,encoding_visible _ _ _ _ v hv,
    rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  have he:=partialTraceB_known (cacheRetrieval (M:=M) U l j) (rankOneMatrix z)
  simp only [conjugate_apply] at he
  rw [he,retrieve_projection]
  simp only [cacheRetrieval,conjugate_apply]

#print axioms retrieval_encoding
#print axioms retrieval_reduced
end
end ICO.C6ModeFockRetrieval
