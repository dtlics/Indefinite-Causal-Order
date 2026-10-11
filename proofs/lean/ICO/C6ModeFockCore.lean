import ICO.C6DecodedHistory
import ICO.C6TwoFockVacuumMemory

namespace ICO.C6ModeFockCore
open Matrix QIT ICO.C6DecodedHistory ICO.C6ModeFockRetrieval ICO.C6ModeFockEncoding
  ICO.C6TwoFockMemory ICO.C6TwoFockVacuumMemory ICO.C6TwoFockVisible
  ICO.C6CacheDecode ICO.C6CacheQueryBound ICO.C6PolarFock ICO.MHBoundedRecording
  ICO.C6RightImageErasure ICO.MHFockKnownOperation
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A M:Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

theorem missing_encoding {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t)
    (v:Fin r→EuclideanSpace ℂ A) :
    (1-Matrix.kronecker (polarLeftOnFock (α:=A) h) (1:CMatrix M)*
      (Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M))ᴴ)*
        encoding T l r (by omega) v=
      encoding T l r (by omega) v*Matrix.kronecker (missing (M:=M) l) (1:CMatrix (Fin r→A)) := by
  refine encoding_transport T l l r (by omega) (by omega) _ (missing (M:=M) l) ?_ v
  cases l with
  | zero=>
    simpa only [missing,Matrix.kronecker,Matrix.one_kronecker_one,Matrix.mul_one] using
      (memoryJ_vacuum_complement (A:=A) (M:=M) (r:=r) h (by omega))
  | succ l=>
    exact memoryJ_left_complement h (by omega)

theorem retrieval_encoding_any {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t)
    (U:Matrix.unitaryGroup A ℂ) (j:A) (v:Fin r→EuclideanSpace ℂ A) :
    retrieval (M:=M) h U j*encoding T l r (by omega) v=
      encoding T l r (by omega) v*
        Matrix.kronecker (retrieved (M:=M) U j l) (1:CMatrix (Fin r→A)) := by
  cases l with
  | zero=>
    rw [encoding]
    simp only [retrieved,Matrix.zero_kronecker,Matrix.mul_zero]
    unfold retrieval
    rw [Matrix.mul_assoc,Matrix.mul_assoc,←Matrix.mul_assoc
      (Matrix.kronecker (polarLeftOnFock h) (1:CMatrix M))ᴴ,
      memoryJ_vacuum_adjoint h (by omega)]
    simp
  | succ l=>exact retrieval_encoding h (by omega) U j v

theorem left_encoding {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t)
    (v:Fin r→EuclideanSpace ℂ A) :
    Matrix.kronecker (polarLeftOnFock (α:=A) h) (1:CMatrix M)*
      encoding T l r (by omega) v=
        encoding T (l+1) r (by omega) v*
          Matrix.kronecker (memoryPolar (M:=M) l) (1:CMatrix (Fin r→A)) :=
  encoding_transport T l (l+1) r _ _ _ _ (memoryJ_left h hs) v

#print axioms missing_encoding
#print axioms retrieval_encoding_any
end
end ICO.C6ModeFockCore
