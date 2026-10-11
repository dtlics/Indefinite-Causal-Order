import ICO.C6BosonicGeometricCreation

/-! The actual forward polar insertion places the newly observed vector in
the enlarged history span. -/
namespace ICO.C6BosonicReencoding
open QIT ICO.C6BosonicGeometricCreation ICO.C6BosonicQueryAlgebra
  ICO.C6BosonicHistorySupport ICO.C6CacheSpanProjection ICO.C6CacheHistorySpan
  ICO.C6PolarFock ICO.C6FockQueryMatrix ICO.C6BosonicFreshRotated
  ICO.MHBoundedRecording ICO.MHProtocolOverlap
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2200000
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def rankOne (x : EuclideanSpace ℂ A) : CMatrix A :=
  Matrix.vecMulVec (fun i=>x i) (fun j=>star (x j))

theorem fixes_rankOne (P : CMatrix A) (x : EuclideanSpace ℂ A) (hx : act P x=x) :
    P*rankOne x=rankOne x := by
  have he := congrArg WithLp.ofLp hx
  change P*ᵥ(⇑x)=⇑x at he
  rw [rankOne,Matrix.mul_vecMulVec,he]

theorem history_new_vector {s : ℕ} (v : Fin s→EuclideanSpace ℂ A) (x : EuclideanSpace ℂ A) :
    act (historyProjection (Fin.snoc v x)) x=x := by
  simpa only [Fin.snoc_last] using historyProjection_contains (Fin.snoc v x) (Fin.last s)

theorem reencoding_support {s t T : ℕ} (v : Fin s→EuclideanSpace ℂ A)
    (x : EuclideanSpace ℂ A) (h : t+1≤T) (ht : t<Fintype.card A) :
    historySupport (Fin.snoc v x) T*polarLeftOnFock h*queryMatrix (rankOne x) T*historySupport v T=
      polarLeftOnFock h*queryMatrix (rankOne x) T*historySupport v T := by
  let P := queryMatrix (historyProjection (Fin.snoc v x)) T
  let B := historySupport (Fin.snoc v x) T
  let X := queryMatrix (rankOne x) T
  have hF : B*polarLeftOnFock h=polarLeftOnFock h*P*B :=
    geometric_left_support (historyUnitary (Fin.snoc v x)) (historyIndices (Fin.snoc v x)) h ht
  have hPX : P*X=X := by
    rw [←query_mul,fixes_rankOne _ x (history_new_vector v x)]
  have hBX : B*X=X*B := (query_support _ _ T).symm
  change B*polarLeftOnFock h*X*historySupport v T=_
  rw [hF]
  calc
    _ = polarLeftOnFock h*(P*X)*(B*historySupport v T) := by
      simp only [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc B X,hBX]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPX,historySupport_snoc]

#print axioms reencoding_support
end
end ICO.C6BosonicReencoding
