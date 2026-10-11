import ICO.C6ResidualCoordinates
import ICO.C6HistoryImageErasure
import ICO.C6BosonicReencoding
import ICO.C6RotatedSelection

/-! A rank-one private measurement selects exactly its actual residual mode
on the fresh branch; the zero-residual branch vanishes. -/
namespace ICO.C6ResidualSelection
open Matrix QIT ICO.C6ResidualModes ICO.C6ResidualCoordinates ICO.C6CacheSpanProjection
  ICO.C6HistoryImageErasure ICO.C6BosonicReencoding ICO.C6BosonicQueryAlgebra
  ICO.C6RotatedSelection ICO.C6NumberSelection ICO.C6FockQueryMatrix
  ICO.C6BosonicFockRotated ICO.C6BosonicFreshRotated ICO.MHProtocolOverlap
  ICO.MHBoundedRecording ICO.C6CacheHistorySpan
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2000000
set_option Elab.async false
variable {A:Type*} [Fintype A] [DecidableEq A] [Nonempty A]

theorem rankOne_adjoint (x:EuclideanSpace ℂ A) : (rankOne x)ᴴ=rankOne x := by
  ext i j
  simp only [rankOne,Matrix.conjTranspose_apply,Matrix.vecMulVec_apply,star_mul,star_star]

theorem measurement_selection (M Q:CMatrix A) (hM:Mᴴ=M) (hQ:Qᴴ=Q)
    (x:EuclideanSpace ℂ A) (h:act Q (act M x)=act M x) :
    rankOne x*M*Q=rankOne x*M := by
  have hv:Q*ᵥ(M*ᵥ(⇑x))=M*ᵥ(⇑x) := congrArg WithLp.ofLp h
  have he:Q*(M*rankOne x)=M*rankOne x := by
    simp only [rankOne,Matrix.mul_vecMulVec,hv]
  have ha:=congrArg Matrix.conjTranspose he
  simpa only [Matrix.conjTranspose_mul,rankOne_adjoint,hM,hQ] using ha

theorem residual_mode_selection {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Active v)
    (U:Matrix.unitaryGroup A ℂ) (a:A) (ha:column U a=mode v i) :
    rankOne (v i)*(1-historyProjection (prior v i))*spanProjection U {a}=
      rankOne (v i)*(1-historyProjection (prior v i)) := by
  apply measurement_selection
  · have hp:(historyProjection (prior v i))ᴴ=historyProjection (prior v i):=
      (spanProjection_projection _ _).isSelfAdjoint.star_eq
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hp]
  · exact (spanProjection_projection U {a}).isSelfAdjoint.star_eq
  · rw [←residual_eq_projection,residual_eq_norm_smul_mode,map_smul,←ha,
      projection_column,if_pos (Finset.mem_singleton_self a)]

theorem inactive_selection {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Fin q)
    (hi:residual v i=0) : rankOne (v i)*(1-historyProjection (prior v i))=0 := by
  have hv:(1-historyProjection (prior v i))*ᵥ(⇑(v i))=0 := by
    have he:=congrArg WithLp.ofLp (residual_eq_projection v i)
    rw [hi] at he
    exact he.symm
  have he:(1-historyProjection (prior v i))*rankOne (v i)=0 := by
    rw [rankOne,Matrix.mul_vecMulVec,hv,Matrix.zero_vecMulVec]
  have ha:=congrArg Matrix.conjTranspose he
  have hp:(historyProjection (prior v i))ᴴ=historyProjection (prior v i):=
    (spanProjection_projection _ _).isSelfAdjoint.star_eq
  simpa only [Matrix.conjTranspose_mul,rankOne_adjoint,Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one,hp,
    Matrix.conjTranspose_zero] using ha

theorem rotatedSelected_query (U:Matrix.unitaryGroup A ℂ) (S:Finset A) (T:ℕ) :
    rotatedSelected U S T=queryMatrix (spanProjection U S) T := by
  rw [spanProjection,query_mul,query_mul,query_adjoint,query_unitary]
  unfold rotatedSelected
  congr 2
  rw [coordinateProjection,query_diagonal]
  rfl

theorem fresh_measurement_selection {q:ℕ} (v:Fin q→EuclideanSpace ℂ A) (i:Active v)
    (U:Matrix.unitaryGroup A ℂ) (a:A) (ha:column U a=mode v i) (B:Finset A)
    (hB:historyProjection (prior v i)=spanProjection U B) (T:ℕ) :
    queryMatrix (rankOne (v i)) T*rotatedFresh U B T*rotatedSelected U {a} T=
      queryMatrix (rankOne (v i)) T*rotatedFresh U B T := by
  rw [rotatedSelected_query,rotatedFresh_complement,←ICO.C6BosonicQueryAlgebra.query_one,←query_sub,
    ←query_mul,←query_mul,←hB,residual_mode_selection v i U a ha]

#print axioms residual_mode_selection
#print axioms inactive_selection
#print axioms fresh_measurement_selection
end
end ICO.C6ResidualSelection
