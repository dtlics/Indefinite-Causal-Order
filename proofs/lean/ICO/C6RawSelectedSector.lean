import ICO.C6RawTwoSector
import ICO.C6ResidualSelection
import ICO.C6TwoFockMemory

/-! The literal measured raw birth selects the conjugate residual mode.
The left cache and arbitrary memory remain spectators for the right creator. -/
namespace ICO.C6RawSelectedSector
open Matrix QIT ICO.C6RawTwoSector ICO.C6TwoFockSector ICO.C6TwoFockMemory
  ICO.C6OrthogonalModeBirth ICO.C6FockQueryMatrix ICO.C6BosonicQueryAlgebra
  ICO.C6ResidualSelection ICO.C6CacheSpanProjection ICO.C6BosonicReencoding
  ICO.C6BosonicFockRotated ICO.C6BosonicFreshRotated ICO.MHProtocolOverlap
  ICO.MHBoundedRecording ICO.MHFockTransport ICO.MHFockRotation
  ICO.MHSectorCovariance ICO.RecordingCopyIdentity ICO.RecordingPureCorrespondence
  ICO.C6PolarFock ICO.C6TwoFockVisible ICO.C6CacheDecode ICO.MHFockSwap
open scoped BigOperators Matrix
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 1024
set_option Elab.async false
variable {A:Type} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem family_sector (F:∀n r,CMatrix (ICO.MHSectorCovariance.Sector (α:=A) n r))
    (T l r:ℕ) (h:l+r≤T) : inputFamily F T*J T l r h=J T l r h*F l r := by
  rw [J,mul_basisEmbedding]
  ext ⟨⟨s,R⟩,a,L⟩ ⟨⟨b,P⟩,S⟩
  by_cases hs:s=lengths T l r h
  · subst s
    have he (i:TwoSector (A:=A) l r) :
        (⟨⟨lengths T l r h,R⟩,(a,L)⟩:InputCutoff (α:=A) T)=sectorEmbed T l r h i ↔
        ((a,L),R)=i := by
      constructor
      · intro hh
        apply sectorEmbed_injective T l r h
        exact hh
      · rintro rfl
        rfl
    simp only [Matrix.submatrix_apply,id_eq]
    rw [show inputFamily F T ⟨⟨lengths T l r h,R⟩,(a,L)⟩
        (sectorEmbed T l r h ((b,P),S))=F l r ((a,L),R) ((b,P),S) by
      simp [inputFamily,sectorEquiv,sectorEmbed,lengths]]
    simp only [Matrix.mul_apply,basisEmbedding,Matrix.submatrix_apply,id_eq,Matrix.one_apply,he]
    simp only [ite_mul,one_mul,zero_mul]
    symm
    convert Finset.sum_eq_single ((a,L),R)
      (s:=Finset.univ) (f:=fun x:TwoSector (A:=A) l r=>
        if ((a,L),R)=x then F l r x ((b,P),S) else 0) ?_ ?_ using 1
    · exact (if_pos rfl).symm
    · intro x _ hx
      exact if_neg (Ne.symm hx)
    · intro hx
      exact (hx (Finset.mem_univ _)).elim
  · have hz:=inputFamily_other F T (⟨⟨s,R⟩,(a,L)⟩:InputCutoff (α:=A) T)
        (sectorEmbed T l r h ((b,P),S)) hs
    rw [Matrix.submatrix_apply,id_eq,hz]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have he:(⟨⟨s,R⟩,(a,L)⟩:InputCutoff (α:=A) T)≠sectorEmbed T l r h i:=by
      intro h';exact hs (congrArg (fun x:InputCutoff (α:=A) T=>x.1.1) h')
    simp [basisEmbedding,he]

theorem query_sector (P:CMatrix A) (T l r:ℕ) (h:l+r≤T) :
    queryMatrix P T*J T l r h=J T l r h*queryFamily P l r :=
  family_sector (queryFamily P) T l r h

def selectedSector (l r:ℕ) (ψ β:A→ℂ) :
    Matrix (TwoSector (A:=A) l (r+1)) (TwoSector (A:=A) l r) ℂ :=
  fun o i=>ψ o.1.1*selectedRaw r β o.2 (i.1.1,i.2)*
    if o.1.2=i.1.2 then 1 else 0

theorem selectedSector_eq (l r:ℕ) (ψ β:A→ℂ) :
    queryFamily (Matrix.vecMulVec ψ β) l (r+1)*rawRightSector l r=
      selectedSector l r ψ β := by
  ext ⟨⟨a,L⟩,R⟩ ⟨⟨b,P⟩,S⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,queryFamily,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply,
    Matrix.vecMulVec_apply,rawRightSector_entry,selectedSector,selectedRaw]
  by_cases hLP:L=P
  · subst P
    simp [Finset.mul_sum,Finset.sum_mul,mul_assoc,eq_comm]
  · simp [hLP,mul_assoc,Finset.mul_sum,Finset.sum_mul,eq_comm]

theorem rankOne_complement (ψ:EuclideanSpace ℂ A) (P:CMatrix A) (hP:Pᴴ=P) :
    rankOne ψ*(1-P)=Matrix.vecMulVec (WithLp.ofLp ψ)
      (fun a=>star ((1-P)*ᵥWithLp.ofLp ψ) a) := by
  have hc:(1-P)ᴴ=1-P:=by rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP]
  have he:(1-P)*rankOne ψ=Matrix.vecMulVec ((1-P)*ᵥWithLp.ofLp ψ)
      (fun a=>star (WithLp.ofLp ψ a)):=by rw [rankOne,Matrix.mul_vecMulVec]
  have ha:=congrArg Matrix.conjTranspose he
  rw [Matrix.conjTranspose_mul,rankOne_adjoint,hc] at ha
  exact ha.trans (by ext i j;simp [Matrix.conjTranspose_apply,Matrix.vecMulVec_apply,star_mul])

theorem measured_raw_sector {t T l r:ℕ} (h:t+1≤T) (hs:l+r≤t)
    (ψ:EuclideanSpace ℂ A) (U:Matrix.unitaryGroup A ℂ) (S:Finset A) :
    queryMatrix (rankOne ψ) T*rotatedFresh U S T*symmetricRightOnFock (α:=A) h*
      J T l r (by omega)=
    J T l (r+1) (by omega)*selectedSector l r (WithLp.ofLp ψ)
      (fun a=>star ((1-spanProjection U S)*ᵥWithLp.ofLp ψ) a) := by
  rw [Matrix.mul_assoc,Matrix.mul_assoc,rawRight_sector h hs,
    ←Matrix.mul_assoc,←Matrix.mul_assoc]
  rw [rotatedFresh_complement,←ICO.C6BosonicQueryAlgebra.query_one,←query_sub,←query_mul,
    rankOne_complement ψ _ (spanProjection_projection U S).isSelfAdjoint.star_eq,
    query_sector,Matrix.mul_assoc,selectedSector_eq]

#print axioms measured_raw_sector
end
end ICO.C6RawSelectedSector
