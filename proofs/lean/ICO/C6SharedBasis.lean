import ICO.C6ChoiceOracle
import ICO.FullSwitchChannel
import ICO.LudersPromise

/-! The one shared unknown basis underlying SAME and translated MUB oracles.
The choice bit remains a public register; its copied outcome is private. -/
namespace ICO.C6SharedBasis
open Matrix QIT ICO.SwitchObservable ICO.FullSwitchChannel
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option Elab.async false
variable {A M : Type} [Fintype A] [DecidableEq A] [Nontrivial A]
  [Fintype M] [DecidableEq M]

def choiceUnitary (U V : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup (A×Bool) ℂ :=
  ⟨controlled U V, by
    have hU₁ : (U:CMatrix A)ᴴ*(U:CMatrix A)=1 := U.property.1
    have hU₂ : (U:CMatrix A)*(U:CMatrix A)ᴴ=1 := U.property.2
    have hV₁ : (V:CMatrix A)ᴴ*(V:CMatrix A)=1 := V.property.1
    have hV₂ : (V:CMatrix A)*(V:CMatrix A)ᴴ=1 := V.property.2
    constructor
    · change (controlled (U:CMatrix A) (V:CMatrix A))ᴴ*controlled U V=1
      rw [controlled_star,controlled_mul,hU₁,hV₁,controlled_one]
    · change controlled (U:CMatrix A) (V:CMatrix A)*(controlled U V)ᴴ=1
      rw [controlled_star,controlled_mul,hU₂,hV₂,controlled_one]⟩

def basis (U H : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup (A×Bool) ℂ :=
  choiceUnitary U (U*H)

def knownBasis (H : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup (A×Bool) ℂ :=
  choiceUnitary 1 H

def shared (U : Matrix.unitaryGroup A ℂ) : Matrix.unitaryGroup (A×Bool) ℂ :=
  choiceUnitary U U

theorem shared_matrix (U : Matrix.unitaryGroup A ℂ) :
    (shared U : CMatrix (A×Bool))=Matrix.kronecker (U:CMatrix A) (1:CMatrix Bool) := by
  ext ⟨a,b⟩ ⟨c,e⟩
  cases b <;> cases e <;> simp [shared,choiceUnitary,controlled,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply]

theorem basis_factor (U H : Matrix.unitaryGroup A ℂ) : basis U H=shared U*knownBasis H := by
  apply Subtype.ext
  change controlled (U:CMatrix A) ((U:CMatrix A)*(H:CMatrix A)) =
    controlled (U:CMatrix A) U * controlled (1:CMatrix A) H
  rw [controlled_mul,Matrix.mul_one]

def kraus (U H : Matrix.unitaryGroup A ℂ) (b : Bool) : A→CMatrix A :=
  basisProjection (if b then ((U*H : Matrix.unitaryGroup A ℂ):CMatrix A) else (U:CMatrix A))

theorem kraus_complete (U H : Matrix.unitaryGroup A ℂ) (b : Bool) :
    (∑i,(kraus U H b i)ᴴ*kraus U H b i)=1 := by
  cases b <;> simp only [kraus,ite_false,ite_true]
  · exact hidden_basis_kraus_complete _ U.property.1 U.property.2
  · exact hidden_basis_kraus_complete _ (U*H).property.1 (U*H).property.2

theorem tagged_projection (U H : Matrix.unitaryGroup A ℂ) (b : Bool) (i : A) :
    ICO.C6ChoiceOracle.taggedKraus (kraus U H) (b,i) =
      basisProjection (basis U H : CMatrix (A×Bool)) (i,b) := by
  ext ⟨a,c⟩ ⟨a',e⟩
  simp only [ICO.LudersPromise.basisProjection_rankOne]
  cases b <;> cases c <;> cases e <;>
    simp [ICO.C6ChoiceOracle.taggedKraus,kraus,ICO.LudersPromise.basisProjection_rankOne,
      basis,choiceUnitary,controlled,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.single,rankOneMatrix,Matrix.vecMulVec_apply]

theorem oracleMap_tagged (U H : Matrix.unitaryGroup A ℂ) :
    ICO.AllChannelDilation.oracleMap (M:=M) (ICO.C6ChoiceOracle.taggedKraus (kraus U H)) =
      ICO.AllChannelDilation.oracleMap (basisProjection (basis U H : CMatrix (A×Bool))) := by
  ext X a b
  simp only [ICO.AllChannelDilation.oracleMap,MatrixMap.ofKraus,LinearMap.coe_mk,
    AddHom.coe_mk,Matrix.sum_apply,Fintype.sum_prod_type,tagged_projection]
  rw [Finset.sum_comm]

#print axioms oracleMap_tagged
end
end ICO.C6SharedBasis
