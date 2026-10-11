import ICO.SequentialIsometry
import ICO.ControlledIsometry
import ICO.OracleLift

namespace ICO.SequentialIsometry
open Matrix QIT ICO.ControlledIsometry
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 1600000
variable {A B C O I : Type u} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]

structure EndData (B O : Type u) [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O] where
  E : Type u
  [finite : Fintype E]
  [decide : DecidableEq E]
  post : Matrix (O×E) B ℂ
  isometry : post.conjTranspose*post=1
attribute [instance] EndData.finite EndData.decide

structure HeadData (A B O : Type u) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O] (q : ℕ) where
  M : Type u
  [finite : Fintype M]
  [decide : DecidableEq M]
  pre : Matrix (A×M) B ℂ
  isometry : pre.conjTranspose*pre=1
  tail : Protocol A (A×M) O q
attribute [instance] HeadData.finite HeadData.decide

def Protocol.ending (p : Protocol A B O 0) : EndData B O := by
  cases p with
  | stop post hpost => exact ⟨_,post,hpost⟩

def Protocol.heading {q : ℕ} (p : Protocol A B O (q+1)) : HeadData A B O q := by
  cases p with
  | query pre hpre after => exact ⟨_,pre,hpre,after⟩

theorem Protocol.ending_map (p : Protocol A B O 0) (U : I → CMatrix A) :
    p.map U = MatrixMap.ofKraus (erasedKraus p.ending.post) := by
  cases p
  rfl

theorem Protocol.heading_map {q : ℕ} (p : Protocol A B O (q+1)) (U : I → CMatrix A) :
    p.map U = (p.heading.tail.map U).comp
      ((ICO.AllChannelDilation.oracleMap U).comp (singleMap p.heading.pre)) := by
  cases p
  rfl

def permutation (e : B ≃ C) : Matrix C B ℂ :=
  (1 : CMatrix B).submatrix e.symm (Equiv.refl _)

theorem permutation_isometry (e : B ≃ C) :
    (permutation e).conjTranspose * permutation e=1 := by
  rw [permutation,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_one,
    Matrix.submatrix_mul_equiv,Matrix.one_mul,Matrix.submatrix_one_equiv]

theorem permutation_sandwich (e : B ≃ C) (X : CMatrix B) :
    permutation e * X * (permutation e).conjTranspose = X.submatrix e.symm e.symm := by
  rw [permutation,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_one,
    Matrix.one_submatrix_mul,Matrix.mul_submatrix_one]
  rfl

theorem erasedKraus_apply {E : Type u} [Fintype E]
    (W : Matrix (O×E) B ℂ) (X : CMatrix B) :
    MatrixMap.ofKraus (erasedKraus W) X = partialTraceB (W*X*W.conjTranspose) := by
  ext o p
  simp only [MatrixMap.ofKraus,LinearMap.coe_mk,AddHom.coe_mk,Matrix.sum_apply,
    partialTraceB,Matrix.mul_apply,Matrix.conjTranspose_apply,erasedKraus]

variable {J : Type u} [Fintype J] [DecidableEq J]
variable {Bs : J → Type u} [∀ j, Fintype (Bs j)] [∀ j, DecidableEq (Bs j)]

def Protocol.controlled {q : ℕ} (p : (j:J) → Protocol A (Bs j) O q) :
    Protocol A ((j:J)×Bs j) O q := by
  induction q generalizing Bs with
  | zero =>
    exact .stop (ICO.ControlledIsometry.controlled (fun j => (p j).ending.post))
      (controlled_isometry _ (fun j => (p j).ending.isometry))
  | succ q ih =>
    let tail := ih (fun j => (p j).heading.tail)
    let e := distrib A (fun j => (p j).heading.M)
    exact .query (ICO.ControlledIsometry.controlled (fun j => (p j).heading.pre))
      (controlled_isometry _ (fun j => (p j).heading.isometry))
      (tail.precompose (permutation e) (permutation_isometry e))

theorem controlled_oracle_block
    {Ms : J → Type u} [∀ j, Fintype (Ms j)] [∀ j, DecidableEq (Ms j)]
    (W : (j:J) → Matrix (A×Ms j) (Bs j) ℂ)
    (U : I → CMatrix A) (X : CMatrix ((j:J)×Bs j)) (j:J) :
    (permutation (distrib A Ms) *
      ICO.AllChannelDilation.oracleMap U
        (ICO.ControlledIsometry.controlled W*X*(ICO.ControlledIsometry.controlled W).conjTranspose) *
      (permutation (distrib A Ms)).conjTranspose).submatrix (Sigma.mk j) (Sigma.mk j) =
    ICO.AllChannelDilation.oracleMap U
      (W j * X.submatrix (Sigma.mk j) (Sigma.mk j) * (W j).conjTranspose) := by
  rw [permutation_sandwich]
  ext x y
  simp only [Matrix.submatrix_apply,distrib,Equiv.coe_fn_symm_mk]
  rw [ICO.OracleLift.oracleMap_lift,ICO.OracleLift.oracleMap_lift]
  change (MatrixMap.ofKraus U) (fun a b =>
      (ICO.ControlledIsometry.controlled W*X*(ICO.ControlledIsometry.controlled W).conjTranspose)
        (a,⟨j,x.2⟩) (b,⟨j,y.2⟩)) x.1 y.1 = _
  simp_rw [controlled_sandwich_block]
  rfl

theorem Protocol.controlled_map {q : ℕ} (p : (j:J) → Protocol A (Bs j) O q)
    (U : I → CMatrix A) (X : CMatrix ((j:J)×Bs j)) :
    (Protocol.controlled p).map U X =
      ∑ j, (p j).map U (X.submatrix (Sigma.mk j) (Sigma.mk j)) := by
  induction q generalizing Bs with
  | zero =>
    change MatrixMap.ofKraus (erasedKraus (ICO.ControlledIsometry.controlled
      (fun j => (p j).ending.post))) X = _
    rw [erasedKraus_apply,controlled_erasure]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Protocol.ending_map,erasedKraus_apply]
  | succ q ih =>
    change (((Protocol.controlled (fun j => (p j).heading.tail)).precompose
      (permutation (distrib A (fun j => (p j).heading.M)))
      (permutation_isometry _)).map U)
      (ICO.AllChannelDilation.oracleMap U
        (singleMap (ICO.ControlledIsometry.controlled (fun j => (p j).heading.pre)) X)) = _
    rw [Protocol.precompose_map]
    simp only [LinearMap.comp_apply,singleMap_apply]
    rw [ih]
    apply Finset.sum_congr rfl
    intro j hj
    rw [controlled_oracle_block,Protocol.heading_map]
    simp only [LinearMap.comp_apply,singleMap_apply]

#print axioms Protocol.controlled_map
#print axioms Protocol.controlled
end
end ICO.SequentialIsometry
