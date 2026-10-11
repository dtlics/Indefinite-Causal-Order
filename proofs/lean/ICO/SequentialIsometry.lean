import ICO.AllChannelDilation

namespace ICO.SequentialIsometry
open Matrix QIT ICO.ClassicalDilation ICO.InstrumentCompression
open scoped BigOperators
noncomputable section
universe u
set_option maxHeartbeats 1200000

/-- A sequential q-query protocol. All known operations are isometries on
accessible registers; all information discarded by the original strategy is
retained in the final finite environment. -/
inductive Protocol (A : Type u) [Fintype A] [DecidableEq A] :
    (B O : Type u) → [Fintype B] → [DecidableEq B] → [Fintype O] → [DecidableEq O] →
      ℕ → Type (u+1) where
  | stop {B O E : Type u} [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
      [Fintype E] [DecidableEq E] (post : Matrix (O×E) B ℂ)
      (isometry : post.conjTranspose*post=1) : Protocol A B O 0
  | query {B O M : Type u} [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
      [Fintype M] [DecidableEq M] {q : ℕ} (pre : Matrix (A×M) B ℂ)
      (isometry : pre.conjTranspose*pre=1) (after : Protocol A (A×M) O q) :
        Protocol A B O (q+1)

variable {A B O C I : Type u} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
  [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]

def erasedKraus {E : Type u} [Fintype E] (W : Matrix (O×E) B ℂ) : E → Matrix O B ℂ :=
  fun e o b => W (o,e) b

def singleMap (W : Matrix C B ℂ) : MatrixMap B C :=
  MatrixMap.ofKraus (fun _ : PUnit.{u+1} => W)

theorem singleMap_apply (W : Matrix C B ℂ) (X : CMatrix B) : singleMap W X=W*X*W.conjTranspose := by
  simp [singleMap,MatrixMap.ofKraus]

def Protocol.map {q : ℕ} (p : Protocol A B O q) (U : I → CMatrix A) : MatrixMap B O := by
  induction p with
  | stop post hpost => exact MatrixMap.ofKraus (erasedKraus post)
  | query pre hpre after ih => exact ih.comp ((ICO.AllChannelDilation.oracleMap U).comp (singleMap pre))

/-- Absorb a known rectangular input isometry into the first known operation. -/
def Protocol.precompose {q : ℕ} (p : Protocol A B O q)
    (W : Matrix B C ℂ) (hW : W.conjTranspose*W=1) : Protocol A C O q := by
  cases p with
  | stop post hpost =>
    exact .stop (post*W) (by simp [Matrix.conjTranspose_mul,Matrix.mul_assoc,←Matrix.mul_assoc post.conjTranspose post,hpost,hW])
  | query pre hpre after =>
    exact .query (pre*W) (by simp [Matrix.conjTranspose_mul,Matrix.mul_assoc,←Matrix.mul_assoc pre.conjTranspose pre,hpre,hW]) after

theorem erasedKraus_mul {E : Type u} [Fintype E]
    (W : Matrix (O×E) B ℂ) (V : Matrix B C ℂ) (e : E) :
    erasedKraus (W*V) e=erasedKraus W e*V := rfl

theorem ofKraus_right_mul {E : Type u} [Fintype E]
    (K : E → Matrix O B ℂ) (W : Matrix B C ℂ) :
    MatrixMap.ofKraus (fun e => K e*W)=(MatrixMap.ofKraus K).comp (singleMap W) := by
  ext X o p
  simp only [MatrixMap.ofKraus,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.comp_apply,
    singleMap_apply,Matrix.conjTranspose_mul,Matrix.mul_assoc,Matrix.sum_apply]

theorem singleMap_mul (V : Matrix O B ℂ) (W : Matrix B C ℂ) :
    singleMap (V*W)=(singleMap V).comp (singleMap W) := by
  ext X o p
  simp only [LinearMap.comp_apply,singleMap_apply,Matrix.conjTranspose_mul,Matrix.mul_assoc]

theorem Protocol.precompose_map {q : ℕ} (p : Protocol A B O q)
    (W : Matrix B C ℂ) (hW : W.conjTranspose*W=1) (U : I → CMatrix A) :
    (p.precompose W hW).map U=(p.map U).comp (singleMap W) := by
  cases p with
  | stop post hpost =>
    change MatrixMap.ofKraus (fun e => erasedKraus post e*W)=_
    exact ofKraus_right_mul _ _
  | query pre hpre after =>
    change (after.map U).comp ((ICO.AllChannelDilation.oracleMap U).comp (singleMap (pre*W)))=_
    rw [singleMap_mul]
    rfl

#print axioms Protocol.precompose_map
end
end ICO.SequentialIsometry
