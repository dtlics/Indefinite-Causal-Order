import ICO.GeneralOrderedQubitFamilies
import ICO.TwoQueryDilation
import ICO.QubitChoiIndex

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.GeneralOrderedQubitFamilies
open ICO.ExactQubitObstruction ICO.PositiveSupport

namespace ICO.NormalFormQubitObstruction
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
variable {M : Type} [Fintype M] [DecidableEq M]

abbrev flattenChoi := ICO.QubitChoiIndex.flatten

theorem branch_output (b : Branch) (U V : CMatrix (Fin 2)) :
    b.output U V = flattenChoi (MatrixMap.choi (MatrixMap.ofKraus
      (ICO.AllChannelDilation.circuitKraus b.pre b.mid b.post U V))) := by
  ext i j
  simp only [Branch.output,flattenChoi,ICO.QubitChoiIndex.flatten,MatrixMap.choi_ofKraus,Matrix.sum_apply,
    rankOne,Matrix.vecMulVec_apply,ICO.QubitCircuitLink.vectorize]
  rfl

def zeroPre (b : Branch) : Branch := {b with pre:=0}

theorem zeroPre_output (b : Branch) (U V : CMatrix (Fin 2)) : (zeroPre b).output U V=0 := by
  have hz (k : b.K) : ICO.QubitCircuitLink.circuitKraus
      (0 : Matrix (Fin 2 × b.M) (Fin 2) ℂ) b.mid b.post U V k=0 := by
    unfold ICO.QubitCircuitLink.circuitKraus
    exact Matrix.mul_zero _
  change (∑ k : b.K,rankOne (ICO.QubitCircuitLink.vectorize
    (ICO.QubitCircuitLink.circuitKraus (0 : Matrix (Fin 2 × b.M) (Fin 2) ℂ)
      b.mid b.post U V k)))=0
  simp_rw [hz]
  ext i j
  simp [ICO.QubitCircuitLink.vectorize,rankOne,Matrix.vecMulVec_apply,Matrix.sum_apply]

def baseBranch (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (b : R.Branch) : Branch where
  M := M
  N := M × (R.rest b).Branch
  K := (((Fin 2 × M) × Fin 4) × (R.rest b).Branch)
  pre := R.pre.op b
  mid := ICO.AllChannelDilation.normalMid (R.rest b)
  post := ICO.AllChannelDilation.normalPost (R.rest b)
  mid_isometry := ICO.AllChannelDilation.normalMid_complete (R.rest b)
  post_isometry := ICO.AllChannelDilation.normalPost_complete (R.rest b)

def abBranch (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (b : R.Branch) : Branch :=
  if R.order b = .firstThenSecond then baseBranch R b else zeroPre (baseBranch R b)

def baBranch (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (b : R.Branch) : Branch :=
  if R.order b = .firstThenSecond then zeroPre (baseBranch R b) else baseBranch R b

theorem split_branch (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (b : R.Branch) (U V : CMatrix (Fin 2)) :
    (abBranch R b).output U V+(baBranch R b).output V U =
      flattenChoi (MatrixMap.choi (ICO.TwoQueryDilation.branchMap R b U V)) := by
  cases ho : R.order b with
  | firstThenSecond =>
    simp only [abBranch,baBranch,ho,if_true,zeroPre_output,add_zero,
      ICO.TwoQueryDilation.branchMap]
    exact branch_output (baseBranch R b) U V
  | secondThenFirst =>
    simp only [abBranch,baBranch,ho,reduceCtorEq,if_false,zeroPre_output,zero_add,
      ICO.TwoQueryDilation.branchMap]
    exact branch_output (baseBranch R b) V U

theorem family_split (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (U V : CMatrix (Fin 2)) :
    familyOutput (abBranch R) U V+familyOutput (baBranch R) V U =
      ∑ b : R.Branch,flattenChoi (MatrixMap.choi (ICO.TwoQueryDilation.branchMap R b U V)) := by
  unfold familyOutput
  rw [← Finset.sum_add_distrib]
  simp_rw [split_branch]

theorem normalForm_output (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (U V : Fin 4 → CMatrix (Fin 2))
    (hU : ∑ i,(U i)ᴴ * U i=1) (hV : ∑ j,(V j)ᴴ * V j=1) :
    flattenChoi (MatrixMap.choi
      ((R.channel (ICO.AllChannelDilation.oracleChannel U hU)
        (ICO.AllChannelDilation.oracleChannel V hV)).map)) =
      ∑ i,∑ j,(familyOutput (abBranch R) (U i) (V j)+familyOutput (baBranch R) (V j) (U i)) := by
  simp_rw [family_split]
  ext o p
  simp only [flattenChoi,ICO.QubitChoiIndex.flatten,MatrixMap.choi,
    ICO.TwoQueryDilation.normalForm_channel,Matrix.sum_apply]
  conv_rhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  exact (Finset.sum_comm).symm

/-- The exact positive-dilution obstruction applies to the actual adaptive
normal form on arbitrary noisy channels and the retained control output. -/
theorem no_normalForm
    (lambda mu : ℝ) (hl0 : 0<lambda) (hl1 : lambda≤1) (hm0 : 0<mu) (hm1 : mu≤1)
    (R : ICO.TwoQueryTree.NormalForm (Fin 2) (Fin 2 × M) (Fin 4))
    (h : ∀ U V : Fin 4 → CMatrix (Fin 2), ∀ (hU : ∑ i,(U i)ᴴ * U i=1)
      (hV : ∑ j,(V j)ᴴ * V j=1),
      flattenChoi (MatrixMap.choi
        ((R.channel (ICO.AllChannelDilation.oracleChannel U hU)
          (ICO.AllChannelDilation.oracleChannel V hV)).map)) =
        dilutedSwitchOutput lambda mu U V) : False := by
  apply no_circuit_family lambda mu hl0 hl1 hm0 hm1 (abBranch R) (baBranch R)
  intro U V hU hV
  rw [← normalForm_output R U V hU hV]
  exact h U V hU hV

theorem no_twoQueryTree
    (lambda mu : ℝ) (hl0 : 0<lambda) (hl1 : lambda≤1) (hm0 : 0<mu) (hm1 : mu≤1)
    (tree : ICO.TwoQueryTree.QueryTree (Fin 2 × M) (Fin 4) (Fin 2))
    (h : ∀ U V : Fin 4 → CMatrix (Fin 2), ∀ (hU : ∑ i,(U i)ᴴ * U i=1)
      (hV : ∑ j,(V j)ᴴ * V j=1),
      flattenChoi (MatrixMap.choi
        ((tree.channel (ICO.AllChannelDilation.oracleChannel U hU)
          (ICO.AllChannelDilation.oracleChannel V hV)).map)) =
        dilutedSwitchOutput lambda mu U V) : False := by
  apply no_normalForm lambda mu hl0 hl1 hm0 hm1 tree.normalForm
  intro U V hU hV
  rw [ICO.TwoQueryTree.QueryTree.normalForm_correct]
  exact h U V hU hV

#print axioms no_twoQueryTree
end
end ICO.NormalFormQubitObstruction
