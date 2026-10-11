import ICO.ExactQubitObstruction
import ICO.QubitCircuitLink

namespace ICO.GeneralOrderedQubitFamilies
open ICO.QubitCircuitMatrix ICO.QubitCircuitLink ICO.PositiveSupport
open ICO.ExactQubitObstruction ICO.QubitLink ICO.TensorRowOperators ICO.TensorBitOrder
open Matrix
open scoped BigOperators ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section

/-- A finite ordered circuit with arbitrary subnormalized preprocessing and
trace-preserving middle/final continuations. All memory dimensions may vary
from one classical branch to another. -/
structure Branch where
  M : Type
  N : Type
  K : Type
  [finiteM : Fintype M]
  [finiteN : Fintype N]
  [finiteK : Fintype K]
  [decideM : DecidableEq M]
  [decideN : DecidableEq N]
  [decideK : DecidableEq K]
  pre : Matrix (Fin 2 × M) (Fin 2) ℂ
  mid : Matrix (Fin 2 × N) (Fin 2 × M) ℂ
  post : Matrix (Fin 4 × K) (Fin 2 × N) ℂ
  mid_isometry : midᴴ * mid = 1
  post_isometry : postᴴ * post = 1

attribute [instance] Branch.finiteM Branch.finiteN Branch.finiteK
  Branch.decideM Branch.decideN Branch.decideK
def Branch.matrix (b : Branch) : Matrix (Fin 128) (Fin 128) ℂ :=
  circuitMatrix b.pre b.mid b.post

def Branch.reverse (b : Branch) : Matrix (Fin 128) (Fin 128) ℂ :=
  reverseMatrix b.pre b.mid b.post

def Branch.output (b : Branch) (U V : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  ∑ e : b.K, rankOne (vectorize (circuitKraus b.pre b.mid b.post U V e))

variable {J : Type*} [Fintype J]

def familyMatrix (b : J → Branch) : Matrix (Fin 128) (Fin 128) ℂ := ∑ j, (b j).matrix
def reverseFamilyMatrix (b : J → Branch) : Matrix (Fin 128) (Fin 128) ℂ := ∑ j, (b j).reverse
def familyOutput (b : J → Branch) (U V : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  ∑ j, (b j).output U V

theorem periodic_sum (C : J → Matrix (Fin 128) (Fin 128) ℂ) :
    periodicTensor (∑ j, C j) = ∑ j, periodicTensor (C j) := by
  ext i j
  simp [periodicTensor, Matrix.sum_apply]

theorem familyMatrix_pos (b : J → Branch) : (familyMatrix b).PosSemidef := by
  have h : familyMatrix b = ∑ z : (j : J) × (b j).K,
      rankOne (circuitVectors (b z.1).pre (b z.1).mid (b z.1).post z.2) := by
    simp [familyMatrix, Branch.matrix, matrix_decomposition, Fintype.sum_sigma]
  rw [h]
  exact sum_rankOne_pos _

theorem reverseFamilyMatrix_pos (b : J → Branch) : (reverseFamilyMatrix b).PosSemidef := by
  have h : reverseFamilyMatrix b = ∑ z : (j : J) × (b j).K,
      rankOne (reverseVectors (b z.1).pre (b z.1).mid (b z.1).post z.2) := by
    simp [reverseFamilyMatrix, Branch.reverse, reverse_decomposition, Fintype.sum_sigma]
  rw [h]
  exact sum_rankOne_pos _

theorem familyMatrix_rows (b : J → Branch) (k : Nat) :
    abRow k (periodicTensor (familyMatrix b)) = 0 := by
  unfold familyMatrix
  rw [periodic_sum,map_sum]
  have h (j : J) : abRow k (periodicTensor (b j).matrix) = 0 :=
    matrix_abRows _ _ _ (b j).mid_isometry (b j).post_isometry k
  simp [h]

theorem reverseFamilyMatrix_rows (b : J → Branch) (k : Nat) :
    baRow k (periodicTensor (reverseFamilyMatrix b)) = 0 := by
  unfold reverseFamilyMatrix
  rw [periodic_sum,map_sum]
  have h (j : J) : baRow k (periodicTensor (b j).reverse) = 0 :=
    matrix_baRows _ _ _ (b j).mid_isometry (b j).post_isometry k
  simp [h]

theorem linked_family (b : J → Branch) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    linkMatrix U V * familyMatrix b * (linkMatrix U V)ᴴ = familyOutput b U V := by
  simp [familyMatrix, familyOutput, Branch.matrix, Branch.output,
    Matrix.mul_sum, Matrix.sum_mul, linked_circuitMatrix]

theorem linked_reverseFamily (b : J → Branch) (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    linkMatrix U V * reverseFamilyMatrix b * (linkMatrix U V)ᴴ = familyOutput b V U := by
  simp [reverseFamilyMatrix, familyOutput, Branch.reverse, Branch.output,
    Matrix.mul_sum, Matrix.sum_mul, linked_reverseMatrix]

attribute [local irreducible] familyMatrix reverseFamilyMatrix familyOutput
  Branch.matrix Branch.reverse Branch.output

/-- No finite classical family of actual circuits, with either first-query
order and arbitrary branch-dependent memory sizes, implements the diluted
switch exactly on all channels. -/
theorem no_circuit_family {L : Type*} [Fintype L]
    (lambda mu : ℝ) (hl0 : 0 < lambda) (hl1 : lambda ≤ 1) (hm0 : 0 < mu) (hm1 : mu ≤ 1)
    (bA : J → Branch) (bB : L → Branch)
    (hOutput : ∀ U V : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
      (∑ i, (U i)ᴴ * U i) = 1 → (∑ j, (V j)ᴴ * V j) = 1 →
      (∑ i, ∑ j, (familyOutput bA (U i) (V j) + familyOutput bB (V j) (U i))) =
        dilutedSwitchOutput lambda mu U V) : False := by
  apply no_positive_ordered_switch lambda mu hl0 hl1 hm0 hm1
    (familyMatrix bA) (reverseFamilyMatrix bB) (familyMatrix_pos bA) (reverseFamilyMatrix_pos bB)
    (fun k _ => familyMatrix_rows bA k) (fun k _ => reverseFamilyMatrix_rows bB k)
  intro U V hU hV
  simp only [Matrix.mul_add, Matrix.add_mul, linked_family, linked_reverseFamily]
  exact hOutput U V hU hV

#print axioms no_circuit_family
end
end ICO.GeneralOrderedQubitFamilies

