import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

/-! Positive sums of rank-one matrices cannot cancel outside a subspace.
This is the support step in the exact-switch obstruction. The input is an
actual equality of finite matrices, rather than a support axiom. -/

namespace ICO.PositiveSupport

open Matrix
open scoped ComplexConjugate

noncomputable section

variable {N I J : Type*} [Fintype N] [Fintype I] [Fintype J]

def rankOne (v : N → ℂ) : Matrix N N ℂ :=
  Matrix.vecMulVec v (star v)

def overlap (x v : N → ℂ) : ℂ := star x ⬝ᵥ v

def quadratic (M : Matrix N N ℂ) (x : N → ℂ) : ℝ :=
  (star x ⬝ᵥ (M *ᵥ x)).re

theorem rankOne_quadratic (v x : N → ℂ) :
    quadratic (rankOne v) x = Complex.normSq (overlap x v) := by
  have h : star x ⬝ᵥ (rankOne v *ᵥ x) =
      overlap x v * star (overlap x v) := by
    simp [rankOne, Matrix.vecMulVec_apply, overlap, Matrix.mulVec, dotProduct,
      Finset.mul_sum, Finset.sum_mul, star_sum, StarMul.star_mul,
      mul_assoc, mul_left_comm, mul_comm]
    exact Finset.sum_comm
  unfold quadratic
  rw [h]
  simpa using congrArg Complex.re (Complex.mul_conj (overlap x v))

theorem sum_rankOne_quadratic (v : I → N → ℂ) (x : N → ℂ) :
    quadratic (∑ i, rankOne (v i)) x =
      ∑ i, Complex.normSq (overlap x (v i)) := by
  have h : quadratic (∑ i, rankOne (v i)) x =
      ∑ i, quadratic (rankOne (v i)) x := by
    unfold quadratic
    simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply,
      Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    calc
      (∑ a : N, ∑ b : N, ∑ i : I,
          (star x a * (rankOne (v i) a b * x b)).re) =
          ∑ a : N, ∑ i : I, ∑ b : N,
            (star x a * (rankOne (v i) a b * x b)).re := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [h]
  simp_rw [rankOne_quadratic]

theorem each_overlap_zero_of_sum_eq
    (v : I → N → ℂ) (w : J → N → ℂ)
    (h : (∑ i, rankOne (v i)) = ∑ j, rankOne (w j))
    (x : N → ℂ) (hw : ∀ j, overlap x (w j) = 0) (i : I) :
    overlap x (v i) = 0 := by
  have hsum : (∑ k, Complex.normSq (overlap x (v k))) = 0 := by
    rw [← sum_rankOne_quadratic, h, sum_rankOne_quadratic]
    simp [hw]
  have hi : Complex.normSq (overlap x (v i)) ≤
      ∑ k, Complex.normSq (overlap x (v k)) :=
    Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (overlap x (v k)))
      (Finset.mem_univ i)
  rw [hsum] at hi
  exact Complex.normSq_eq_zero.mp (le_antisymm hi (Complex.normSq_nonneg _))

def euclidean (v : N → ℂ) : EuclideanSpace ℂ N :=
  (WithLp.equiv 2 (N → ℂ)).symm v

theorem inner_euclidean (x v : N → ℂ) :
    @inner ℂ (EuclideanSpace ℂ N) _ (euclidean x) (euclidean v) = overlap x v := by
  change v ⬝ᵥ star x = star x ⬝ᵥ v
  exact dotProduct_comm _ _

/-- Each vector of any rank-one decomposition lies in a subspace containing
the vectors of an equal positive decomposition. -/
theorem each_mem_of_sum_eq
    (S : Submodule ℂ (EuclideanSpace ℂ N))
    (v : I → N → ℂ) (w : J → N → ℂ)
    (h : (∑ i, rankOne (v i)) = ∑ j, rankOne (w j))
    (hw : ∀ j, euclidean (w j) ∈ S) (i : I) :
    euclidean (v i) ∈ S := by
  rw [← S.orthogonal_orthogonal]
  apply (Submodule.mem_orthogonal _ _).2
  intro x hx
  let x' : N → ℂ := (WithLp.equiv 2 (N → ℂ)) x
  have hxe : euclidean x' = x := by simp [euclidean, x']
  have hwzero : ∀ j, overlap x' (w j) = 0 := by
    intro j
    rw [← inner_euclidean, hxe]
    exact Submodule.inner_left_of_mem_orthogonal (hw j) hx
  rw [← hxe, inner_euclidean]
  exact each_overlap_zero_of_sum_eq v w h x' hwzero i

#print axioms each_mem_of_sum_eq

theorem rankOne_mulVec {O : Type*} [Fintype O]
    (L : Matrix O N ℂ) (v : N → ℂ) :
    rankOne (L *ᵥ v) = L * rankOne v * Lᴴ := by
  ext a b
  simp [rankOne, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Finset.mul_sum, Finset.sum_mul, star_sum, StarMul.star_mul,
    mul_assoc, mul_left_comm, mul_comm]

theorem sum_rankOne_sandwich {O : Type*} [Fintype O]
    (L : Matrix O N ℂ) (v : I → N → ℂ) :
    L * (∑ i, rankOne (v i)) * Lᴴ = ∑ i, rankOne (L *ᵥ v i) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, ← rankOne_mulVec]

/-- For an actual linked output matrix, positivity prevents cancellation
outside the target's vector support, separately for every Kraus term. -/
theorem each_linked_mem {O : Type*} [Fintype O]
    (L : Matrix O N ℂ) (S : Submodule ℂ (EuclideanSpace ℂ O))
    (v : I → N → ℂ) (w : J → O → ℂ)
    (houtput : L * (∑ i, rankOne (v i)) * Lᴴ = ∑ j, rankOne (w j))
    (hw : ∀ j, euclidean (w j) ∈ S) (i : I) :
    euclidean (L *ᵥ v i) ∈ S := by
  apply each_mem_of_sum_eq S (fun i => L *ᵥ v i) w _ hw i
  rw [← sum_rankOne_sandwich]
  exact houtput

#print axioms each_linked_mem

end
end ICO.PositiveSupport
