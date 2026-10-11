import ICO.PositiveSupport
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Ordered finite-dimensional Stinespring circuits produce the homogeneous
comb trace constraints. The first operation may be subnormalized; only the
middle and final continuations are required to preserve trace. -/
namespace ICO.OrderedCombSemantics
open Matrix ICO.PositiveSupport
open scoped BigOperators ComplexConjugate ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
noncomputable section

variable {I J A M N P F K H : Type*}
  [Fintype I] [Fintype J] [Fintype A] [Fintype M] [Fintype N]
  [Fintype P] [Fintype F] [Fintype K] [Fintype H]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq M]
  [DecidableEq N] [DecidableEq P] [DecidableEq F] [DecidableEq K] [DecidableEq H]

def partialTrace (C : Matrix (I × J) (I × J) ℂ) : Matrix I I ℂ :=
  fun i j => ∑ k : J, C (i,k) (j,k)

theorem isometry_pairing (W : Matrix I J ℂ) (hW : Wᴴ * W = 1)
    (x y : J → ℂ) : (W *ᵥ x) ⬝ᵥ star (W *ᵥ y) = x ⬝ᵥ star y := by
  rw [dotProduct_comm (W *ᵥ x), star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, hW, one_mulVec, dotProduct_comm]

def insertWire (a : A) (x : M → ℂ) : A × M → ℂ :=
  fun am => if am.1 = a then x am.2 else 0

theorem insertWire_pairing (a b : A) (x y : M → ℂ) :
    insertWire a x ⬝ᵥ star (insertWire b y) =
      if a = b then x ⬝ᵥ star y else 0 := by
  by_cases hab : a = b
  · subst b
    simp [insertWire, dotProduct, Fintype.sum_prod_type]
  · simp [insertWire, dotProduct, Fintype.sum_prod_type, hab, eq_comm]

def postLift (W : Matrix (F × K) (A × N) ℂ) (k : K) :
    Matrix ((H × A) × F) (H × N) ℂ :=
  fun i j => if i.1.1 = j.1 then W (i.2,k) (i.1.2,j.2) else 0

def postComb (W : Matrix (F × K) (A × N) ℂ) (B : Matrix (H × N) (H × N) ℂ) :
    Matrix ((H × A) × F) ((H × A) × F) ℂ :=
  ∑ k : K, postLift W k * B * (postLift W k)ᴴ

theorem postComb_pos (W : Matrix (F × K) (A × N) ℂ)
    {B : Matrix (H × N) (H × N) ℂ} (hB : B.PosSemidef) :
    (postComb W B).PosSemidef := by
  classical
  unfold postComb
  have hsum (S : Finset K) : (∑ k ∈ S, postLift W k * B * (postLift W k)ᴴ).PosSemidef := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (Matrix.PosSemidef.zero (n := (H × A) × F) (R := ℂ))
    | @insert k S hk ih =>
      rw [Finset.sum_insert hk]
      exact (hB.mul_mul_conjTranspose_same (postLift W k)).add ih
  exact hsum Finset.univ

theorem postComb_entry (W : Matrix (F × K) (A × N) ℂ)
    (B : Matrix (H × N) (H × N) ℂ) (h h' : H) (a a' : A) (f f' : F) :
    postComb W B ((h,a),f) ((h',a'),f') =
      ∑ k : K, ∑ n : N, ∑ m : N,
        W (f,k) (a,n) * B (h,n) (h',m) * star (W (f',k) (a',m)) := by
  simp [postComb, postLift, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul, apply_ite]
  apply Finset.sum_congr rfl
  intro k hk
  exact Finset.sum_comm

theorem column_sum (W : Matrix (F × K) (A × N) ℂ)
    (hW : Wᴴ * W = 1) (a a' : A) (n m : N) :
    (∑ f : F, ∑ k : K, W (f,k) (a,n) * star (W (f,k) (a',m))) =
      (1 : Matrix (A × N) (A × N) ℂ) (a,n) (a',m) := by
  have h := congrFun (congrFun hW (a',m)) (a,n)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, eq_comm, mul_comm] using h

theorem sum_four_swap {R : Type*} [AddCommMonoid R]
    (g : F → K → N → N → R) :
    (∑ f : F, ∑ k : K, ∑ n : N, ∑ m : N, g f k n m) =
      ∑ n : N, ∑ m : N, ∑ f : F, ∑ k : K, g f k n m := by
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (fk : F × K) (nm : N × N) => g fk.1 fk.2 nm.1 nm.2))

theorem postComb_trace (W : Matrix (F × K) (A × N) ℂ)
    (hW : Wᴴ * W = 1) (B : Matrix (H × N) (H × N) ℂ) :
    partialTrace (postComb W B) = Matrix.kronecker (partialTrace B) (1 : Matrix A A ℂ) := by
  ext ⟨h,a⟩ ⟨h',a'⟩
  change (∑ f : F, postComb W B ((h,a),f) ((h',a'),f)) = _
  simp_rw [postComb_entry]
  rw [sum_four_swap]
  have hp (n m : N) :
      (∑ f : F, ∑ k : K,
        W (f,k) (a,n) * B (h,n) (h',m) * star (W (f,k) (a',m))) =
        B (h,n) (h',m) * (1 : Matrix (A × N) (A × N) ℂ) (a,n) (a',m) := by
    rw [← column_sum W hW a a' n m]
    simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  simp_rw [hp]
  simp [partialTrace, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.ext_iff, ite_and, Finset.sum_mul]

abbrev FourWires (P A : Type*) := ((P × A) × A) × A
abbrev SixWires (P A F : Type*) := (FourWires P A × A) × F

def preMiddle (pre : Matrix (A × M) P ℂ) (mid : Matrix (A × N) (A × M) ℂ) :
    FourWires P A × N → ℂ :=
  fun hn => (mid *ᵥ insertWire hn.1.1.2 (fun m => pre (hn.1.1.1.2,m) hn.1.1.1.1))
    (hn.1.2,hn.2)

def circuitComb (pre : Matrix (A × M) P ℂ) (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (F × K) (A × N) ℂ) : Matrix (SixWires P A F) (SixWires P A F) ℂ :=
  postComb post (rankOne (preMiddle pre mid))

theorem circuitComb_decomposition (pre : Matrix (A × M) P ℂ)
    (mid : Matrix (A × N) (A × M) ℂ) (post : Matrix (F × K) (A × N) ℂ) :
    circuitComb pre mid post =
      ∑ k : K, rankOne (postLift post k *ᵥ preMiddle pre mid) := by
  unfold circuitComb postComb
  simp only [rankOne_mulVec]

def preComb (pre : Matrix (A × M) P ℂ) : Matrix (P × A) (P × A) ℂ :=
  fun pa qb => (fun m => pre (pa.2,m) pa.1) ⬝ᵥ star (fun m => pre (qb.2,m) qb.1)

theorem preMiddle_trace (pre : Matrix (A × M) P ℂ)
    (mid : Matrix (A × N) (A × M) ℂ) (hmid : midᴴ * mid = 1) :
    partialTrace (partialTrace (rankOne (preMiddle pre mid))) =
      Matrix.kronecker (preComb pre) (1 : Matrix A A ℂ) := by
  ext ⟨⟨p,ai⟩,ao⟩ ⟨⟨q,aj⟩,ap⟩
  change (∑ bi : A, ∑ n : N,
    (mid *ᵥ insertWire ao (fun m => pre (ai,m) p)) (bi,n) *
    star ((mid *ᵥ insertWire ap (fun m => pre (aj,m) q)) (bi,n))) = _
  have h := isometry_pairing mid hmid (insertWire ao (fun m => pre (ai,m) p))
    (insertWire ap (fun m => pre (aj,m) q))
  rw [insertWire_pairing] at h
  simpa [dotProduct, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, preComb] using h

theorem circuitComb_trace (pre : Matrix (A × M) P ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (F × K) (A × N) ℂ) (hpost : postᴴ * post = 1) :
    partialTrace (circuitComb pre mid post) =
      Matrix.kronecker (partialTrace (rankOne (preMiddle pre mid))) (1 : Matrix A A ℂ) :=
  postComb_trace post hpost _

#print axioms preMiddle_trace
#print axioms circuitComb_trace
end
end ICO.OrderedCombSemantics
