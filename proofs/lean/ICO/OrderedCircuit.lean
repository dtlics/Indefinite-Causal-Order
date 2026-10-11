import ICO.CircuitOutput

/-! # A genuine two-query circuit and its six-wire comb

`pre`, `mid`, and `post` are oracle-independent Stinespring matrices. Oracle
matrices are inserted through ordinary matrix composition and tensor identity
maps on the private memories. This file connects that circuit to the comb used
in the reverse-composition bound.
-/

open scoped ComplexOrder MatrixOrder
open Matrix QIT MeasureTheory ICO.CausalReverse ICO.ReverseIntegral
open ICO.CircuitComb ICO.CircuitOutput

namespace ICO.OrderedCircuit

set_option maxHeartbeats 100000
noncomputable section

universe u
variable {A M N K : Type u}
variable [Fintype A] [Fintype M] [Fintype N] [Fintype K]
variable [DecidableEq A] [DecidableEq M] [DecidableEq N] [DecidableEq K]

/-- The open wires before the final channel. They retain both the input and
output of each oracle slot, including the original input reference. -/
def preMiddleVector (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ) : FirstFourWires A × N → ℂ :=
  fun hn => ∑ m : M, mid (hn.1.1.1.2, hn.2) (hn.1.1.2, m) *
    pre (hn.1.2, m) hn.1.1.1.1

def circuitComb (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) : CMatrix (SixWires A) :=
  postprocessedComb post (rankOneMatrix (preMiddleVector pre mid))

theorem circuitComb_pos (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) : (circuitComb pre mid post).PosSemidef :=
  postprocessedComb_pos post (rankOneMatrix_pos _)

theorem circuitComb_causal (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (hpost : post.conjTranspose * post = 1) :
    partialTraceB (circuitComb pre mid post) =
      Matrix.kronecker (partialTraceB (rankOneMatrix (preMiddleVector pre mid)))
        (1 : CMatrix A) :=
  postprocessedComb_causal post hpost _

def postKraus (post : Matrix (A × K) (A × N) ℂ) (k : K) : Matrix A (A × N) ℂ :=
  fun f en => post (f, k) en

/-- Actual circuit composition: first `U`, then `V`, carrying the private
memory through each oracle call. -/
def circuitKraus (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (U V : CMatrix A) (k : K) : CMatrix A :=
  postKraus post k * Matrix.kronecker V (1 : CMatrix N) * mid *
    Matrix.kronecker U (1 : CMatrix M) * pre

theorem mul_kronecker_identity_entry {R : Type u} (X : Matrix R (A × M) ℂ)
    (U : CMatrix A) (r : R) (a : A) (m : M) :
    (X * Matrix.kronecker U (1 : CMatrix M)) r (a, m) =
      ∑ b : A, X r (b, m) * U b a := by
  simp [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type]

theorem circuitKraus_entry (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (U V : CMatrix A) (k : K) (f p : A) :
    circuitKraus pre mid post U V k f p =
      ∑ a : A, ∑ m : M, ∑ b : A, ∑ c : A, ∑ n : N, ∑ e : A,
        post (f, k) (e, n) * V e c * mid (c, n) (b, m) * U b a * pre (a, m) p := by
  have hm (b : A) (m : M) :
      ((postKraus post k * Matrix.kronecker V (1 : CMatrix N)) * mid) f (b, m) =
        ∑ c : A, ∑ n : N, ∑ e : A,
          post (f, k) (e, n) * V e c * mid (c, n) (b, m) := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp_rw [mul_kronecker_identity_entry]
    simp only [postKraus, Finset.sum_mul]
  unfold circuitKraus
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [mul_kronecker_identity_entry, hm]
  simp only [Finset.sum_mul]

theorem oraclePlug_mulVec (U V : CMatrix A) (v : SixWires A → ℂ) (p f : A) :
    (oraclePlug U V).mulVec v (p, f) =
      ∑ c : A, ∑ b : A, ∑ a : A, ∑ e : A,
        U b a * V e c * v (((((p, c), b), a), e), f) := by
  simp [oraclePlug, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_and]

theorem postLift_mulVec {H E F : Type u} [Fintype H] [Fintype E] [Fintype F]
    [DecidableEq H] [DecidableEq E] [DecidableEq F]
    (post : Matrix (F × K) (E × N) ℂ) (k : K) (v : H × N → ℂ)
    (h : H) (e : E) (f : F) :
    (postLift post k).mulVec v ((h, e), f) =
      ∑ n : N, post (f, k) (e, n) * v (h, n) := by
  simp [postLift, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem plugged_branch (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (U V : CMatrix A) (k : K) :
    (oraclePlug U V).mulVec
      ((postLift post k).mulVec (preMiddleVector pre mid)) =
      targetVector (circuitKraus pre mid post U V k) := by
  ext pf
  rcases pf with ⟨p, f⟩
  rw [show targetVector (circuitKraus pre mid post U V k) (p, f) =
    circuitKraus pre mid post U V k f p by rfl, circuitKraus_entry]
  rw [oraclePlug_mulVec]
  simp only [postLift_mulVec, preMiddleVector, Finset.mul_sum]
  let perm : (A × A × A × A × N × M) ≃ (A × M × A × A × N × A) :=
    { toFun := fun x => (x.2.2.1, x.2.2.2.2.2, x.2.1, x.1, x.2.2.2.2.1, x.2.2.2.1)
      invFun := fun x => (x.2.2.2.1, x.2.2.1, x.1, x.2.2.2.2.2, x.2.2.2.2.1, x.2.1)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hs := perm.sum_comp (fun x => post (f, k) (x.2.2.2.2.2, x.2.2.2.2.1) *
    V x.2.2.2.2.2 x.2.2.2.1 * mid (x.2.2.2.1, x.2.2.2.2.1) (x.2.2.1, x.2.1) *
    U x.2.2.1 x.1 * pre (x.1, x.2.1) p)
  have hs' :
      (∑ c : A, ∑ b : A, ∑ a : A, ∑ e : A, ∑ n : N, ∑ m : M,
        post (f, k) (e, n) * V e c * mid (c, n) (b, m) * U b a * pre (a, m) p) =
      ∑ a : A, ∑ m : M, ∑ b : A, ∑ c : A, ∑ n : N, ∑ e : A,
        post (f, k) (e, n) * V e c * mid (c, n) (b, m) * U b a * pre (a, m) p := by
    simpa only [Fintype.sum_prod_type] using hs
  rw [← hs']
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Plugging the comb gives exactly the Choi matrix of the ordinary circuit
with its final environment discarded. -/
theorem outputChoi_eq_circuit (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (U V : CMatrix A) :
    outputChoi (circuitComb pre mid post) U V =
      ∑ k : K, rankOneMatrix (targetVector (circuitKraus pre mid post U V k)) := by
  unfold outputChoi circuitComb postprocessedComb
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
    ← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
    plugged_branch]

/-- The six-wire construction is the standard QIT Choi matrix of the actual
Kraus-form circuit map. -/
theorem outputChoi_eq_mapChoi (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (U V : CMatrix A) :
    outputChoi (circuitComb pre mid post) U V =
      MatrixMap.choi (MatrixMap.ofKraus (circuitKraus pre mid post U V)) := by
  rw [outputChoi_eq_circuit, MatrixMap.choi_ofKraus]
  rfl

theorem outputChoi_outcome_eq_circuit (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (U V : CMatrix A) (S : Finset K) :
    outputChoi (outcomeComb post (rankOneMatrix (preMiddleVector pre mid)) S) U V =
      ∑ k ∈ S, rankOneMatrix (targetVector (circuitKraus pre mid post U V k)) := by
  unfold outputChoi outcomeComb
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
    ← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
    plugged_branch]

def midBlock (mid : Matrix (A × N) (A × M) ℂ) (b : A) : Matrix (A × N) M ℂ :=
  fun cn m => mid cn (b, m)

theorem midBlock_isometry (mid : Matrix (A × N) (A × M) ℂ)
    (hmid : mid.conjTranspose * mid = 1) (b : A) :
    (midBlock mid b).conjTranspose * midBlock mid b = 1 := by
  ext m n
  have h := congrFun (congrFun hmid (b, m)) (b, n)
  simpa [midBlock, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

theorem isometry_rankOne_trace {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (L : Matrix I J ℂ)
    (hL : L.conjTranspose * L = 1) (v : J → ℂ) :
    (rankOneMatrix (L.mulVec v)).trace = (rankOneMatrix v).trace := by
  rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
    Matrix.trace_mul_cycle, hL, Matrix.one_mul]

theorem preMiddle_slice_trace (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ) (hmid : mid.conjTranspose * mid = 1)
    (p a b : A) :
    (∑ c : A, ∑ n : N,
      preMiddleVector pre mid ((((p, c), b), a), n) *
        star (preMiddleVector pre mid ((((p, c), b), a), n))) =
      ∑ m : M, pre (a, m) p * star (pre (a, m) p) := by
  have h := isometry_rankOne_trace (midBlock mid b) (midBlock_isometry mid hmid b)
    (fun m => pre (a, m) p)
  simpa [Matrix.trace, rankOneMatrix_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, midBlock, preMiddleVector] using h

theorem sum_reverse_three {R : Type*} [AddCommMonoid R] (g : A → A → A → R) :
    (∑ c : A, ∑ b : A, ∑ a : A, g c b a) =
      ∑ a : A, ∑ b : A, ∑ c : A, g c b a := by
  calc
    _ = ∑ b : A, ∑ c : A, ∑ a : A, g c b a := Finset.sum_comm
    _ = ∑ b : A, ∑ a : A, ∑ c : A, g c b a := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem preMiddle_trace (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ) (hmid : mid.conjTranspose * mid = 1) :
    (rankOneMatrix (preMiddleVector pre mid)).trace =
      (Fintype.card A : ℂ) * (pre.conjTranspose * pre).trace := by
  have heq : (rankOneMatrix (preMiddleVector pre mid)).trace =
      ∑ p : A, ∑ a : A, ∑ b : A, ∑ c : A, ∑ n : N,
        preMiddleVector pre mid ((((p, c), b), a), n) *
          star (preMiddleVector pre mid ((((p, c), b), a), n)) := by
    simp only [Matrix.trace, rankOneMatrix_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p hp
    exact sum_reverse_three _
  rw [heq]
  simp_rw [preMiddle_slice_trace pre mid hmid]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Finset.mul_sum, mul_comm]

theorem circuitComb_trace (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ) (hmid : mid.conjTranspose * mid = 1)
    (post : Matrix (A × K) (A × N) ℂ) (hpost : post.conjTranspose * post = 1) :
    (circuitComb pre mid post).trace.re =
      (Fintype.card A : ℝ) ^ 2 * (pre.conjTranspose * pre).trace.re := by
  rw [causal_trace_identity _ _ (circuitComb_causal pre mid post hpost),
    partialTraceB_trace, preMiddle_trace pre mid hmid]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  ring

def circuitOverlap (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (U V T : CMatrix A) : ℝ :=
  ((Fintype.card A : ℝ) ^ 2)⁻¹ * tracePair
    (∑ k : K, rankOneMatrix (targetVector (circuitKraus pre mid post U V k)))
    (rankOneMatrix (targetVector T))

theorem circuitOverlap_eq_outputOverlap (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ)
    (post : Matrix (A × K) (A × N) ℂ) (U V T : CMatrix A) :
    circuitOverlap pre mid post U V T = outputOverlap (circuitComb pre mid post) U V T := by
  unfold circuitOverlap outputOverlap
  rw [outputChoi_eq_circuit]

/-- A genuine two-query circuit, including a possibly subnormalized first
branch, obeys the reverse-composition bound. No causal-comb equation or reverse
score bound is assumed. -/
theorem circuit_reverse_bound [Nontrivial A]
    (pre : Matrix (A × M) A ℂ)
    (mid : Matrix (A × N) (A × M) ℂ) (hmid : mid.conjTranspose * mid = 1)
    (post : Matrix (A × K) (A × N) ℂ) (hpost : post.conjTranspose * post = 1) :
    (∫ U : Matrix.unitaryGroup A ℂ, ∫ V : Matrix.unitaryGroup A ℂ,
      circuitOverlap pre mid post (U : CMatrix A) (V : CMatrix A)
        ((U : CMatrix A) * (V : CMatrix A))
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
      ((pre.conjTranspose * pre).trace.re / (Fintype.card A : ℝ)) *
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  simp_rw [circuitOverlap_eq_outputOverlap]
  have h := causal_outputOverlap_bound (circuitComb pre mid post)
    (partialTraceB (rankOneMatrix (preMiddleVector pre mid)))
    (circuitComb_pos pre mid post) (partialTraceB_posSemidef (rankOneMatrix_pos _))
    (circuitComb_causal pre mid post hpost)
  rw [circuitComb_trace pre mid hmid post hpost] at h
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hweight : (Fintype.card A : ℝ) ^ 2 * (pre.conjTranspose * pre).trace.re /
      (Fintype.card A : ℝ) ^ 3 =
      (pre.conjTranspose * pre).trace.re / (Fintype.card A : ℝ) := by
    field_simp [hd]
    <;> ring
  simpa only [hweight] using h

theorem normalized_circuit_reverse_bound [Nontrivial A]
    (pre : Matrix (A × M) A ℂ) (hpre : pre.conjTranspose * pre = 1)
    (mid : Matrix (A × N) (A × M) ℂ) (hmid : mid.conjTranspose * mid = 1)
    (post : Matrix (A × K) (A × N) ℂ) (hpost : post.conjTranspose * post = 1) :
    (∫ U : Matrix.unitaryGroup A ℂ, ∫ V : Matrix.unitaryGroup A ℂ,
      circuitOverlap pre mid post (U : CMatrix A) (V : CMatrix A)
        ((U : CMatrix A) * (V : CMatrix A))
      ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤
        ((Fintype.card A : ℝ)⁻¹ +
          (Fintype.card A : ℝ) / ((Fintype.card A : ℝ) ^ 2 - 1)) ^ 2 := by
  have h := circuit_reverse_bound pre mid hmid post hpost
  rw [hpre] at h
  simpa using h

end
end ICO.OrderedCircuit




