import QIT.States.TraceNorm.Variational
import QIT.States.Geometry.FuchsVdG
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-! Dimension-independent vector-to-state and pure-query hybrid bounds,
including unequal norms and partial trace. -/

namespace ICO.PureHybrid

open Matrix QIT
open scoped BigOperators ComplexConjugate InnerProductSpace

noncomputable section

variable {a b : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

def outer (x y : EuclideanSpace ℂ a) : CMatrix a :=
  Matrix.vecMulVec (fun i => x i) (fun j => star (y j))

theorem unitary_action_norm (U : Matrix.unitaryGroup a ℂ)
    (x : EuclideanSpace ℂ a) :
    ‖(Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ)) (U : CMatrix a) x‖ = ‖x‖ := by
  have hu : (U : CMatrix a) ∈ unitary (CMatrix a) :=
    ⟨Matrix.mem_unitaryGroup_iff'.mp U.2, Matrix.mem_unitaryGroup_iff.mp U.2⟩
  have hc : (Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ)) (U : CMatrix a) ∈
      unitary (EuclideanSpace ℂ a →L[ℂ] EuclideanSpace ℂ a) := by
    rw [Unitary.mem_iff] at hu ⊢
    constructor
    · rw [← map_star, ← map_mul, hu.1, map_one]
    · rw [← map_star, ← map_mul, hu.2, map_one]
  exact ContinuousLinearMap.norm_map_of_mem_unitary hc x

theorem outer_trace_unitary (x y : EuclideanSpace ℂ a)
    (U : CMatrix a) :
    (outer x y * U).trace = ⟪y, (Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ)) U x⟫_ℂ := by
  rw [Matrix.trace_mul_comm, outer, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  have hx : (Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ)) U x =
      WithLp.toLp 2 (U *ᵥ (fun j => x j)) :=
    Matrix.toEuclideanCLM_toLp U (fun j => x j)
  rw [hx]
  simp [dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem outer_traceNorm_le (x y : EuclideanSpace ℂ a) :
    QIT.traceNorm (outer x y) ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨U, hU⟩ := QIT.traceNorm_variational_exists_unitary_abs_trace (outer x y)
  rw [← hU, outer_trace_unitary]
  calc
    ‖⟪y, (Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ)) (U : CMatrix a) x⟫_ℂ‖ ≤
        ‖y‖ * ‖(Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ)) (U : CMatrix a) x‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [unitary_action_norm]; ring

theorem outer_sub_expansion (x y : EuclideanSpace ℂ a) :
    outer x x - outer y y = outer (x - y) x + outer y (x - y) := by
  ext i j
  simp [outer, Matrix.vecMulVec_apply, star_sub]
  ring

theorem pure_traceNorm_le (x y : EuclideanSpace ℂ a) :
    QIT.traceNorm (outer x x - outer y y) ≤
      (‖x‖ + ‖y‖) * ‖x - y‖ := by
  rw [outer_sub_expansion]
  calc
    QIT.traceNorm (outer (x - y) x + outer y (x - y)) ≤
        QIT.traceNorm (outer (x - y) x) + QIT.traceNorm (outer y (x - y)) :=
      QIT.traceNorm_add_le _ _
    _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ :=
      add_le_add (outer_traceNorm_le _ _) (outer_traceNorm_le _ _)
    _ = _ := by ring

theorem subnormalized_pure_distance_le (x y : EuclideanSpace ℂ a)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    (1 / 2 : ℝ) * QIT.traceNorm (outer x x - outer y y) ≤ ‖x - y‖ := by
  have h := pure_traceNorm_le x y
  have hn := norm_nonneg (x - y)
  nlinarith

theorem partial_trace_pure_distance_le (x y : EuclideanSpace ℂ (a × b))
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    (1 / 2 : ℝ) * QIT.traceNorm
      (QIT.partialTraceA (outer x x - outer y y)) ≤ ‖x - y‖ := by
  exact (mul_le_mul_of_nonneg_left (QIT.traceNorm_partialTraceA_le _)
    (by norm_num)).trans (subnormalized_pure_distance_le x y hx hy)

theorem vector_hybrid {E : ℕ → Type*}
    [∀ t, SeminormedAddCommGroup (E t)] [∀ t, NormedSpace ℂ (E t)]
    (x y : (t : ℕ) → E t)
    (F : (t : ℕ) → E t →L[ℂ] E (t + 1)) (ε : ℕ → ℝ)
    (hinit : x 0 = y 0) (hF : ∀ t, ‖F t‖ ≤ 1)
    (hy : ∀ t, y (t + 1) = F t (y t))
    (hloc : ∀ t, ‖x (t + 1) - F t (x t)‖ ≤ ε t) (n : ℕ) :
    ‖x n - y n‖ ≤ ∑ t ∈ Finset.range n, ε t := by
  induction n with
  | zero => simp [hinit]
  | succ n ih =>
    have hstep : ‖x (n + 1) - y (n + 1)‖ ≤ ε n + ‖x n - y n‖ := by
      rw [hy n]
      calc
        ‖x (n + 1) - F n (y n)‖ =
            ‖(x (n + 1) - F n (x n)) + F n (x n - y n)‖ := by
          congr 1
          rw [map_sub]
          abel
        _ ≤ ‖x (n + 1) - F n (x n)‖ + ‖F n (x n - y n)‖ := norm_add_le _ _
        _ ≤ ε n + ‖x n - y n‖ := by
          apply add_le_add (hloc n)
          simpa only [one_mul] using (F n).le_of_opNorm_le (hF n) (x n - y n)
    rw [Finset.sum_range_succ]
    linarith

#print axioms partial_trace_pure_distance_le
#print axioms vector_hybrid

theorem vector_hybrid_upto {E : ℕ → Type*}
    [∀ t, SeminormedAddCommGroup (E t)] [∀ t, NormedSpace ℂ (E t)]
    (x y : (t : ℕ) → E t)
    (F : (t : ℕ) → E t →L[ℂ] E (t + 1)) (ε : ℕ → ℝ) (n : ℕ)
    (hinit : x 0 = y 0) (hF : ∀ t < n, ‖F t‖ ≤ 1)
    (hy : ∀ t < n, y (t + 1) = F t (y t))
    (hloc : ∀ t < n, ‖x (t + 1) - F t (x t)‖ ≤ ε t) :
    ‖x n - y n‖ ≤ ∑ t ∈ Finset.range n, ε t := by
  have hb : ∀ k ≤ n, ‖x k - y k‖ ≤ ∑ t ∈ Finset.range k, ε t := by
    intro k
    induction k with
    | zero => intro hk; simp [hinit]
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hprev := ih (by omega)
      have hstep : ‖x (k + 1) - y (k + 1)‖ ≤ ε k + ‖x k - y k‖ := by
        rw [hy k hkn]
        calc
          ‖x (k + 1) - F k (y k)‖ =
              ‖(x (k + 1) - F k (x k)) + F k (x k - y k)‖ := by
            congr 1
            rw [map_sub]
            abel
          _ ≤ ‖x (k + 1) - F k (x k)‖ + ‖F k (x k - y k)‖ := norm_add_le _ _
          _ ≤ ε k + ‖x k - y k‖ := by
            apply add_le_add (hloc k hkn)
            simpa only [one_mul] using
              (F k).le_of_opNorm_le (hF k hkn) (x k - y k)
      rw [Finset.sum_range_succ]
      linarith
  exact hb n le_rfl

#print axioms vector_hybrid_upto

end
end ICO.PureHybrid
