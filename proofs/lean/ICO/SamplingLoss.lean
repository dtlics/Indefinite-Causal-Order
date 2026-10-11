import ICO.SamplingCP

open scoped ComplexOrder MatrixOrder
open Matrix QIT ICO.InstrumentCompression ICO.FreshSamplingMaps ICO.SamplingCP

namespace ICO.SamplingLoss
set_option maxHeartbeats 600000
noncomputable section

/-- Union-bound loss after `t` previous calls and at most `q` remaining calls.
The previous calls and the remaining calls count both oracle types together. -/
def loss (r t q : ℕ) : ℝ := ∑ k ∈ Finset.range q, ((t : ℝ) + k) / r

theorem loss_nonneg (r t q : ℕ) : 0 ≤ loss r t q := by
  apply Finset.sum_nonneg
  intro k hk
  positivity

theorem loss_zero (r t : ℕ) : loss r t 0 = 0 := by simp [loss]

theorem loss_succ (r t q : ℕ) : loss r t (q + 1) = (t : ℝ) / r + loss r (t + 1) q := by
  rw [loss, Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  unfold loss
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  push_cast
  ring

theorem loss_initial (r q : ℕ) : loss r 0 q = (q : ℝ) * (q - 1) / (2 * r) := by
  have hsum : (∑ k ∈ Finset.range q, (k : ℝ)) = (q : ℝ) * (q - 1) / 2 := by
    induction q with
    | zero => simp
    | succ q ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  simp only [loss, Nat.cast_zero, zero_add, ← Finset.sum_div, hsum, div_div]

theorem step_loss {I : Type} [Fintype I] (r t : ℕ) (hr : 0 < r)
    (hn : Fintype.card I ≤ r) (ht : r - Fintype.card I ≤ t)
    (x L : ℝ) (hx : 0 ≤ x) (hL : 0 ≤ L) (y : I → ℝ)
    (hy : ∀ i, x - y i ≤ L * x) :
    x - (r : ℝ)⁻¹ * ∑ i, y i ≤ ((t : ℝ) / r + L) * x := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hn' : (Fintype.card I : ℝ) ≤ r := by exact_mod_cast hn
  have hnt : (r : ℝ) - Fintype.card I ≤ t := by
    rw [sub_le_iff_le_add]
    exact_mod_cast (show r ≤ t + Fintype.card I by omega)
  have hs : (Fintype.card I : ℝ) * (x - L*x) ≤ ∑ i, y i := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => show x-L*x ≤ y i by linarith [hy i])
  have hmissing : ((r : ℝ) - Fintype.card I) * x ≤ (t : ℝ)*x := mul_le_mul_of_nonneg_right hnt hx
  have hfuture : (Fintype.card I : ℝ) * (L*x) ≤ (r : ℝ)*(L*x) :=
    mul_le_mul_of_nonneg_right hn' (mul_nonneg hL hx)
  have hbase : (r : ℝ)*x - ∑ i, y i ≤ ((t : ℝ) + (r : ℝ)*L)*x := by nlinarith
  calc
    _ = ((r : ℝ)*x - ∑ i, y i) / r := by field_simp
    _ ≤ (((t : ℝ) + (r : ℝ)*L)*x) / r := div_le_div_of_nonneg_right hbase (le_of_lt hr')
    _ = _ := by field_simp

end
end ICO.SamplingLoss
