import ICO.C6Bounds

/-! The paper's simpler uniform-sector cache bound. The exponential query
threshold is unchanged; a small numerical constant absorbs the looseness. -/
namespace ICO.C6UniformBounds
open ICO.C6Bounds
noncomputable section
set_option maxHeartbeats 1600000

def uniformCacheError (q : ℕ) (d : ℝ) : ℝ := 6*(q:ℝ)*((q-1:ℕ):ℝ)/d

def uniformError (q : ℕ) (d r : ℝ) : ℝ :=
  error q d r-cacheError q d+uniformCacheError q d

theorem uniformError_formula (q : ℕ) (d r : ℝ) :
    uniformError q d r=18*(2*q)*(2*q+1)/r^2+2*forwardError q d+
      14*q*creatorError (2*q) d+2*birthError q d+
      2*q*((q-1:ℕ):ℝ)/d+uniformCacheError q d := by
  unfold uniformError error
  ring

theorem uniformError_le {q : ℕ} {r : ℝ} (hq : 1≤q) (hqr : (q:ℝ)≤r/100) :
    uniformError q (r^16) r≤215/10000 := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  obtain ⟨hr,h24,hD⟩ := radius_dimensions hq' hqr
  have hr2 : 0<r^2 := sq_pos_of_pos hr
  have hd2 : r^2≤r^16 := by linarith
  have hq2 : (q:ℝ)^2≤r^2/10000 := by
    have hh := mul_self_le_mul_self (by positivity : (0:ℝ)≤q) hqr
    nlinarith
  have hm : ((q-1:ℕ):ℝ)≤q := by exact_mod_cast Nat.sub_le q 1
  have hc : uniformCacheError q (r^16)≤6/10000 := by
    unfold uniformCacheError
    apply (div_le_div_of_nonneg_left (by positivity) hr2 hd2).trans
    apply (div_le_iff₀ hr2).mpr
    nlinarith
  have hnon : 0≤cacheError q (r^16) := by unfold cacheError; positivity
  have he := error_le hq hqr
  unfold uniformError
  linarith

theorem uniformError_lt_one_third {q : ℕ} {r : ℝ} (hq : 1≤q) (hqr : (q:ℝ)≤r/100) :
    uniformError q (r^16) r<1/3 := by
  have hh := uniformError_le hq hqr
  linarith

#print axioms uniformError_le
end
end ICO.C6UniformBounds
