import ICO.TestingBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Scalar bounds for the correlated SAME/MUB comparison. The radius is
`d = r^16`; no quantum comparison theorem is asserted in this module. -/
namespace ICO.C6Bounds
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def forwardError (q : ℕ) (d : ℝ) : ℝ :=
  ∑ i : Fin q, Real.sqrt (2*(2*(i:ℝ)+1)/(d-2*(i:ℝ)))

def creatorError (t d : ℝ) : ℝ := Real.sqrt (2*t*(t+1)/d)+t/d

def birthError (q : ℕ) (d : ℝ) : ℝ :=
  ∑ i : Fin q, if i.val=0 then 0 else
    Real.sqrt ((2*(i:ℝ)-1)/(d-(i:ℝ)+1)) + Real.sqrt (2*(i:ℝ)/(d-(i:ℝ)))

def cacheError (q : ℕ) (d : ℝ) : ℝ := 3*((q-1:ℕ):ℝ)*((q-2:ℕ):ℝ)/d

def error (q : ℕ) (d r : ℝ) : ℝ :=
  18*(2*q)*(2*q+1)/r^2 + 2*forwardError q d +
    14*q*creatorError (2*q) d + 2*birthError q d +
    2*q*((q-1:ℕ):ℝ)/d + cacheError q d

theorem radius_dimensions {q r : ℝ} (hq : 1≤q) (hqr : q≤r/100) :
    0<r ∧ r^2≤r^4 ∧ r^4≤r^16-2*q := by
  have hr := ICO.TestingBounds.radius_ge_hundred hq hqr
  have hr1 : 1≤r := by linarith
  have h12 : 2≤r^12 := by
    have hh := pow_le_pow_right₀ hr1 (show (1:ℕ)≤12 by norm_num)
    norm_num at hh
    linarith
  have h16 : 2*r^4≤r^16 := by
    have hh := mul_le_mul_of_nonneg_right h12 (pow_nonneg (by linarith : 0≤r) 4)
    nlinarith only [hh]
  have h14 : r≤r^4 := by
    simpa using pow_le_pow_right₀ hr1 (show (1:ℕ)≤4 by norm_num)
  have h24 : r^2≤r^4 := pow_le_pow_right₀ hr1 (by norm_num)
  exact ⟨by linarith, h24, by linarith⟩

theorem radical_majorant {x D a r : ℝ} (hr : 0<r) (ha : 0≤a)
    (hD : r^4≤D) (hx : x≤a^2) : Real.sqrt (x/D)≤a/r^2 := by
  have hr2 : 0<r^2 := sq_pos_of_pos hr
  have hr4 : 0<r^4 := pow_pos hr 4
  have hD0 : 0<D := hr4.trans_le hD
  apply (Real.sqrt_le_left (by positivity : 0≤a/r^2)).mpr
  apply (div_le_iff₀ hD0).mpr
  have hh := mul_le_mul_of_nonneg_left hD (sq_nonneg (a/r^2))
  have he : (a/r^2)^2*r^4 = a^2 := by field_simp
  rw [he] at hh
  exact hx.trans hh

theorem forwardError_le {q : ℕ} {r : ℝ} (hq : 1≤q) (hqr : (q:ℝ)≤r/100) :
    forwardError q (r^16)≤2*(q:ℝ)^2/r^2 := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  obtain ⟨hr,h24,hD⟩ := radius_dimensions hq' hqr
  have hi (i:Fin q) : (i:ℝ)+1≤q := by exact_mod_cast i.isLt
  have hi0 (i:Fin q) : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg _
  have hb (i:Fin q) : Real.sqrt (2*(2*(i:ℝ)+1)/(r^16-2*(i:ℝ)))≤2*q/r^2 := by
    apply radical_majorant hr (by positivity)
    · linarith [hi i]
    · nlinarith [hi i, hi0 i]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hb i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  unfold forwardError
  convert hh using 1 <;> ring

theorem birthError_le {q : ℕ} {r : ℝ} (hq : 1≤q) (hqr : (q:ℝ)≤r/100) :
    birthError q (r^16)≤4*(q:ℝ)^2/r^2 := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  obtain ⟨hr,h24,hD⟩ := radius_dimensions hq' hqr
  have hb (i:Fin q) : (if i.val=0 then 0 else
      Real.sqrt ((2*(i:ℝ)-1)/(r^16-(i:ℝ)+1)) +
        Real.sqrt (2*(i:ℝ)/(r^16-(i:ℝ))))≤4*q/r^2 := by
    have hi : (i:ℝ)+1≤q := by exact_mod_cast i.isLt
    have hi0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg _
    split_ifs
    · positivity
    · have hb := radical_majorant (a:=2*q) (x:=2*(i:ℝ)-1)
        (D:=r^16-(i:ℝ)+1) hr (by positivity) (by linarith) (by nlinarith)
      have hc := radical_majorant (a:=2*q) (x:=2*(i:ℝ))
        (D:=r^16-(i:ℝ)) hr (by positivity) (by linarith) (by nlinarith)
      ring_nf at hb hc ⊢
      linarith
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hb i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  unfold birthError
  convert hh using 1 <;> ring

theorem creatorError_le {q r : ℝ} (hq : 1≤q) (hqr : q≤r/100) :
    creatorError (2*q) (r^16)≤6*q/r^2 := by
  obtain ⟨hr,h24,hD⟩ := radius_dimensions hq hqr
  have hr2 : 0<r^2 := sq_pos_of_pos hr
  have hd0 : 0<r^16 := pow_pos hr 16
  have hrad := radical_majorant (a:=4*q) (x:=2*(2*q)*(2*q+1))
    (D:=r^16) hr (by linarith) (by linarith) (by nlinarith)
  have hd2 : r^2≤r^16 := by linarith
  have hfrac : 2*q/r^16≤2*q/r^2 :=
    div_le_div_of_nonneg_left (by linarith) hr2 hd2
  unfold creatorError
  ring_nf at hrad hfrac ⊢
  linarith

theorem error_le {q : ℕ} {r : ℝ} (hq : 1≤q) (hqr : (q:ℝ)≤r/100) :
    error q (r^16) r≤209/10000 := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  obtain ⟨hr,h24,hD⟩ := radius_dimensions hq' hqr
  have hr2 : 0<r^2 := sq_pos_of_pos hr
  have hd0 : 0<r^16 := pow_pos hr 16
  have hd2 : r^2≤r^16 := by linarith
  have hq2 : (q:ℝ)^2≤r^2/10000 := by
    have hh := mul_self_le_mul_self (by positivity : (0:ℝ)≤q) hqr
    nlinarith
  have hbase : (q:ℝ)^2/r^2≤1/10000 := (div_le_iff₀ hr2).mpr (by linarith)
  have hm1 : ((q-1:ℕ):ℝ)≤q := by exact_mod_cast Nat.sub_le q 1
  have hm2 : ((q-2:ℕ):ℝ)≤q := by exact_mod_cast Nat.sub_le q 2
  have hmain : 18*(2*(q:ℝ))*(2*q+1)/r^2≤108/10000 := by
    apply (div_le_iff₀ hr2).mpr
    nlinarith
  have hf := forwardError_le hq hqr
  have hb := birthError_le hq hqr
  have hc := creatorError_le hq' hqr
  have hc' := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ)≤14*q)
  have hcache : cacheError q (r^16)≤3*(q:ℝ)^2/r^2 := by
    unfold cacheError
    apply le_trans (div_le_div_of_nonneg_left (by positivity) hr2 hd2)
    apply (div_le_div_iff_of_pos_right hr2).mpr
    nlinarith [mul_le_mul hm1 hm2 (by positivity) (by positivity)]
  have hnorm : 2*(q:ℝ)*((q-1:ℕ):ℝ)/r^16≤2*(q:ℝ)^2/r^2 := by
    apply le_trans (div_le_div_of_nonneg_left (by positivity) hr2 hd2)
    apply (div_le_div_iff_of_pos_right hr2).mpr
    nlinarith
  unfold error
  ring_nf at hmain hf hb hc' hcache hnorm hbase ⊢
  linarith

theorem error_lt_one_third {q : ℕ} {r : ℝ} (hq : 1≤q) (hqr : (q:ℝ)≤r/100) :
    error q (r^16) r<1/3 := by
  have h := error_le hq hqr
  linarith

#print axioms error_le
end
end ICO.C6Bounds
