import ICO.MHWordDomainTwirl
import ICO.MHWordOccupationTurn

namespace ICO.MHWordSectorTwirl
open Matrix QIT MeasureTheory ICO.MHWordDistinct ICO.MHWordRotation
  ICO.MHWordDomain ICO.MHWordDomainTwirl
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1800000
variable {A : Type} [Fintype A] [DecidableEq A] [Nontrivial A]

def leftSlots (l r : ℕ) : Finset (Fin l ⊕ Fin r) := Finset.univ.map ⟨Sum.inl,Sum.inl_injective⟩

theorem slots_disjoint (l r : ℕ) : Disjoint (leftSlots l r) (rightSlots l r) := by
  apply Finset.disjoint_left.mpr
  intro j hj hq
  cases j <;> simp [leftSlots,rightSlots] at *

theorem slots_cover (l r : ℕ) : leftSlots l r ∪ rightSlots l r=Finset.univ := by
  ext j
  cases j <;> simp [leftSlots,rightSlots]

theorem fixed_sector_twirl_le (l r : ℕ) (κ : ℝ) (hκ : 1≤κ) :
    (∫ D, twirl (rightSlots l r) D
      (distinctProjection (A := A) (J := Fin l ⊕ Fin r)-domainModel (rightSlots l r) κ)
        ∂unitaryHaarMeasure (a := A)) ≤
      (κ*((2*(l : ℝ)+r)/((Fintype.card A : ℝ)+1) +
        2*(r : ℝ)*Real.sqrt (((l : ℝ)+r)/Fintype.card A))) •
          (1 : CMatrix (WordBasis A (Fin l ⊕ Fin r))) := by
  simpa [leftSlots,rightSlots,Fintype.card_sum] using
    domain_double_twirl_le (A := A) (leftSlots l r) (rightSlots l r)
      (slots_disjoint l r) (slots_cover l r) κ hκ

theorem two_div_succ_le_sqrt_inverse (d : ℝ) (hd : 0<d) :
    2/(d+1)≤Real.sqrt (1/d) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  have hp : 0<d+1 := by positivity
  apply (le_div_iff₀ hd).2
  rw [show (2/(d+1))^2*d=4*d/(d+1)^2 by rw [div_pow]; ring]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).2
  nlinarith [sq_nonneg (d-1)]

theorem sector_scalar_le (l r : ℕ) (d κ : ℝ) (hd : 0<d) (hκ0 : 0≤κ) (hκ2 : κ≤2) :
    κ*((2*(l : ℝ)+r)/(d+1)+2*(r : ℝ)*Real.sqrt (((l : ℝ)+r)/d)) ≤
      6*((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/d) := by
  by_cases ht : l+r=0
  · have hl : l=0 := by omega
    have hr : r=0 := by omega
    simp [hl,hr]
  · have ht1 : (1 : ℝ)≤(l : ℝ)+r := by exact_mod_cast (show 1≤l+r by omega)
    have hdiv : 2/(d+1)≤Real.sqrt (((l : ℝ)+r)/d) :=
      (two_div_succ_le_sqrt_inverse d hd).trans
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ht1 hd.le))
    have hfrac : (2*(l : ℝ)+r)/(d+1) ≤ ((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/d) := by
      calc
        _ ≤ (2*((l : ℝ)+r))/(d+1) := div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) r]) (by positivity)
        _ = ((l : ℝ)+r)*(2/(d+1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by positivity)
    have hs := Real.sqrt_nonneg (((l : ℝ)+r)/d)
    have hr : 2*(r : ℝ)*Real.sqrt (((l : ℝ)+r)/d) ≤
        2*((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/d) := mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) l]) hs
    have hb := mul_le_mul_of_nonneg_left (add_le_add hfrac hr) hκ0
    have hc := mul_le_mul_of_nonneg_right hκ2
      (show 0≤((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/d) +
        2*((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/d) by positivity)
    nlinarith

theorem fixed_sector_six_twirl_le (l r : ℕ) (κ : ℝ) (hκ1 : 1≤κ) (hκ2 : κ≤2) :
    (∫ D, twirl (rightSlots l r) D
      (distinctProjection (A := A) (J := Fin l ⊕ Fin r)-domainModel (rightSlots l r) κ)
        ∂unitaryHaarMeasure (a := A)) ≤
      (6*((l : ℝ)+r)*Real.sqrt (((l : ℝ)+r)/Fintype.card A)) •
          (1 : CMatrix (WordBasis A (Fin l ⊕ Fin r))) := by
  apply (fixed_sector_twirl_le l r κ hκ1).trans
  apply smul_le_smul_of_nonneg_right _ Matrix.PosSemidef.one.nonneg
  exact sector_scalar_le l r _ κ (by exact_mod_cast Fintype.card_pos)
    (le_trans (by norm_num) hκ1) hκ2

#print axioms fixed_sector_six_twirl_le
end
end ICO.MHWordSectorTwirl


