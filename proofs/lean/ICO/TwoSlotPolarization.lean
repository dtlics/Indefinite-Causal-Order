import ICO.OneSlotPolarization

namespace ICO.TwoSlotPolarization
open ICO.OneSlotPolarization
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem elim_update_left {m n : Nat} [DecidableEq (Fin m)] [DecidableEq (Fin m ⊕ Fin n)] (a : Fin m → E) (b : Fin n → E) (i : Fin m) (x : E) :
    Sum.elim (Function.update a i x) b = Function.update (Sum.elim a b) (Sum.inl i) x := by
  funext j
  cases j <;> simp [Function.update_apply]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem elim_update_right {m n : Nat} [DecidableEq (Fin n)] [DecidableEq (Fin m ⊕ Fin n)] (a : Fin m → E) (b : Fin n → E) (j : Fin n) (x : E) :
    Sum.elim a (Function.update b j x) = Function.update (Sum.elim a b) (Sum.inr j) x := by
  funext i
  cases i <;> simp [Function.update_apply]

def fixB {m n : Nat}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m ⊕ Fin n => E) F) (b : Fin n → E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F where
  toFun a := f (Sum.elim a b)
  map_update_add' a i x y := by
    change f (Sum.elim (Function.update a i (x+y)) b) =
      f (Sum.elim (Function.update a i x) b) + f (Sum.elim (Function.update a i y) b)
    rw [elim_update_left a b i (x+y), elim_update_left a b i x, elim_update_left a b i y]
    exact f.map_update_add _ _ _ _
  map_update_smul' a i z x := by
    change f (Sum.elim (Function.update a i (z • x)) b) = z • f (Sum.elim (Function.update a i x) b)
    rw [elim_update_left a b i (z • x), elim_update_left a b i x]
    exact f.map_update_smul _ _ _ _
  cont := f.cont.comp (continuous_pi fun j => by
    cases j with
    | inl i => exact continuous_apply i
    | inr j => exact continuous_const)

def fixA {m n : Nat}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m ⊕ Fin n => E) F) (a : Fin m → E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F where
  toFun b := f (Sum.elim a b)
  map_update_add' b j x y := by
    change f (Sum.elim a (Function.update b j (x+y))) =
      f (Sum.elim a (Function.update b j x)) + f (Sum.elim a (Function.update b j y))
    rw [elim_update_right a b j (x+y), elim_update_right a b j x, elim_update_right a b j y]
    exact f.map_update_add _ _ _ _
  map_update_smul' b j z x := by
    change f (Sum.elim a (Function.update b j (z • x))) = z • f (Sum.elim a (Function.update b j x))
    rw [elim_update_right a b j (z • x), elim_update_right a b j x]
    exact f.map_update_smul _ _ _ _
  cont := f.cont.comp (continuous_pi fun i => by
    cases i with
    | inl i => exact continuous_const
    | inr j => exact continuous_apply j)

/-- First-order polarization in both slot types. The theorem holds for every
positive finite m,n; it is not a check at finitely many query budgets. -/
theorem sum_one_each {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m ⊕ Fin n => E) F)
    (e a b : E) (u00 u10 u01 u11 : F)
    (h : ∀ t s : ℝ, t ∈ Set.Icc 0 1 → s ∈ Set.Icc 0 1 →
      f (Sum.elim (fun _ => e+t • (a-e)) (fun _ => e+s • (b-e))) =
        (u00+s • (u01-u00)) + t • ((u10+s • (u11-u10)) - (u00+s • (u01-u00)))) :
    (∑ i : Fin m, ∑ j : Fin n,
      f (Sum.elim (Function.update (fun _ => e) i a) (Function.update (fun _ => e) j b))) =
        u11+(m-1) • u01+(n-1) • u10+((m-1)*(n-1)) • u00 := by
  let g : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F :=
    ∑ i : Fin m, fixA f (Function.update (fun _ => e) i a)
  have hg (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
      g (fun _ => e+s • (b-e)) =
        (u10+(m-1) • u00) + s • ((u11+(m-1) • u01) - (u10+(m-1) • u00)) := by
    have hh := sum_one_insert hm (fixB f (fun _ => e+s • (b-e))) e a
      (u00+s • (u01-u00)) (u10+s • (u11-u10)) (fun t ht => h t s ht hs)
    change (∑ i : Fin m, f (Sum.elim (Function.update (fun _ => e) i a)
      (fun _ => e+s • (b-e)))) = _ at hh
    simp only [g, ContinuousMultilinearMap.sum_apply]
    change (∑ i : Fin m, f (Sum.elim (Function.update (fun _ => e) i a)
      (fun _ => e+s • (b-e)))) = _
    rw [hh]
    module
  have hh := sum_one_insert hn g e b (u10+(m-1) • u00) (u11+(m-1) • u01) hg
  simp only [g, ContinuousMultilinearMap.sum_apply] at hh
  change (∑ j : Fin n, ∑ i : Fin m,
    f (Sum.elim (Function.update (fun _ => e) i a) (Function.update (fun _ => e) j b))) = _ at hh
  rw [Finset.sum_comm] at hh
  rw [hh]
  simp only [smul_add, smul_smul]
  rw [Nat.mul_comm (n-1) (m-1)]
  abel

theorem dilution_weights {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (u00 u10 u01 u11 : F) :
    (1/((m : ℝ)*(n : ℝ))) •
      (u11+(m-1) • u01+(n-1) • u10+((m-1)*(n-1)) • u00) =
      ((1/(m : ℝ))*(1/(n : ℝ))) • u11 +
      ((1/(m : ℝ))*(1-1/(n : ℝ))) • u10 +
      ((1-1/(m : ℝ))*(1/(n : ℝ))) • u01 +
      ((1-1/(m : ℝ))*(1-1/(n : ℝ))) • u00 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hm1 : ((m-1 : Nat) : ℝ) = (m : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hn1 : ((n-1 : Nat) : ℝ) = (n : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  match_scalars <;> (try simp only [Nat.cast_mul, hm1, hn1]) <;>
    field_simp [hm0, hn0] <;> ring

/-- Uniformly choosing one A slot and one B slot realizes precisely the
identity-diluted bilinear target, with positive parameters 1/m and 1/n. -/
theorem average_one_each {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m ⊕ Fin n => E) F)
    (e a b : E) (u00 u10 u01 u11 : F)
    (h : ∀ t s : ℝ, t ∈ Set.Icc 0 1 → s ∈ Set.Icc 0 1 →
      f (Sum.elim (fun _ => e+t • (a-e)) (fun _ => e+s • (b-e))) =
        (u00+s • (u01-u00)) + t • ((u10+s • (u11-u10)) - (u00+s • (u01-u00)))) :
    (1/((m : ℝ)*(n : ℝ))) • (∑ i : Fin m, ∑ j : Fin n,
      f (Sum.elim (Function.update (fun _ => e) i a) (Function.update (fun _ => e) j b))) =
      ((1/(m : ℝ))*(1/(n : ℝ))) • u11 +
      ((1/(m : ℝ))*(1-1/(n : ℝ))) • u10 +
      ((1-1/(m : ℝ))*(1/(n : ℝ))) • u01 +
      ((1-1/(m : ℝ))*(1-1/(n : ℝ))) • u00 := by
  rw [sum_one_each hm hn f e a b u00 u10 u01 u11 h]
  exact dilution_weights hm hn u00 u10 u01 u11

#print axioms average_one_each

end
end ICO.TwoSlotPolarization

