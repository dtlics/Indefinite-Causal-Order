import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone
import Mathlib.Tactic

/-! The first-order polarization identity needed for finite-query reduction.
Unlike full polarization, it only inserts one nonidentity argument. This is
enough to reduce finite repeated queries to a one-call diluted realization. -/
namespace ICO.OneSlotPolarization
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem diagonal_derivative {n : Nat}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (e a : E) :
    HasDerivAt (fun t : ℝ => f (fun _ => e+t • (a-e)))
      (∑ i : Fin n, f (Function.update (fun _ => e) i (a-e))) 0 := by
  have hc : HasDerivAt (fun t : ℝ => fun _ : Fin n => e+t • (a-e))
      (fun _ => a-e) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (a-e)).const_add e
  have hf := (f.hasFDerivAt (fun _ => e)).comp_hasDerivAt_of_eq 0 hc (by simp)
  simpa only [Function.comp_def, ContinuousMultilinearMap.linearDeriv_apply] using hf

/-- If repeated mixtures interpolate affinely between u and v, then summing
over the position of one distinguished input yields v+(n-1)u. Only equality
on the physical mixture segment 0≤t≤1 is assumed. -/
theorem sum_one_insert {n : Nat} (hn : 0 < n)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
    (e a : E) (u v : F)
    (h : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      f (fun _ => e+t • (a-e)) = u+t • (v-u)) :
    (∑ i : Fin n, f (Function.update (fun _ => e) i a)) = v+(n-1) • u := by
  have hu : f (fun _ => e) = u := by simpa using h 0 (by simp)
  have hd := (diagonal_derivative f e a).hasDerivWithinAt (s := Set.Icc 0 1)
  have ht : HasDerivWithinAt (fun t : ℝ => u+t • (v-u)) (v-u) (Set.Icc 0 1) 0 := by
    apply HasDerivAt.hasDerivWithinAt
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v-u)).const_add u
  have ht' := ht.congr_of_mem (fun t ht => h t ht) (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
  have hdiff := (hd.derivWithin (uniqueDiffOn_Icc_zero_one 0 (by simp))).symm.trans
    (ht'.derivWithin (uniqueDiffOn_Icc_zero_one 0 (by simp)))
  have hsub (i : Fin n) :
      f (Function.update (fun _ => e) i (a-e)) =
        f (Function.update (fun _ => e) i a) - f (fun _ => e) := by
    simpa only [Function.update_eq_self] using
      f.toMultilinearMap.map_update_sub (fun _ => e) i a e
  simp_rw [hsub, hu] at hdiff
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hdiff
  have hsum := eq_add_of_sub_eq hdiff
  rw [hsum]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [Nat.succ_sub_one, succ_nsmul]
  abel

end
end ICO.OneSlotPolarization
