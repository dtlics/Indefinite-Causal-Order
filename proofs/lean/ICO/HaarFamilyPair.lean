import ICO.HaarFamily
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Conditioning on one coordinate in each of two independent Haar families -/

open Matrix QIT MeasureTheory ICO.HaarFamily

namespace ICO.HaarFamilyPair
set_option maxHeartbeats 600000
noncomputable section
universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]

theorem continuous_integral_compact
    {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    [SecondCountableTopology Y] (μ : Measure Y) [IsFiniteMeasure μ]
    (f : X × Y → ℝ) (hf : Continuous f) :
    Continuous (fun x => ∫ y, f (x,y) ∂μ) := by
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := μ)
      (f := fun x y => f (x,y)) hf isCompact_univ)

theorem integral_coordinate_pair {r s : ℕ} (i : Fin (r + 1)) (j : Fin (s + 1))
    (f : (Fin (r + 1) → Unitary (A := A)) × (Fin (s + 1) → Unitary (A := A)) → ℝ)
    (hf : Continuous f) :
    (∫ UV, f UV ∂(familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))) =
      ∫ RU : Fin r → Unitary (A := A), ∫ RV : Fin s → Unitary (A := A),
        ∫ U : Unitary (A := A), ∫ V : Unitary (A := A),
          f (i.insertNth U RU, j.insertNth V RV)
          ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)
          ∂familyMeasure (A := A) s ∂familyMeasure (A := A) r := by
  have hint := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1)))
  rw [integral_prod _ hint]
  have hc := continuous_integral_compact (familyMeasure (A := A) (s + 1)) f hf
  rw [integral_insertNth i _ hc]
  apply integral_congr_ae
  filter_upwards [] with RU
  have hrow (U : Unitary (A := A)) :
      (∫ VF, f (i.insertNth U RU, VF) ∂familyMeasure (A := A) (s + 1)) =
        ∫ RV : Fin s → Unitary (A := A), ∫ V : Unitary (A := A),
          f (i.insertNth U RU, j.insertNth V RV) ∂unitaryHaarMeasure (a := A)
          ∂familyMeasure (A := A) s :=
    integral_insertNth j _ (hf.comp (continuous_const.prodMk continuous_id))
  simp_rw [hrow]
  have hinner : Continuous (fun p : (Unitary (A := A) × (Fin s → Unitary (A := A))) ×
      Unitary (A := A) => f (i.insertNth p.1.1 RU, j.insertNth p.2 p.1.2)) := by
    apply hf.comp
    apply Continuous.prodMk
    · exact Continuous.finInsertNth (A := fun _ => Unitary (A := A)) i
        (continuous_fst.comp continuous_fst) continuous_const
    · exact Continuous.finInsertNth (A := fun _ => Unitary (A := A)) j continuous_snd
        (continuous_snd.comp continuous_fst)
  have hcont := continuous_integral_compact (unitaryHaarMeasure (a := A)) _ hinner
  have hint2 := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (unitaryHaarMeasure (a := A)).prod (familyMeasure (A := A) s))
  exact integral_integral_swap hint2

theorem integral_coordinate_pair_le {r s : ℕ} (i : Fin (r + 1)) (j : Fin (s + 1))
    (f : (Fin (r + 1) → Unitary (A := A)) × (Fin (s + 1) → Unitary (A := A)) → ℝ)
    (hf : Continuous f) (h0 : ∀ UV, 0 ≤ f UV) (c : ℝ)
    (hc : ∀ (RU : Fin r → Unitary (A := A)) (RV : Fin s → Unitary (A := A)),
      (∫ U : Unitary (A := A), ∫ V : Unitary (A := A),
        f (i.insertNth U RU, j.insertNth V RV)
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)) ≤ c) :
    (∫ UV, f UV ∂(familyMeasure (A := A) (r + 1)).prod (familyMeasure (A := A) (s + 1))) ≤ c := by
  rw [integral_coordinate_pair i j f hf]
  have hn (RU : Fin r → Unitary (A := A)) (RV : Fin s → Unitary (A := A)) :
      0 ≤ ∫ U : Unitary (A := A), ∫ V : Unitary (A := A),
        f (i.insertNth U RU, j.insertNth V RV)
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A) :=
    integral_nonneg (fun U => integral_nonneg (fun V => h0 _))
  have hrow (RU : Fin r → Unitary (A := A)) :
      (∫ RV : Fin s → Unitary (A := A), ∫ U : Unitary (A := A), ∫ V : Unitary (A := A),
        f (i.insertNth U RU, j.insertNth V RV)
        ∂unitaryHaarMeasure (a := A) ∂unitaryHaarMeasure (a := A)
        ∂familyMeasure (A := A) s) ≤ c := by
    have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (hn RU))
      (integrable_const c (μ := familyMeasure (A := A) s)) (Filter.Eventually.of_forall (hc RU))
    simpa using h
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun RU => integral_nonneg (hn RU)))
    (integrable_const c (μ := familyMeasure (A := A) r)) (Filter.Eventually.of_forall hrow)
  simpa using h

end
end ICO.HaarFamilyPair
