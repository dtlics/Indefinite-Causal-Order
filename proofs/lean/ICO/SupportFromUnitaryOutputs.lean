import ICO.QubitLink
import ICO.PositiveSupport

/-! Unit-qubit output equality implies the actual 25-dimensional tensor support.
The hypothesis is a concrete equality of linked positive matrices for every
unitary pair. No abstract support, rank, or certificate hypotheses remain. -/
namespace ICO.SupportFromUnitaryOutputs
open ICO.QubitLink ICO.QubitUnitaryTests ICO.UnitaryTestCertificates
open ICO.ExactSupportSpace ICO.ExactSupportIndependence ICO.PositiveSupport
open Matrix
open scoped BigOperators ComplexConjugate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

theorem each_kraus_supported {K : Type*} [Fintype K]
    (v : K → Fin 128 → ℂ)
    (houtput : ∀ U V : Matrix (Fin 2) (Fin 2) ℂ,
      Uᴴ * U = 1 → Vᴴ * V = 1 →
      ∃ weight : Fin 4 → ℂ,
        linkMatrix U V * (∑ k, rankOne (v k)) * (linkMatrix U V)ᴴ =
          ∑ b, rankOne (weight b • outputVector U V b))
    (k : K) : ∃ x : Fin 25 → ℂ, encode x = v k := by
  apply support_of_constraints
  intro r hr
  let rr : Fin 103 := ⟨r.val, hr⟩
  let U := normalizedMatrix (uData rr.val)
  let V := normalizedMatrix (vData rr.val)
  have hU : Uᴴ * U = 1 := normalized_unitary _ (all_norm_pos rr).1
  have hV : Vᴴ * V = 1 := normalized_unitary _ (all_norm_pos rr).2
  obtain ⟨weight, hout⟩ := houtput U V hU hV
  have hsum : (∑ j, rankOne (linkMatrix U V *ᵥ v j)) =
      ∑ b, rankOne (weight b • outputVector U V b) := by
    rw [← sum_rankOne_sandwich]
    exact hout
  let probe : Fin 8 → ℂ := star (annihilator rr)
  have hkill (b : Fin 4) : overlap probe (weight b • outputVector U V b) = 0 := by
    simp only [overlap, probe, star_star, dotProduct_smul]
    rw [annihilator_normalized_output, smul_zero]
  have hzero := each_overlap_zero_of_sum_eq
    (fun j => linkMatrix U V *ᵥ v j)
    (fun b => weight b • outputVector U V b) hsum probe hkill k
  simp only [overlap, probe, star_star] at hzero
  change annihilator rr ⬝ᵥ (linkMatrix (normalizedMatrix (uData rr.val))
    (normalizedMatrix (vData rr.val)) *ᵥ v k) = 0 at hzero
  rw [annihilator_normalized_link] at hzero
  have hnonzero := mul_ne_zero
    (normalization_ne_zero _ (all_norm_pos rr).1)
    (normalization_ne_zero _ (all_norm_pos rr).2)
  have hcoef := (mul_eq_zero.mp hzero).resolve_left hnonzero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hv := (mul_eq_zero.mp hcoef).resolve_left htwo
  simpa [headIndex, rr] using hv

#print axioms each_kraus_supported

end
end ICO.SupportFromUnitaryOutputs
