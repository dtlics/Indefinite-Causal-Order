import ICO.DilutedSwitchCoordinates
import ICO.SupportFromUnitaryOutputs
import ICO.QubitChannelLink
import ICO.PositiveDecomposition

/-! The finite qubit obstruction, with forced support and channel gauge
derived from actual linked output identities. This theorem does not assume
the unknown support coordinates, rank, or certificate identities. -/
namespace ICO.ExactQubitObstruction
open ICO.ExactSeparation ICO.ExactTensorCertificates ICO.ExactSupportIndependence
open ICO.SupportCoordinates ICO.DilutedSwitchTarget ICO.PositiveSupport
open ICO.SupportFromUnitaryOutputs ICO.QubitChannelLink ICO.QubitLink
open ICO.TensorRowOperators ICO.TensorBitOrder Matrix
open scoped BigOperators ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

theorem rowValue_add_sub (row : Nat → Coord → Int) (k : Nat) (x y z : Vector) :
    rowValue row k (x+y-z) = rowValue row k x + rowValue row k y - rowValue row k z := by
  simp [rowValue, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem no_positive_ordered_target {KA KB : Type*} [Fintype KA] [Fintype KB]
    (lambda mu : ℝ) (hl0 : 0 < lambda) (hl1 : lambda ≤ 1) (hm0 : 0 < mu) (hm1 : mu ≤ 1)
    (vA : KA → Fin 128 → ℂ) (vB : KB → Fin 128 → ℂ)
    (hAB : ∀ k < 1088, abRow k (periodicTensor (∑ a, rankOne (vA a))) = 0)
    (hBA : ∀ k < 1088, baRow k (periodicTensor (∑ b, rankOne (vB b))) = 0)
    (hOutput : ∀ U V : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
      (∑ i, (U i)ᴴ * U i) = 1 → (∑ j, (V j)ᴴ * V j) = 1 →
      (∑ i, ∑ j, linkMatrix (U i) (V j) *
        ((∑ a, rankOne (vA a)) + ∑ b, rankOne (vB b)) * (linkMatrix (U i) (V j))ᴴ) =
      ∑ i, ∑ j, linkMatrix (U i) (V j) * targetChoi lambda mu * (linkMatrix (U i) (V j))ᴴ) : False := by
  let C := (∑ a, rankOne (vA a)) + ∑ b, rankOne (vB b)
  let v : KA ⊕ KB → Fin 128 → ℂ := Sum.elim vA vB
  have hv : (∑ k, rankOne (v k)) = C := by simp [v,C,Fintype.sum_sum_type]
  have hUnit (U V : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
      linkMatrix U V * C * (linkMatrix U V)ᴴ =
        linkMatrix U V * targetChoi lambda mu * (linkMatrix U V)ᴴ := by
    have h := hOutput (singleKraus U) (singleKraus V) (singleKraus_complete U hU) (singleKraus_complete V hV)
    simpa only [singleKraus_link] using h
  have hs (k : KA ⊕ KB) : ∃ x : Fin 25 → ℂ, encode x = v k := by
    apply each_kraus_supported v _ k
    intro U V hU hV
    refine ⟨unitaryWeights lambda mu, ?_⟩
    rw [hv,hUnit U V hU hV]
    exact target_unitary_support lambda mu hl0.le hl1 hm0.le hm1 U V hU hV
  let xA : KA → Fin 25 → ℂ := fun k => Classical.choose (hs (Sum.inl k))
  let xB : KB → Fin 25 → ℂ := fun k => Classical.choose (hs (Sum.inr k))
  have hxA (k : KA) : encode (xA k) = vA k := Classical.choose_spec (hs (Sum.inl k))
  have hxB (k : KB) : encode (xB k) = vB k := Classical.choose_spec (hs (Sum.inr k))
  have hCA : supportedChoi xA = ∑ a, rankOne (vA a) := by simp [supportedChoi,hxA]
  have hCB : supportedChoi xB = ∑ b, rankOne (vB b) := by simp [supportedChoi,hxB]
  have hGauge (k : Nat) (hk : k < 16384) : gaugeRow k (periodicTensor (C-targetChoi lambda mu)) = 0 := by
    apply gaugeRows_of_kraus_tests _ _ k hk
    intro U V hU hV
    simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hOutput U V hU hV)
  apply no_supported_decomposition lambda mu hl0 hm0 (supportCoordinates xA) (supportCoordinates xB)
  · intro k hk
    rw [support_abRows,hCA,hAB k hk]
    rfl
  · intro k hk
    rw [support_baRows,hCB,hBA k hk]
    rfl
  · intro k hk
    rw [rowValue_add_sub,support_gaugeRows,support_gaugeRows,target_gaugeRows,hCA,hCB]
    have ht : periodicTensor (C-targetChoi lambda mu) =
        periodicTensor (∑ a, rankOne (vA a)) + periodicTensor (∑ b, rankOne (vB b)) -
          periodicTensor (targetChoi lambda mu) := rfl
    have h := congrArg Complex.re (hGauge k hk)
    rw [ht,map_sub,map_add,Complex.sub_re,Complex.add_re] at h
    exact h

#print axioms no_positive_ordered_target

theorem no_positive_matrix_target
    (lambda mu : ℝ) (hl0 : 0 < lambda) (hl1 : lambda ≤ 1) (hm0 : 0 < mu) (hm1 : mu ≤ 1)
    (CA CB : Matrix (Fin 128) (Fin 128) ℂ) (hCA : CA.PosSemidef) (hCB : CB.PosSemidef)
    (hAB : ∀ k < 1088, abRow k (periodicTensor CA) = 0)
    (hBA : ∀ k < 1088, baRow k (periodicTensor CB) = 0)
    (hOutput : ∀ U V : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
      (∑ i, (U i)ᴴ * U i) = 1 → (∑ j, (V j)ᴴ * V j) = 1 →
      (∑ i, ∑ j, linkMatrix (U i) (V j) * (CA+CB) * (linkMatrix (U i) (V j))ᴴ) =
      ∑ i, ∑ j, linkMatrix (U i) (V j) * targetChoi lambda mu * (linkMatrix (U i) (V j))ᴴ) : False := by
  obtain ⟨vA,rfl⟩ := exists_rankOne_decomposition CA hCA
  obtain ⟨vB,rfl⟩ := exists_rankOne_decomposition CB hCB
  exact no_positive_ordered_target lambda mu hl0 hl1 hm0 hm1 vA vB hAB hBA hOutput

def dilutedSwitchOutput {I J : Type*} [Fintype I] [Fintype J]
    (lambda mu : ℝ) (U : I → Matrix (Fin 2) (Fin 2) ℂ) (V : J → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  (((1-lambda)*(1-mu) : ℝ) : ℂ) • identityChoi +
    ((lambda*(1-mu) : ℝ) : ℂ) • queryChoi U +
    (((1-lambda)*mu : ℝ) : ℂ) • queryChoi V +
    ((lambda*mu : ℝ) : ℂ) • switchChoi U V

/-- No positive pair of ordered qubit combs implements the actual diluted
switch on all channels. The preprocessing branch need not have scalar mass,
and no environment dimension or Kraus rank is assumed. -/
theorem no_positive_ordered_switch
    (lambda mu : ℝ) (hl0 : 0 < lambda) (hl1 : lambda ≤ 1) (hm0 : 0 < mu) (hm1 : mu ≤ 1)
    (CA CB : Matrix (Fin 128) (Fin 128) ℂ) (hCA : CA.PosSemidef) (hCB : CB.PosSemidef)
    (hAB : ∀ k < 1088, abRow k (periodicTensor CA) = 0)
    (hBA : ∀ k < 1088, baRow k (periodicTensor CB) = 0)
    (hOutput : ∀ U V : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
      (∑ i, (U i)ᴴ * U i) = 1 → (∑ j, (V j)ᴴ * V j) = 1 →
      (∑ i, ∑ j, linkMatrix (U i) (V j) * (CA+CB) * (linkMatrix (U i) (V j))ᴴ) =
        dilutedSwitchOutput lambda mu U V) : False := by
  apply no_positive_matrix_target lambda mu hl0 hl1 hm0 hm1 CA CB hCA hCB hAB hBA
  intro U V hU hV
  rw [hOutput U V hU hV, linked_target_kraus lambda mu U V hU hV]
  rfl

#print axioms no_positive_ordered_switch
end
end ICO.ExactQubitObstruction
