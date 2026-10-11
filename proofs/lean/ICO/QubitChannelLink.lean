import ICO.QubitChannelKraus
import ICO.TensorBitOrder

namespace ICO.QubitChannelLink
open ICO.QubitChannelKraus ICO.QubitLink ICO.TensorBitOrder ICO.PositiveSupport
open Matrix
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

def packEquiv : Fin 8 × Fin 4 × Fin 4 ≃ Fin 128 where
  toFun x := pack x.1 x.2.1 x.2.2
  invFun i := (external i,slotA i,slotB i)
  left_inv := by
    intro ⟨o,a,b⟩
    have h := unpack_pack o a b
    simp only [h.1,h.2.1,h.2.2]
  right_inv := pack_unpack

theorem sum_pack (f : Fin 128 → ℂ) :
    (∑ i : Fin 128, f i) = ∑ o : Fin 8, ∑ a : Fin 4, ∑ b : Fin 4, f (pack o a b) := by
  simpa only [Fintype.sum_prod_type, packEquiv] using (packEquiv.sum_comp f).symm

theorem link_pack (U V : Matrix (Fin 2) (Fin 2) ℂ)
    (o p : Fin 8) (a b : Fin 4) :
    linkMatrix U V o (pack p a b) =
      if o=p then choiVector U a * choiVector V b else 0 := by
  have hai : bit (pack p a b).val 32 = ((finProdFinEquiv (m := 2) (n := 2)).symm a).1 := by
    apply Fin.ext; fin_cases p <;> dsimp [bit, pack, finProdFinEquiv, Fin.divNat] <;> omega
  have hao : bit (pack p a b).val 16 = ((finProdFinEquiv (m := 2) (n := 2)).symm a).2 := by
    apply Fin.ext; dsimp [bit, pack, finProdFinEquiv, Fin.modNat]; omega
  have hbi : bit (pack p a b).val 8 = ((finProdFinEquiv (m := 2) (n := 2)).symm b).1 := by
    apply Fin.ext; dsimp [bit, pack, finProdFinEquiv, Fin.divNat]; omega
  have hbo : bit (pack p a b).val 4 = ((finProdFinEquiv (m := 2) (n := 2)).symm b).2 := by
    apply Fin.ext; dsimp [bit, pack, finProdFinEquiv, Fin.modNat]; omega
  have ho : outputIndex (pack p a b) = p := by
    apply Fin.ext
    fin_cases p <;> fin_cases a <;> fin_cases b <;>
      norm_num [outputIndex, ICO.UnitaryTestCertificates.outIndex, pack]
  simp [linkMatrix, hai, hao, hbi, hbo, ho, choiVector]

theorem linked_matrix_entry (C : Matrix (Fin 128) (Fin 128) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (o p : Fin 8) :
    (linkMatrix U V * C * (linkMatrix U V)ᴴ) o p =
      ∑ aj : Fin 4, ∑ bj : Fin 4, ∑ ai : Fin 4, ∑ bi : Fin 4,
        choiVector U ai * choiVector V bi * C (pack o ai bi) (pack p aj bj) *
          star (choiVector U aj * choiVector V bj) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  simp_rw [sum_pack, link_pack]
  simp [ite_mul, mul_ite, apply_ite, eq_comm]

theorem linked_matrix_contract (C : Matrix (Fin 128) (Fin 128) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) (o p : Fin 8) :
    (linkMatrix U V * C * (linkMatrix U V)ᴴ) o p =
      QubitTensorGauge.contract (slotTensor C o p) (rankOne (choiVector U)) (rankOne (choiVector V)) := by
  rw [linked_matrix_entry]
  simp only [QubitTensorGauge.contract, Fintype.sum_prod_type, slotTensor,
    rankOne, Matrix.vecMulVec_apply, Pi.star_apply]
  let perm : (Fin 4 × Fin 4 × Fin 4 × Fin 4) ≃ (Fin 4 × Fin 4 × Fin 4 × Fin 4) :=
    { toFun := fun x => (x.2.2.1,x.1,x.2.2.2,x.2.1)
      invFun := fun x => (x.2.1,x.2.2.2,x.1,x.2.2.1)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hs := perm.sum_comp (fun x => choiVector U x.1 * star (choiVector U x.2.1) *
    C (pack o x.1 x.2.2.1) (pack p x.2.1 x.2.2.2) *
      (choiVector V x.2.2.1 * star (choiVector V x.2.2.2)))
  simp only [Fintype.sum_prod_type, perm, Equiv.coe_fn_mk] at hs
  rw [← hs]
  repeat' apply Finset.sum_congr rfl <;> intro _ _
  simp [StarMul.star_mul]
  ring

theorem linked_kraus_contract {I J : Type*} [Fintype I] [Fintype J]
    (C : Matrix (Fin 128) (Fin 128) ℂ)
    (U : I → Matrix (Fin 2) (Fin 2) ℂ) (V : J → Matrix (Fin 2) (Fin 2) ℂ) (o p : Fin 8) :
    (∑ i, ∑ j, linkMatrix (U i) (V j) * C * (linkMatrix (U i) (V j))ᴴ) o p =
      QubitTensorGauge.contract (slotTensor C o p) (krausChoi U) (krausChoi V) := by
  simp only [Matrix.sum_apply, linked_matrix_contract]
  change _ = QubitTensorGauge.contraction (slotTensor C o p) (∑ i, rankOne (choiVector (U i)))
    (∑ j, rankOne (choiVector (V j)))
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

/-- Equality on all actual TP Kraus channels gives the certificate's CPTP
gauge rows; neither a projection equation nor a channel-span axiom is assumed. -/
theorem gaugeRows_of_kraus_tests (C : Matrix (Fin 128) (Fin 128) ℂ)
    (h : ∀ U V : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
      (∑ i, (U i)ᴴ * U i) = 1 → (∑ j, (V j)ᴴ * V j) = 1 →
      (∑ i, ∑ j, linkMatrix (U i) (V j) * C * (linkMatrix (U i) (V j))ᴴ) = 0)
    (k : Nat) (hk : k < 16384) :
    TensorRowOperators.gaugeRow k (periodicTensor C) = 0 := by
  apply gaugeRow_zero_of_channels _ _ k hk
  intro o p A B hA hB
  obtain ⟨U,hUA,hU⟩ := exists_kraus A hA
  obtain ⟨V,hVB,hV⟩ := exists_kraus B hB
  have ht : slotTensorNat (periodicTensor C) o p = slotTensor C o p := by
    ext a b
    simp [slotTensorNat, slotTensor, periodicTensor, modIndex_fin]
  rw [ht, ← hUA, ← hVB, ← linked_kraus_contract]
  exact congrFun (congrFun (h U V hU hV) o) p

def singleKraus (U : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => if i=0 then U else 0

theorem singleKraus_complete (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    (∑ i, (singleKraus U i)ᴴ * singleKraus U i) = 1 := by
  simp [singleKraus, apply_ite, ite_mul, mul_ite, hU]

theorem link_zero_first (V : Matrix (Fin 2) (Fin 2) ℂ) : linkMatrix 0 V = 0 := by
  ext o i; simp [linkMatrix]

theorem link_zero_second (U : Matrix (Fin 2) (Fin 2) ℂ) : linkMatrix U 0 = 0 := by
  ext o i; simp [linkMatrix]

theorem singleKraus_link (C : Matrix (Fin 128) (Fin 128) ℂ)
    (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ i : Fin 4, ∑ j : Fin 4,
      linkMatrix (singleKraus U i) (singleKraus V j) * C *
        (linkMatrix (singleKraus U i) (singleKraus V j))ᴴ) =
      linkMatrix U V * C * (linkMatrix U V)ᴴ := by
  have hi (i : Fin 4) : linkMatrix (if i=0 then U else 0) V =
      if i=0 then linkMatrix U V else 0 := by
    by_cases h : i=0 <;> simp [h, link_zero_first]
  simp [singleKraus, apply_ite, link_zero_first, link_zero_second, hi, ite_mul, mul_ite]

#print axioms linked_kraus_contract
#print axioms gaugeRows_of_kraus_tests
end
end ICO.QubitChannelLink
