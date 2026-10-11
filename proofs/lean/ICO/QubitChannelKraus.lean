import ICO.QubitCPTPGauge
import ICO.PositiveDecomposition

namespace ICO.QubitChannelKraus
open ICO.QubitCPTPGauge ICO.PositiveSupport Matrix
open scoped BigOperators ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

def slotIndex (i o : Fin 2) : Fin 4 := finProdFinEquiv (i,o)
def choiVector (U : Matrix (Fin 2) (Fin 2) ℂ) (s : Fin 4) : ℂ :=
  U ((finProdFinEquiv (m := 2) (n := 2)).symm s).2
    ((finProdFinEquiv (m := 2) (n := 2)).symm s).1

def krausChoi {K : Type*} [Fintype K] (U : K → Matrix (Fin 2) (Fin 2) ℂ) : SlotMatrix :=
  ∑ k, rankOne (choiVector (U k))

theorem choiVector_slot (U : Matrix (Fin 2) (Fin 2) ℂ) (i o : Fin 2) :
    choiVector U (slotIndex i o) = U o i := by
  simp [choiVector, slotIndex]

theorem kraus_complete_of_trace {K : Type*} [Fintype K]
    (U : K → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ i j, traceOutput (krausChoi U) i j = if i=j then 1 else 0) :
    (∑ k, (U k)ᴴ * U k) = 1 := by
  ext i j
  have h := hU j i
  have he (i o : Fin 2) : (⟨2*i.val+o.val, by omega⟩ : Fin 4) = slotIndex i o := by
    apply Fin.ext; dsimp [slotIndex, finProdFinEquiv]; omega
  simp only [traceOutput, he, krausChoi, Matrix.sum_apply, rankOne,
    Matrix.vecMulVec_apply, Pi.star_apply, choiVector_slot] at h
  rw [Finset.sum_comm] at h
  simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, eq_comm, mul_comm] using h

def chosenColumns (J : SlotMatrix) (hJ : J.PosSemidef) : Fin 4 → Fin 4 → ℂ :=
  Classical.choose (exists_rankOne_decomposition J hJ)

def channelKraus (J : SlotMatrix) (hJ : J.PosSemidef) (k : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun o i => chosenColumns J hJ k (slotIndex i o)

theorem channelKraus_choi (J : SlotMatrix) (hJ : J.PosSemidef) :
    krausChoi (channelKraus J hJ) = J := by
  have he (k : Fin 4) : choiVector (channelKraus J hJ k) = chosenColumns J hJ k := by
    funext a
    obtain ⟨⟨i,o⟩,rfl⟩ := (finProdFinEquiv (m := 2) (n := 2)).surjective a
    simp [choiVector,channelKraus,slotIndex]
  simp only [krausChoi,he]
  exact (Classical.choose_spec (exists_rankOne_decomposition J hJ)).symm

theorem channelKraus_complete (J : SlotMatrix) (hJ : IsChannelChoi J) :
    (∑ k : Fin 4, (channelKraus J hJ.1 k)ᴴ * channelKraus J hJ.1 k) = 1 := by
  apply kraus_complete_of_trace
  rw [channelKraus_choi]
  exact hJ.2

/-- Every positive trace-preserving qubit Choi matrix has a finite actual
Kraus representation, with its completeness equation derived from TP. -/
theorem exists_kraus (J : SlotMatrix) (hJ : IsChannelChoi J) :
    ∃ U : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
      krausChoi U = J ∧ (∑ k, (U k)ᴴ * U k) = 1 :=
  ⟨channelKraus J hJ.1, channelKraus_choi J hJ.1, channelKraus_complete J hJ⟩

#print axioms exists_kraus
end
end ICO.QubitChannelKraus
