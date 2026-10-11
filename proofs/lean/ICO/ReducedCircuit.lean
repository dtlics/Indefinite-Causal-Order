import ICO.CircuitPolarization
import ICO.UniformQueryMixture

open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise
open Matrix QIT ICO.LabelledQueryTree ICO.CircuitPolarization ICO.UniformQueryMixture

namespace ICO.ReducedCircuit
set_option maxHeartbeats 400000
noncomputable section
variable {H O A : Type} [Fintype H] [Fintype O] [Fintype A]
  [DecidableEq H] [DecidableEq O] [DecidableEq A]

/-- Choose one labelled slot of each type uniformly by an actual preprocessing
instrument, then execute the identity-specialized adaptive circuit. -/
def reduce {m n : Nat} (hm : 0<m) (hn : 0<n)
    (tree : Tree (Fin m ⊕ Fin n) H O Finset.univ A) : ICO.TwoQueryTree.QueryTree H O A := by
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact uniformMixture (fun p : Fin m × Fin n => selected tree p.1 p.2)

theorem reduce_choi {m n : Nat} (hm : 0<m) (hn : 0<n)
    (tree : Tree (Fin m ⊕ Fin n) H O Finset.univ A) (U V : Channel H H) :
    MatrixMap.choi (((reduce hm hn tree).channel U V).map) =
      (1/((m : ℝ)*(n : ℝ))) • (∑ i : Fin m, ∑ j : Fin n,
        MatrixMap.choi (((selected tree i j).channel U V).map)) := by
  letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  unfold reduce
  rw [uniformMixture_choi]
  simp [Fintype.card_prod,Fintype.sum_prod_type]

/-- A physical finite-query reduction, producing one ordinary two-query
adaptive circuit that realizes the positive identity dilution of the target. -/
theorem reduce_bilinear {m n : Nat} (hm : 0<m) (hn : 0<n)
    (tree : Tree (Fin m ⊕ Fin n) H O Finset.univ A) (U V : Channel H H)
    (u00 u10 u01 u11 : CMatrix (A × O))
    (h : ∀ t s : ℝ, t ∈ Set.Icc 0 1 → s ∈ Set.Icc 0 1 →
      MatrixMap.choi (tree.map (Sum.elim
        (fun _ => LinearMap.id+t • (U.map-LinearMap.id))
        (fun _ => LinearMap.id+s • (V.map-LinearMap.id)))) =
        (u00+s • (u01-u00)) + t • ((u10+s • (u11-u10)) - (u00+s • (u01-u00)))) :
    MatrixMap.choi (((reduce hm hn tree).channel U V).map) =
      ((1/(m : ℝ))*(1/(n : ℝ))) • u11 +
      ((1/(m : ℝ))*(1-1/(n : ℝ))) • u10 +
      ((1-1/(m : ℝ))*(1/(n : ℝ))) • u01 +
      ((1-1/(m : ℝ))*(1-1/(n : ℝ))) • u00 := by
  rw [reduce_choi]
  exact average_selected hm hn tree U V u00 u10 u01 u11 h

#print axioms reduce_bilinear
end
end ICO.ReducedCircuit
