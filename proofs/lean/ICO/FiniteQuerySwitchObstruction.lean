import ICO.AbsentOracle
import ICO.NormalFormQubitObstruction
import ICO.ReducedCircuit
import ICO.OracleLift
import ICO.SwitchMixture
import ICO.SwitchNonconstant
import ICO.QueryOracleMaps

open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise
open Matrix QIT ICO.LabelledQueryTree ICO.QubitChoiIndex
open ICO.AllChannelDilation ICO.ExactQubitObstruction ICO.DilutedSwitchTarget

namespace ICO.FiniteQuerySwitchObstruction
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
noncomputable section
variable {M : Type} [Fintype M] [DecidableEq M]
attribute [local irreducible] identityChoi queryChoi switchChoi

/-- Exact simulation of the fixed-plus-control switch, stated on actual
complete Kraus channels of arbitrary finite Kraus rank. -/
def RealizesSwitch {m n : Nat}
    (tree : Tree (Fin m ⊕ Fin n) (Fin 2 × M) (Fin 4) Finset.univ (Fin 2)) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J],
    ∀ (U : I → CMatrix (Fin 2)) (V : J → CMatrix (Fin 2))
      (hU : ∑ i,(U i)ᴴ * U i=1) (hV : ∑ j,(V j)ᴴ * V j=1),
      flatten (MatrixMap.choi (tree.map
        (Sum.elim (fun _ => oracleMap U) (fun _ => oracleMap V)))) = switchChoi U V

theorem correctness_on_mixtures {m n : Nat}
    (tree : Tree (Fin m ⊕ Fin n) (Fin 2 × M) (Fin 4) Finset.univ (Fin 2))
    (h : RealizesSwitch tree) (U V : Fin 4 → CMatrix (Fin 2))
    (hU : ∑ i,(U i)ᴴ * U i=1) (hV : ∑ j,(V j)ᴴ * V j=1)
    (t s : ℝ) (ht : t∈Set.Icc 0 1) (hs : s∈Set.Icc 0 1) :
    MatrixMap.choi (tree.map (Sum.elim
      (fun _ => LinearMap.id+t • ((oracleChannel U hU).map-LinearMap.id))
      (fun _ => LinearMap.id+s • ((oracleChannel V hV).map-LinearMap.id)))) =
      (unflatten identityChoi+s • (unflatten (queryChoi V)-unflatten identityChoi)) +
        t • ((unflatten (queryChoi U)+s • (unflatten (switchChoi U V)-unflatten (queryChoi U))) -
          (unflatten identityChoi+s • (unflatten (queryChoi V)-unflatten identityChoi))) := by
  have hh := h (Option (Fin 4)) (Option (Fin 4))
    (ICO.OracleLift.mixtureKraus t U) (ICO.OracleLift.mixtureKraus s V)
    (ICO.OracleLift.mixtureKraus_complete t ht U hU)
    (ICO.OracleLift.mixtureKraus_complete s hs V hV)
  change flatten (MatrixMap.choi (tree.map (Sum.elim
    (fun _ => oracleMap (ICO.OracleLift.mixtureKraus t U))
    (fun _ => oracleMap (ICO.OracleLift.mixtureKraus s V))))) = _ at hh
  simp_rw [ICO.OracleLift.mixture_oracleMap t ht U,ICO.OracleLift.mixture_oracleMap s hs V] at hh
  change _ = switchChoi (ICO.SwitchMixture.mixtureKraus t U) (ICO.SwitchMixture.mixtureKraus s V) at hh
  rw [ICO.SwitchMixture.switch_mixture t s ht hs U V] at hh
  apply flatten_injective
  simp only [flatten_add,flatten_sub,flatten_smul,flatten_unflatten]
  change flatten (MatrixMap.choi (tree.map (Sum.elim
    (fun _ => LinearMap.id+t • (oracleMap U-LinearMap.id))
    (fun _ => LinearMap.id+s • (oracleMap V-LinearMap.id))))) = _
  rw [hh]
  change ((1-t)*(1-s)) • identityChoi+(t*(1-s)) • queryChoi U+
    ((1-t)*s) • queryChoi V+(t*s) • switchChoi U V = _
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
  ring

#check correctness_on_mixtures

/-- No finite labelled adaptive circuit with positive finite budgets can
exactly implement the switch on arbitrary qubit channels. -/
theorem no_positive_budget {m n : Nat} (hm : 0<m) (hn : 0<n)
    (tree : Tree (Fin m ⊕ Fin n) (Fin 2 × M) (Fin 4) Finset.univ (Fin 2)) :
    ¬ RealizesSwitch tree := by
  intro h
  have hm0 : (0 : ℝ)<m := by exact_mod_cast hm
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have hm1 : (1 : ℝ)≤m := by exact_mod_cast hm
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast hn
  apply ICO.NormalFormQubitObstruction.no_twoQueryTree (1/(m : ℝ)) (1/(n : ℝ))
    (by positivity) ((div_le_iff₀ hm0).mpr (by simpa using hm1))
    (by positivity) ((div_le_iff₀ hn0).mpr (by simpa using hn1))
    (ICO.ReducedCircuit.reduce hm hn tree)
  intro U V hU hV
  have hr := ICO.ReducedCircuit.reduce_bilinear hm hn tree (oracleChannel U hU) (oracleChannel V hV)
    (unflatten identityChoi) (unflatten (queryChoi U)) (unflatten (queryChoi V))
    (unflatten (switchChoi U V)) (correctness_on_mixtures tree h U V hU hV)
  change flatten _ = _
  rw [hr]
  simp only [flatten_add,flatten_smul,flatten_unflatten]
  unfold dilutedSwitchOutput
  change ((1/(m : ℝ))*(1/(n : ℝ))) • switchChoi U V+
      ((1/(m : ℝ))*(1-1/(n : ℝ))) • queryChoi U+
      ((1-1/(m : ℝ))*(1/(n : ℝ))) • queryChoi V+
      ((1-1/(m : ℝ))*(1-1/(n : ℝ))) • identityChoi = _
  ext i j
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  ring

#check no_positive_budget

theorem no_zero_first {n : Nat}
    (tree : Tree (Fin 0 ⊕ Fin n) (Fin 2 × M) (Fin 4) Finset.univ (Fin 2)) :
    ¬ RealizesSwitch tree := by
  intro h
  let I := ICO.SwitchNonconstant.identityFamily
  let X := ICO.SwitchNonconstant.flipFamily
  have hI := ICO.SwitchNonconstant.identity_complete
  have hX := ICO.SwitchNonconstant.flip_complete
  have hi := h (Fin 1) (Fin 1) I I hI hI
  have hx := h (Fin 1) (Fin 1) X I hX hI
  have he := ICO.AbsentOracle.zero_first_map tree (oracleMap (M:=M) I)
    (oracleMap (M:=M) X) (oracleMap (M:=M) I)
  have hout := congrArg (fun F : MatrixMap (Fin 2) (Fin 4) => flatten (MatrixMap.choi F)) he
  exact ICO.SwitchNonconstant.switch_changes_first (hi.symm.trans (hout.trans hx))

theorem no_zero_second {m : Nat}
    (tree : Tree (Fin m ⊕ Fin 0) (Fin 2 × M) (Fin 4) Finset.univ (Fin 2)) :
    ¬ RealizesSwitch tree := by
  intro h
  let I := ICO.SwitchNonconstant.identityFamily
  let X := ICO.SwitchNonconstant.flipFamily
  have hI := ICO.SwitchNonconstant.identity_complete
  have hX := ICO.SwitchNonconstant.flip_complete
  have hi := h (Fin 1) (Fin 1) I I hI hI
  have hx := h (Fin 1) (Fin 1) I X hI hX
  have he := ICO.AbsentOracle.zero_second_map tree (oracleMap (M:=M) I)
    (oracleMap (M:=M) X) (oracleMap (M:=M) I)
  have hout := congrArg (fun F : MatrixMap (Fin 2) (Fin 4) => flatten (MatrixMap.choi F)) he
  exact ICO.SwitchNonconstant.switch_changes_second (hi.symm.trans (hout.trans hx))

/-- No exact switch realization exists at any finite labelled query budgets,
including circuits omitting one of the two oracle types entirely. -/
theorem no_finite_budget {m n : Nat}
    (tree : Tree (Fin m ⊕ Fin n) (Fin 2 × M) (Fin 4) Finset.univ (Fin 2)) :
    ¬ RealizesSwitch tree := by
  by_cases hm : m=0
  · subst m
    exact no_zero_first tree
  · by_cases hn : n=0
    · subst n
      exact no_zero_second tree
    · exact no_positive_budget (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) tree

#print axioms no_finite_budget
end
end ICO.FiniteQuerySwitchObstruction

