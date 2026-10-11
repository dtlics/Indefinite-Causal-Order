import ICO.ExactTensorCertificates
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Real separation from the certified tensor rows

This is a finite-dimensional mathematical obstruction, not yet a formal theorem
about quantum circuits.  The hypotheses are the actual homogeneous causal and
CPTP-gauge coefficient rows in the support expansion.  The separate tasks of
forcing that support from positivity and of reducing arbitrary-query strategies
to this expansion are not hidden as axioms or claimed here.
-/

namespace ICO.ExactSeparation

open ICO.ExactTensorCertificates
open scoped BigOperators

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev Coord := Fin 325
abbrev Vector := Coord → ℝ

/-- All upper-triangle coordinates in lexicographic order. -/
def coordinates : List (Nat × Nat) :=
  (List.range 25).flatMap (fun a => (List.range (25 - a)).map (fun o => (a, a + o)))

structure CertifiedCoordinate where
  a : Nat
  b : Nat
  ab : abIdentity a b
  ba : baIdentity a b
  gauge : gaugeIdentity a b
  a_le_b : a ≤ b
  b_lt25 : b < 25

instance : Inhabited CertifiedCoordinate := ⟨⟨0, 0, ab_0_0, ba_0_0, gauge_0_0, by decide, by decide⟩⟩

def coordinateData : Array CertifiedCoordinate := #[
  ⟨0, 0, ab_0_0, ba_0_0, gauge_0_0, by decide, by decide⟩,
  ⟨0, 1, ab_0_1, ba_0_1, gauge_0_1, by decide, by decide⟩,
  ⟨0, 2, ab_0_2, ba_0_2, gauge_0_2, by decide, by decide⟩,
  ⟨0, 3, ab_0_3, ba_0_3, gauge_0_3, by decide, by decide⟩,
  ⟨0, 4, ab_0_4, ba_0_4, gauge_0_4, by decide, by decide⟩,
  ⟨0, 5, ab_0_5, ba_0_5, gauge_0_5, by decide, by decide⟩,
  ⟨0, 6, ab_0_6, ba_0_6, gauge_0_6, by decide, by decide⟩,
  ⟨0, 7, ab_0_7, ba_0_7, gauge_0_7, by decide, by decide⟩,
  ⟨0, 8, ab_0_8, ba_0_8, gauge_0_8, by decide, by decide⟩,
  ⟨0, 9, ab_0_9, ba_0_9, gauge_0_9, by decide, by decide⟩,
  ⟨0, 10, ab_0_10, ba_0_10, gauge_0_10, by decide, by decide⟩,
  ⟨0, 11, ab_0_11, ba_0_11, gauge_0_11, by decide, by decide⟩,
  ⟨0, 12, ab_0_12, ba_0_12, gauge_0_12, by decide, by decide⟩,
  ⟨0, 13, ab_0_13, ba_0_13, gauge_0_13, by decide, by decide⟩,
  ⟨0, 14, ab_0_14, ba_0_14, gauge_0_14, by decide, by decide⟩,
  ⟨0, 15, ab_0_15, ba_0_15, gauge_0_15, by decide, by decide⟩,
  ⟨0, 16, ab_0_16, ba_0_16, gauge_0_16, by decide, by decide⟩,
  ⟨0, 17, ab_0_17, ba_0_17, gauge_0_17, by decide, by decide⟩,
  ⟨0, 18, ab_0_18, ba_0_18, gauge_0_18, by decide, by decide⟩,
  ⟨0, 19, ab_0_19, ba_0_19, gauge_0_19, by decide, by decide⟩,
  ⟨0, 20, ab_0_20, ba_0_20, gauge_0_20, by decide, by decide⟩,
  ⟨0, 21, ab_0_21, ba_0_21, gauge_0_21, by decide, by decide⟩,
  ⟨0, 22, ab_0_22, ba_0_22, gauge_0_22, by decide, by decide⟩,
  ⟨0, 23, ab_0_23, ba_0_23, gauge_0_23, by decide, by decide⟩,
  ⟨0, 24, ab_0_24, ba_0_24, gauge_0_24, by decide, by decide⟩,
  ⟨1, 1, ab_1_1, ba_1_1, gauge_1_1, by decide, by decide⟩,
  ⟨1, 2, ab_1_2, ba_1_2, gauge_1_2, by decide, by decide⟩,
  ⟨1, 3, ab_1_3, ba_1_3, gauge_1_3, by decide, by decide⟩,
  ⟨1, 4, ab_1_4, ba_1_4, gauge_1_4, by decide, by decide⟩,
  ⟨1, 5, ab_1_5, ba_1_5, gauge_1_5, by decide, by decide⟩,
  ⟨1, 6, ab_1_6, ba_1_6, gauge_1_6, by decide, by decide⟩,
  ⟨1, 7, ab_1_7, ba_1_7, gauge_1_7, by decide, by decide⟩,
  ⟨1, 8, ab_1_8, ba_1_8, gauge_1_8, by decide, by decide⟩,
  ⟨1, 9, ab_1_9, ba_1_9, gauge_1_9, by decide, by decide⟩,
  ⟨1, 10, ab_1_10, ba_1_10, gauge_1_10, by decide, by decide⟩,
  ⟨1, 11, ab_1_11, ba_1_11, gauge_1_11, by decide, by decide⟩,
  ⟨1, 12, ab_1_12, ba_1_12, gauge_1_12, by decide, by decide⟩,
  ⟨1, 13, ab_1_13, ba_1_13, gauge_1_13, by decide, by decide⟩,
  ⟨1, 14, ab_1_14, ba_1_14, gauge_1_14, by decide, by decide⟩,
  ⟨1, 15, ab_1_15, ba_1_15, gauge_1_15, by decide, by decide⟩,
  ⟨1, 16, ab_1_16, ba_1_16, gauge_1_16, by decide, by decide⟩,
  ⟨1, 17, ab_1_17, ba_1_17, gauge_1_17, by decide, by decide⟩,
  ⟨1, 18, ab_1_18, ba_1_18, gauge_1_18, by decide, by decide⟩,
  ⟨1, 19, ab_1_19, ba_1_19, gauge_1_19, by decide, by decide⟩,
  ⟨1, 20, ab_1_20, ba_1_20, gauge_1_20, by decide, by decide⟩,
  ⟨1, 21, ab_1_21, ba_1_21, gauge_1_21, by decide, by decide⟩,
  ⟨1, 22, ab_1_22, ba_1_22, gauge_1_22, by decide, by decide⟩,
  ⟨1, 23, ab_1_23, ba_1_23, gauge_1_23, by decide, by decide⟩,
  ⟨1, 24, ab_1_24, ba_1_24, gauge_1_24, by decide, by decide⟩,
  ⟨2, 2, ab_2_2, ba_2_2, gauge_2_2, by decide, by decide⟩,
  ⟨2, 3, ab_2_3, ba_2_3, gauge_2_3, by decide, by decide⟩,
  ⟨2, 4, ab_2_4, ba_2_4, gauge_2_4, by decide, by decide⟩,
  ⟨2, 5, ab_2_5, ba_2_5, gauge_2_5, by decide, by decide⟩,
  ⟨2, 6, ab_2_6, ba_2_6, gauge_2_6, by decide, by decide⟩,
  ⟨2, 7, ab_2_7, ba_2_7, gauge_2_7, by decide, by decide⟩,
  ⟨2, 8, ab_2_8, ba_2_8, gauge_2_8, by decide, by decide⟩,
  ⟨2, 9, ab_2_9, ba_2_9, gauge_2_9, by decide, by decide⟩,
  ⟨2, 10, ab_2_10, ba_2_10, gauge_2_10, by decide, by decide⟩,
  ⟨2, 11, ab_2_11, ba_2_11, gauge_2_11, by decide, by decide⟩,
  ⟨2, 12, ab_2_12, ba_2_12, gauge_2_12, by decide, by decide⟩,
  ⟨2, 13, ab_2_13, ba_2_13, gauge_2_13, by decide, by decide⟩,
  ⟨2, 14, ab_2_14, ba_2_14, gauge_2_14, by decide, by decide⟩,
  ⟨2, 15, ab_2_15, ba_2_15, gauge_2_15, by decide, by decide⟩,
  ⟨2, 16, ab_2_16, ba_2_16, gauge_2_16, by decide, by decide⟩,
  ⟨2, 17, ab_2_17, ba_2_17, gauge_2_17, by decide, by decide⟩,
  ⟨2, 18, ab_2_18, ba_2_18, gauge_2_18, by decide, by decide⟩,
  ⟨2, 19, ab_2_19, ba_2_19, gauge_2_19, by decide, by decide⟩,
  ⟨2, 20, ab_2_20, ba_2_20, gauge_2_20, by decide, by decide⟩,
  ⟨2, 21, ab_2_21, ba_2_21, gauge_2_21, by decide, by decide⟩,
  ⟨2, 22, ab_2_22, ba_2_22, gauge_2_22, by decide, by decide⟩,
  ⟨2, 23, ab_2_23, ba_2_23, gauge_2_23, by decide, by decide⟩,
  ⟨2, 24, ab_2_24, ba_2_24, gauge_2_24, by decide, by decide⟩,
  ⟨3, 3, ab_3_3, ba_3_3, gauge_3_3, by decide, by decide⟩,
  ⟨3, 4, ab_3_4, ba_3_4, gauge_3_4, by decide, by decide⟩,
  ⟨3, 5, ab_3_5, ba_3_5, gauge_3_5, by decide, by decide⟩,
  ⟨3, 6, ab_3_6, ba_3_6, gauge_3_6, by decide, by decide⟩,
  ⟨3, 7, ab_3_7, ba_3_7, gauge_3_7, by decide, by decide⟩,
  ⟨3, 8, ab_3_8, ba_3_8, gauge_3_8, by decide, by decide⟩,
  ⟨3, 9, ab_3_9, ba_3_9, gauge_3_9, by decide, by decide⟩,
  ⟨3, 10, ab_3_10, ba_3_10, gauge_3_10, by decide, by decide⟩,
  ⟨3, 11, ab_3_11, ba_3_11, gauge_3_11, by decide, by decide⟩,
  ⟨3, 12, ab_3_12, ba_3_12, gauge_3_12, by decide, by decide⟩,
  ⟨3, 13, ab_3_13, ba_3_13, gauge_3_13, by decide, by decide⟩,
  ⟨3, 14, ab_3_14, ba_3_14, gauge_3_14, by decide, by decide⟩,
  ⟨3, 15, ab_3_15, ba_3_15, gauge_3_15, by decide, by decide⟩,
  ⟨3, 16, ab_3_16, ba_3_16, gauge_3_16, by decide, by decide⟩,
  ⟨3, 17, ab_3_17, ba_3_17, gauge_3_17, by decide, by decide⟩,
  ⟨3, 18, ab_3_18, ba_3_18, gauge_3_18, by decide, by decide⟩,
  ⟨3, 19, ab_3_19, ba_3_19, gauge_3_19, by decide, by decide⟩,
  ⟨3, 20, ab_3_20, ba_3_20, gauge_3_20, by decide, by decide⟩,
  ⟨3, 21, ab_3_21, ba_3_21, gauge_3_21, by decide, by decide⟩,
  ⟨3, 22, ab_3_22, ba_3_22, gauge_3_22, by decide, by decide⟩,
  ⟨3, 23, ab_3_23, ba_3_23, gauge_3_23, by decide, by decide⟩,
  ⟨3, 24, ab_3_24, ba_3_24, gauge_3_24, by decide, by decide⟩,
  ⟨4, 4, ab_4_4, ba_4_4, gauge_4_4, by decide, by decide⟩,
  ⟨4, 5, ab_4_5, ba_4_5, gauge_4_5, by decide, by decide⟩,
  ⟨4, 6, ab_4_6, ba_4_6, gauge_4_6, by decide, by decide⟩,
  ⟨4, 7, ab_4_7, ba_4_7, gauge_4_7, by decide, by decide⟩,
  ⟨4, 8, ab_4_8, ba_4_8, gauge_4_8, by decide, by decide⟩,
  ⟨4, 9, ab_4_9, ba_4_9, gauge_4_9, by decide, by decide⟩,
  ⟨4, 10, ab_4_10, ba_4_10, gauge_4_10, by decide, by decide⟩,
  ⟨4, 11, ab_4_11, ba_4_11, gauge_4_11, by decide, by decide⟩,
  ⟨4, 12, ab_4_12, ba_4_12, gauge_4_12, by decide, by decide⟩,
  ⟨4, 13, ab_4_13, ba_4_13, gauge_4_13, by decide, by decide⟩,
  ⟨4, 14, ab_4_14, ba_4_14, gauge_4_14, by decide, by decide⟩,
  ⟨4, 15, ab_4_15, ba_4_15, gauge_4_15, by decide, by decide⟩,
  ⟨4, 16, ab_4_16, ba_4_16, gauge_4_16, by decide, by decide⟩,
  ⟨4, 17, ab_4_17, ba_4_17, gauge_4_17, by decide, by decide⟩,
  ⟨4, 18, ab_4_18, ba_4_18, gauge_4_18, by decide, by decide⟩,
  ⟨4, 19, ab_4_19, ba_4_19, gauge_4_19, by decide, by decide⟩,
  ⟨4, 20, ab_4_20, ba_4_20, gauge_4_20, by decide, by decide⟩,
  ⟨4, 21, ab_4_21, ba_4_21, gauge_4_21, by decide, by decide⟩,
  ⟨4, 22, ab_4_22, ba_4_22, gauge_4_22, by decide, by decide⟩,
  ⟨4, 23, ab_4_23, ba_4_23, gauge_4_23, by decide, by decide⟩,
  ⟨4, 24, ab_4_24, ba_4_24, gauge_4_24, by decide, by decide⟩,
  ⟨5, 5, ab_5_5, ba_5_5, gauge_5_5, by decide, by decide⟩,
  ⟨5, 6, ab_5_6, ba_5_6, gauge_5_6, by decide, by decide⟩,
  ⟨5, 7, ab_5_7, ba_5_7, gauge_5_7, by decide, by decide⟩,
  ⟨5, 8, ab_5_8, ba_5_8, gauge_5_8, by decide, by decide⟩,
  ⟨5, 9, ab_5_9, ba_5_9, gauge_5_9, by decide, by decide⟩,
  ⟨5, 10, ab_5_10, ba_5_10, gauge_5_10, by decide, by decide⟩,
  ⟨5, 11, ab_5_11, ba_5_11, gauge_5_11, by decide, by decide⟩,
  ⟨5, 12, ab_5_12, ba_5_12, gauge_5_12, by decide, by decide⟩,
  ⟨5, 13, ab_5_13, ba_5_13, gauge_5_13, by decide, by decide⟩,
  ⟨5, 14, ab_5_14, ba_5_14, gauge_5_14, by decide, by decide⟩,
  ⟨5, 15, ab_5_15, ba_5_15, gauge_5_15, by decide, by decide⟩,
  ⟨5, 16, ab_5_16, ba_5_16, gauge_5_16, by decide, by decide⟩,
  ⟨5, 17, ab_5_17, ba_5_17, gauge_5_17, by decide, by decide⟩,
  ⟨5, 18, ab_5_18, ba_5_18, gauge_5_18, by decide, by decide⟩,
  ⟨5, 19, ab_5_19, ba_5_19, gauge_5_19, by decide, by decide⟩,
  ⟨5, 20, ab_5_20, ba_5_20, gauge_5_20, by decide, by decide⟩,
  ⟨5, 21, ab_5_21, ba_5_21, gauge_5_21, by decide, by decide⟩,
  ⟨5, 22, ab_5_22, ba_5_22, gauge_5_22, by decide, by decide⟩,
  ⟨5, 23, ab_5_23, ba_5_23, gauge_5_23, by decide, by decide⟩,
  ⟨5, 24, ab_5_24, ba_5_24, gauge_5_24, by decide, by decide⟩,
  ⟨6, 6, ab_6_6, ba_6_6, gauge_6_6, by decide, by decide⟩,
  ⟨6, 7, ab_6_7, ba_6_7, gauge_6_7, by decide, by decide⟩,
  ⟨6, 8, ab_6_8, ba_6_8, gauge_6_8, by decide, by decide⟩,
  ⟨6, 9, ab_6_9, ba_6_9, gauge_6_9, by decide, by decide⟩,
  ⟨6, 10, ab_6_10, ba_6_10, gauge_6_10, by decide, by decide⟩,
  ⟨6, 11, ab_6_11, ba_6_11, gauge_6_11, by decide, by decide⟩,
  ⟨6, 12, ab_6_12, ba_6_12, gauge_6_12, by decide, by decide⟩,
  ⟨6, 13, ab_6_13, ba_6_13, gauge_6_13, by decide, by decide⟩,
  ⟨6, 14, ab_6_14, ba_6_14, gauge_6_14, by decide, by decide⟩,
  ⟨6, 15, ab_6_15, ba_6_15, gauge_6_15, by decide, by decide⟩,
  ⟨6, 16, ab_6_16, ba_6_16, gauge_6_16, by decide, by decide⟩,
  ⟨6, 17, ab_6_17, ba_6_17, gauge_6_17, by decide, by decide⟩,
  ⟨6, 18, ab_6_18, ba_6_18, gauge_6_18, by decide, by decide⟩,
  ⟨6, 19, ab_6_19, ba_6_19, gauge_6_19, by decide, by decide⟩,
  ⟨6, 20, ab_6_20, ba_6_20, gauge_6_20, by decide, by decide⟩,
  ⟨6, 21, ab_6_21, ba_6_21, gauge_6_21, by decide, by decide⟩,
  ⟨6, 22, ab_6_22, ba_6_22, gauge_6_22, by decide, by decide⟩,
  ⟨6, 23, ab_6_23, ba_6_23, gauge_6_23, by decide, by decide⟩,
  ⟨6, 24, ab_6_24, ba_6_24, gauge_6_24, by decide, by decide⟩,
  ⟨7, 7, ab_7_7, ba_7_7, gauge_7_7, by decide, by decide⟩,
  ⟨7, 8, ab_7_8, ba_7_8, gauge_7_8, by decide, by decide⟩,
  ⟨7, 9, ab_7_9, ba_7_9, gauge_7_9, by decide, by decide⟩,
  ⟨7, 10, ab_7_10, ba_7_10, gauge_7_10, by decide, by decide⟩,
  ⟨7, 11, ab_7_11, ba_7_11, gauge_7_11, by decide, by decide⟩,
  ⟨7, 12, ab_7_12, ba_7_12, gauge_7_12, by decide, by decide⟩,
  ⟨7, 13, ab_7_13, ba_7_13, gauge_7_13, by decide, by decide⟩,
  ⟨7, 14, ab_7_14, ba_7_14, gauge_7_14, by decide, by decide⟩,
  ⟨7, 15, ab_7_15, ba_7_15, gauge_7_15, by decide, by decide⟩,
  ⟨7, 16, ab_7_16, ba_7_16, gauge_7_16, by decide, by decide⟩,
  ⟨7, 17, ab_7_17, ba_7_17, gauge_7_17, by decide, by decide⟩,
  ⟨7, 18, ab_7_18, ba_7_18, gauge_7_18, by decide, by decide⟩,
  ⟨7, 19, ab_7_19, ba_7_19, gauge_7_19, by decide, by decide⟩,
  ⟨7, 20, ab_7_20, ba_7_20, gauge_7_20, by decide, by decide⟩,
  ⟨7, 21, ab_7_21, ba_7_21, gauge_7_21, by decide, by decide⟩,
  ⟨7, 22, ab_7_22, ba_7_22, gauge_7_22, by decide, by decide⟩,
  ⟨7, 23, ab_7_23, ba_7_23, gauge_7_23, by decide, by decide⟩,
  ⟨7, 24, ab_7_24, ba_7_24, gauge_7_24, by decide, by decide⟩,
  ⟨8, 8, ab_8_8, ba_8_8, gauge_8_8, by decide, by decide⟩,
  ⟨8, 9, ab_8_9, ba_8_9, gauge_8_9, by decide, by decide⟩,
  ⟨8, 10, ab_8_10, ba_8_10, gauge_8_10, by decide, by decide⟩,
  ⟨8, 11, ab_8_11, ba_8_11, gauge_8_11, by decide, by decide⟩,
  ⟨8, 12, ab_8_12, ba_8_12, gauge_8_12, by decide, by decide⟩,
  ⟨8, 13, ab_8_13, ba_8_13, gauge_8_13, by decide, by decide⟩,
  ⟨8, 14, ab_8_14, ba_8_14, gauge_8_14, by decide, by decide⟩,
  ⟨8, 15, ab_8_15, ba_8_15, gauge_8_15, by decide, by decide⟩,
  ⟨8, 16, ab_8_16, ba_8_16, gauge_8_16, by decide, by decide⟩,
  ⟨8, 17, ab_8_17, ba_8_17, gauge_8_17, by decide, by decide⟩,
  ⟨8, 18, ab_8_18, ba_8_18, gauge_8_18, by decide, by decide⟩,
  ⟨8, 19, ab_8_19, ba_8_19, gauge_8_19, by decide, by decide⟩,
  ⟨8, 20, ab_8_20, ba_8_20, gauge_8_20, by decide, by decide⟩,
  ⟨8, 21, ab_8_21, ba_8_21, gauge_8_21, by decide, by decide⟩,
  ⟨8, 22, ab_8_22, ba_8_22, gauge_8_22, by decide, by decide⟩,
  ⟨8, 23, ab_8_23, ba_8_23, gauge_8_23, by decide, by decide⟩,
  ⟨8, 24, ab_8_24, ba_8_24, gauge_8_24, by decide, by decide⟩,
  ⟨9, 9, ab_9_9, ba_9_9, gauge_9_9, by decide, by decide⟩,
  ⟨9, 10, ab_9_10, ba_9_10, gauge_9_10, by decide, by decide⟩,
  ⟨9, 11, ab_9_11, ba_9_11, gauge_9_11, by decide, by decide⟩,
  ⟨9, 12, ab_9_12, ba_9_12, gauge_9_12, by decide, by decide⟩,
  ⟨9, 13, ab_9_13, ba_9_13, gauge_9_13, by decide, by decide⟩,
  ⟨9, 14, ab_9_14, ba_9_14, gauge_9_14, by decide, by decide⟩,
  ⟨9, 15, ab_9_15, ba_9_15, gauge_9_15, by decide, by decide⟩,
  ⟨9, 16, ab_9_16, ba_9_16, gauge_9_16, by decide, by decide⟩,
  ⟨9, 17, ab_9_17, ba_9_17, gauge_9_17, by decide, by decide⟩,
  ⟨9, 18, ab_9_18, ba_9_18, gauge_9_18, by decide, by decide⟩,
  ⟨9, 19, ab_9_19, ba_9_19, gauge_9_19, by decide, by decide⟩,
  ⟨9, 20, ab_9_20, ba_9_20, gauge_9_20, by decide, by decide⟩,
  ⟨9, 21, ab_9_21, ba_9_21, gauge_9_21, by decide, by decide⟩,
  ⟨9, 22, ab_9_22, ba_9_22, gauge_9_22, by decide, by decide⟩,
  ⟨9, 23, ab_9_23, ba_9_23, gauge_9_23, by decide, by decide⟩,
  ⟨9, 24, ab_9_24, ba_9_24, gauge_9_24, by decide, by decide⟩,
  ⟨10, 10, ab_10_10, ba_10_10, gauge_10_10, by decide, by decide⟩,
  ⟨10, 11, ab_10_11, ba_10_11, gauge_10_11, by decide, by decide⟩,
  ⟨10, 12, ab_10_12, ba_10_12, gauge_10_12, by decide, by decide⟩,
  ⟨10, 13, ab_10_13, ba_10_13, gauge_10_13, by decide, by decide⟩,
  ⟨10, 14, ab_10_14, ba_10_14, gauge_10_14, by decide, by decide⟩,
  ⟨10, 15, ab_10_15, ba_10_15, gauge_10_15, by decide, by decide⟩,
  ⟨10, 16, ab_10_16, ba_10_16, gauge_10_16, by decide, by decide⟩,
  ⟨10, 17, ab_10_17, ba_10_17, gauge_10_17, by decide, by decide⟩,
  ⟨10, 18, ab_10_18, ba_10_18, gauge_10_18, by decide, by decide⟩,
  ⟨10, 19, ab_10_19, ba_10_19, gauge_10_19, by decide, by decide⟩,
  ⟨10, 20, ab_10_20, ba_10_20, gauge_10_20, by decide, by decide⟩,
  ⟨10, 21, ab_10_21, ba_10_21, gauge_10_21, by decide, by decide⟩,
  ⟨10, 22, ab_10_22, ba_10_22, gauge_10_22, by decide, by decide⟩,
  ⟨10, 23, ab_10_23, ba_10_23, gauge_10_23, by decide, by decide⟩,
  ⟨10, 24, ab_10_24, ba_10_24, gauge_10_24, by decide, by decide⟩,
  ⟨11, 11, ab_11_11, ba_11_11, gauge_11_11, by decide, by decide⟩,
  ⟨11, 12, ab_11_12, ba_11_12, gauge_11_12, by decide, by decide⟩,
  ⟨11, 13, ab_11_13, ba_11_13, gauge_11_13, by decide, by decide⟩,
  ⟨11, 14, ab_11_14, ba_11_14, gauge_11_14, by decide, by decide⟩,
  ⟨11, 15, ab_11_15, ba_11_15, gauge_11_15, by decide, by decide⟩,
  ⟨11, 16, ab_11_16, ba_11_16, gauge_11_16, by decide, by decide⟩,
  ⟨11, 17, ab_11_17, ba_11_17, gauge_11_17, by decide, by decide⟩,
  ⟨11, 18, ab_11_18, ba_11_18, gauge_11_18, by decide, by decide⟩,
  ⟨11, 19, ab_11_19, ba_11_19, gauge_11_19, by decide, by decide⟩,
  ⟨11, 20, ab_11_20, ba_11_20, gauge_11_20, by decide, by decide⟩,
  ⟨11, 21, ab_11_21, ba_11_21, gauge_11_21, by decide, by decide⟩,
  ⟨11, 22, ab_11_22, ba_11_22, gauge_11_22, by decide, by decide⟩,
  ⟨11, 23, ab_11_23, ba_11_23, gauge_11_23, by decide, by decide⟩,
  ⟨11, 24, ab_11_24, ba_11_24, gauge_11_24, by decide, by decide⟩,
  ⟨12, 12, ab_12_12, ba_12_12, gauge_12_12, by decide, by decide⟩,
  ⟨12, 13, ab_12_13, ba_12_13, gauge_12_13, by decide, by decide⟩,
  ⟨12, 14, ab_12_14, ba_12_14, gauge_12_14, by decide, by decide⟩,
  ⟨12, 15, ab_12_15, ba_12_15, gauge_12_15, by decide, by decide⟩,
  ⟨12, 16, ab_12_16, ba_12_16, gauge_12_16, by decide, by decide⟩,
  ⟨12, 17, ab_12_17, ba_12_17, gauge_12_17, by decide, by decide⟩,
  ⟨12, 18, ab_12_18, ba_12_18, gauge_12_18, by decide, by decide⟩,
  ⟨12, 19, ab_12_19, ba_12_19, gauge_12_19, by decide, by decide⟩,
  ⟨12, 20, ab_12_20, ba_12_20, gauge_12_20, by decide, by decide⟩,
  ⟨12, 21, ab_12_21, ba_12_21, gauge_12_21, by decide, by decide⟩,
  ⟨12, 22, ab_12_22, ba_12_22, gauge_12_22, by decide, by decide⟩,
  ⟨12, 23, ab_12_23, ba_12_23, gauge_12_23, by decide, by decide⟩,
  ⟨12, 24, ab_12_24, ba_12_24, gauge_12_24, by decide, by decide⟩,
  ⟨13, 13, ab_13_13, ba_13_13, gauge_13_13, by decide, by decide⟩,
  ⟨13, 14, ab_13_14, ba_13_14, gauge_13_14, by decide, by decide⟩,
  ⟨13, 15, ab_13_15, ba_13_15, gauge_13_15, by decide, by decide⟩,
  ⟨13, 16, ab_13_16, ba_13_16, gauge_13_16, by decide, by decide⟩,
  ⟨13, 17, ab_13_17, ba_13_17, gauge_13_17, by decide, by decide⟩,
  ⟨13, 18, ab_13_18, ba_13_18, gauge_13_18, by decide, by decide⟩,
  ⟨13, 19, ab_13_19, ba_13_19, gauge_13_19, by decide, by decide⟩,
  ⟨13, 20, ab_13_20, ba_13_20, gauge_13_20, by decide, by decide⟩,
  ⟨13, 21, ab_13_21, ba_13_21, gauge_13_21, by decide, by decide⟩,
  ⟨13, 22, ab_13_22, ba_13_22, gauge_13_22, by decide, by decide⟩,
  ⟨13, 23, ab_13_23, ba_13_23, gauge_13_23, by decide, by decide⟩,
  ⟨13, 24, ab_13_24, ba_13_24, gauge_13_24, by decide, by decide⟩,
  ⟨14, 14, ab_14_14, ba_14_14, gauge_14_14, by decide, by decide⟩,
  ⟨14, 15, ab_14_15, ba_14_15, gauge_14_15, by decide, by decide⟩,
  ⟨14, 16, ab_14_16, ba_14_16, gauge_14_16, by decide, by decide⟩,
  ⟨14, 17, ab_14_17, ba_14_17, gauge_14_17, by decide, by decide⟩,
  ⟨14, 18, ab_14_18, ba_14_18, gauge_14_18, by decide, by decide⟩,
  ⟨14, 19, ab_14_19, ba_14_19, gauge_14_19, by decide, by decide⟩,
  ⟨14, 20, ab_14_20, ba_14_20, gauge_14_20, by decide, by decide⟩,
  ⟨14, 21, ab_14_21, ba_14_21, gauge_14_21, by decide, by decide⟩,
  ⟨14, 22, ab_14_22, ba_14_22, gauge_14_22, by decide, by decide⟩,
  ⟨14, 23, ab_14_23, ba_14_23, gauge_14_23, by decide, by decide⟩,
  ⟨14, 24, ab_14_24, ba_14_24, gauge_14_24, by decide, by decide⟩,
  ⟨15, 15, ab_15_15, ba_15_15, gauge_15_15, by decide, by decide⟩,
  ⟨15, 16, ab_15_16, ba_15_16, gauge_15_16, by decide, by decide⟩,
  ⟨15, 17, ab_15_17, ba_15_17, gauge_15_17, by decide, by decide⟩,
  ⟨15, 18, ab_15_18, ba_15_18, gauge_15_18, by decide, by decide⟩,
  ⟨15, 19, ab_15_19, ba_15_19, gauge_15_19, by decide, by decide⟩,
  ⟨15, 20, ab_15_20, ba_15_20, gauge_15_20, by decide, by decide⟩,
  ⟨15, 21, ab_15_21, ba_15_21, gauge_15_21, by decide, by decide⟩,
  ⟨15, 22, ab_15_22, ba_15_22, gauge_15_22, by decide, by decide⟩,
  ⟨15, 23, ab_15_23, ba_15_23, gauge_15_23, by decide, by decide⟩,
  ⟨15, 24, ab_15_24, ba_15_24, gauge_15_24, by decide, by decide⟩,
  ⟨16, 16, ab_16_16, ba_16_16, gauge_16_16, by decide, by decide⟩,
  ⟨16, 17, ab_16_17, ba_16_17, gauge_16_17, by decide, by decide⟩,
  ⟨16, 18, ab_16_18, ba_16_18, gauge_16_18, by decide, by decide⟩,
  ⟨16, 19, ab_16_19, ba_16_19, gauge_16_19, by decide, by decide⟩,
  ⟨16, 20, ab_16_20, ba_16_20, gauge_16_20, by decide, by decide⟩,
  ⟨16, 21, ab_16_21, ba_16_21, gauge_16_21, by decide, by decide⟩,
  ⟨16, 22, ab_16_22, ba_16_22, gauge_16_22, by decide, by decide⟩,
  ⟨16, 23, ab_16_23, ba_16_23, gauge_16_23, by decide, by decide⟩,
  ⟨16, 24, ab_16_24, ba_16_24, gauge_16_24, by decide, by decide⟩,
  ⟨17, 17, ab_17_17, ba_17_17, gauge_17_17, by decide, by decide⟩,
  ⟨17, 18, ab_17_18, ba_17_18, gauge_17_18, by decide, by decide⟩,
  ⟨17, 19, ab_17_19, ba_17_19, gauge_17_19, by decide, by decide⟩,
  ⟨17, 20, ab_17_20, ba_17_20, gauge_17_20, by decide, by decide⟩,
  ⟨17, 21, ab_17_21, ba_17_21, gauge_17_21, by decide, by decide⟩,
  ⟨17, 22, ab_17_22, ba_17_22, gauge_17_22, by decide, by decide⟩,
  ⟨17, 23, ab_17_23, ba_17_23, gauge_17_23, by decide, by decide⟩,
  ⟨17, 24, ab_17_24, ba_17_24, gauge_17_24, by decide, by decide⟩,
  ⟨18, 18, ab_18_18, ba_18_18, gauge_18_18, by decide, by decide⟩,
  ⟨18, 19, ab_18_19, ba_18_19, gauge_18_19, by decide, by decide⟩,
  ⟨18, 20, ab_18_20, ba_18_20, gauge_18_20, by decide, by decide⟩,
  ⟨18, 21, ab_18_21, ba_18_21, gauge_18_21, by decide, by decide⟩,
  ⟨18, 22, ab_18_22, ba_18_22, gauge_18_22, by decide, by decide⟩,
  ⟨18, 23, ab_18_23, ba_18_23, gauge_18_23, by decide, by decide⟩,
  ⟨18, 24, ab_18_24, ba_18_24, gauge_18_24, by decide, by decide⟩,
  ⟨19, 19, ab_19_19, ba_19_19, gauge_19_19, by decide, by decide⟩,
  ⟨19, 20, ab_19_20, ba_19_20, gauge_19_20, by decide, by decide⟩,
  ⟨19, 21, ab_19_21, ba_19_21, gauge_19_21, by decide, by decide⟩,
  ⟨19, 22, ab_19_22, ba_19_22, gauge_19_22, by decide, by decide⟩,
  ⟨19, 23, ab_19_23, ba_19_23, gauge_19_23, by decide, by decide⟩,
  ⟨19, 24, ab_19_24, ba_19_24, gauge_19_24, by decide, by decide⟩,
  ⟨20, 20, ab_20_20, ba_20_20, gauge_20_20, by decide, by decide⟩,
  ⟨20, 21, ab_20_21, ba_20_21, gauge_20_21, by decide, by decide⟩,
  ⟨20, 22, ab_20_22, ba_20_22, gauge_20_22, by decide, by decide⟩,
  ⟨20, 23, ab_20_23, ba_20_23, gauge_20_23, by decide, by decide⟩,
  ⟨20, 24, ab_20_24, ba_20_24, gauge_20_24, by decide, by decide⟩,
  ⟨21, 21, ab_21_21, ba_21_21, gauge_21_21, by decide, by decide⟩,
  ⟨21, 22, ab_21_22, ba_21_22, gauge_21_22, by decide, by decide⟩,
  ⟨21, 23, ab_21_23, ba_21_23, gauge_21_23, by decide, by decide⟩,
  ⟨21, 24, ab_21_24, ba_21_24, gauge_21_24, by decide, by decide⟩,
  ⟨22, 22, ab_22_22, ba_22_22, gauge_22_22, by decide, by decide⟩,
  ⟨22, 23, ab_22_23, ba_22_23, gauge_22_23, by decide, by decide⟩,
  ⟨22, 24, ab_22_24, ba_22_24, gauge_22_24, by decide, by decide⟩,
  ⟨23, 23, ab_23_23, ba_23_23, gauge_23_23, by decide, by decide⟩,
  ⟨23, 24, ab_23_24, ba_23_24, gauge_23_24, by decide, by decide⟩,
  ⟨24, 24, ab_24_24, ba_24_24, gauge_24_24, by decide, by decide⟩
]

def coordinateByNat (c : Nat) : Nat × Nat :=
  ((coordinateData[c]!).a, (coordinateData[c]!).b)

def coordinate (c : Coord) : Nat × Nat := coordinateByNat c.val

def coefficient (row : Nat → Nat → Nat → Int) (k : Nat) (c : Coord) : Int :=
  row k (coordinate c).1 (coordinate c).2

def witnessCoefficient (c : Coord) : Int :=
  witness (coordinate c).1 (coordinate c).2

def rowValue (row : Nat → Coord → Int) (k : Nat) (X : Vector) : ℝ :=
  ∑ c, (row k c : ℝ) * X c

def functional (X : Vector) : ℝ := ∑ c, (witnessCoefficient c : ℝ) * X c

def combinedCoefficient (data : List (Nat × Int)) (row : Nat → Coord → Int)
    (c : Coord) : Int :=
  (data.map (fun kc => kc.2 * row kc.1 c)).sum

def combinedValue (data : List (Nat × Int)) (row : Nat → Coord → Int)
    (X : Vector) : ℝ :=
  (data.map (fun kc => (kc.2 : ℝ) * rowValue row kc.1 X)).sum

theorem combination_expands (data : List (Nat × Int)) (row : Nat → Coord → Int)
    (X : Vector) :
    combinedValue data row X = ∑ c, (combinedCoefficient data row c : ℝ) * X c := by
  induction data with
  | nil => simp [combinedValue, combinedCoefficient]
  | cons kc rest ih =>
    simp only [combinedValue, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp [combinedCoefficient, Int.cast_add, Int.cast_mul, add_mul,
      Finset.sum_add_distrib, rowValue, Finset.mul_sum, mul_assoc]

theorem combination_zero (data : List (Nat × Int)) (row : Nat → Coord → Int)
    (X : Vector) (hrows : ∀ kc ∈ data, rowValue row kc.1 X = 0) :
    combinedValue data row X = 0 := by
  induction data with
  | nil => simp [combinedValue]
  | cons kc rest ih =>
    have hk := hrows kc (by simp)
    have hr : ∀ t ∈ rest, rowValue row t.1 X = 0 := by
      intro t ht
      exact hrows t (by simp [ht])
    simp only [combinedValue, List.map_cons, List.sum_cons]
    change (kc.2 : ℝ) * rowValue row kc.1 X + combinedValue rest row X = 0
    rw [hk, ih hr]
    simp

theorem certified_rows_force_zero (data : List (Nat × Int))
    (row : Nat → Coord → Int) (scale : Int) (X : Vector)
    (hscale : scale ≠ 0)
    (hcertificate : ∀ c, combinedCoefficient data row c = scale * witnessCoefficient c)
    (hrows : ∀ kc ∈ data, rowValue row kc.1 X = 0) : functional X = 0 := by
  have hzero := combination_zero data row X hrows
  rw [combination_expands] at hzero
  simp_rw [hcertificate, Int.cast_mul, mul_assoc] at hzero
  rw [← Finset.mul_sum] at hzero
  have hs : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale
  exact (mul_eq_zero.mp hzero).resolve_left hs

theorem ab_certificate (c : Coord) :
    combinedCoefficient abRows (coefficient rowAB) c =
      abScale * witnessCoefficient c := by
  change abIdentity (coordinate c).1 (coordinate c).2
  exact (coordinateData[c.val]!).ab

theorem ab_rows_in_range : ∀ kc ∈ abRows, kc.1 < 1088 := by
  decide +kernel

theorem ab_functional_zero (X : Vector)
    (hrows : ∀ k < 1088, rowValue (coefficient rowAB) k X = 0) :
    functional X = 0 := by
  apply certified_rows_force_zero abRows (coefficient rowAB) abScale X
  · norm_num [abScale]
  · exact ab_certificate
  · intro kc hk
    exact hrows kc.1 (ab_rows_in_range kc hk)

theorem ba_certificate (c : Coord) :
    combinedCoefficient baRows (coefficient rowBA) c =
      baScale * witnessCoefficient c := by
  change baIdentity (coordinate c).1 (coordinate c).2
  exact (coordinateData[c.val]!).ba

theorem ba_rows_in_range : ∀ kc ∈ baRows, kc.1 < 1088 := by
  decide +kernel

theorem ba_functional_zero (X : Vector)
    (hrows : ∀ k < 1088, rowValue (coefficient rowBA) k X = 0) :
    functional X = 0 := by
  apply certified_rows_force_zero baRows (coefficient rowBA) baScale X
  · norm_num [baScale]
  · exact ba_certificate
  · intro kc hk
    exact hrows kc.1 (ba_rows_in_range kc hk)

theorem gauge_certificate (c : Coord) :
    combinedCoefficient gaugeRows (coefficient rowGauge16) c =
      gaugeScale * witnessCoefficient c := by
  change gaugeIdentity (coordinate c).1 (coordinate c).2
  exact (coordinateData[c.val]!).gauge

theorem gauge_rows_in_range : ∀ kc ∈ gaugeRows, kc.1 < 16384 := by
  decide +kernel

theorem gauge_functional_zero (X : Vector)
    (hrows : ∀ k < 16384, rowValue (coefficient rowGauge16) k X = 0) :
    functional X = 0 := by
  apply certified_rows_force_zero gaugeRows (coefficient rowGauge16) gaugeScale X
  · norm_num [gaugeScale]
  · exact gauge_certificate
  · intro kc hk
    exact hrows kc.1 (gauge_rows_in_range kc hk)

theorem functional_add (X Y : Vector) : functional (X + Y) = functional X + functional Y := by
  simp [functional, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem functional_sub (X Y : Vector) : functional (X - Y) = functional X - functional Y := by
  simp [functional, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The normalized diagonal Choi representative of the identity-diluted switch. -/
def targetEntry (lambda mu : ℝ) (a b : Nat) : ℝ :=
  if a != b then 0
  else if a < 16 then (1 - lambda) * (1 - mu) / 8
  else if a < 20 then lambda * (1 - mu) / 4
  else if a < 24 then (1 - lambda) * mu / 4
  else lambda * mu / 2

def target (lambda mu : ℝ) (c : Coord) : ℝ :=
  targetEntry lambda mu (coordinate c).1 (coordinate c).2

theorem diagonal_witness (a : Nat) : witness a a = if a = 24 then 1 else 0 := by
  unfold witness
  split_ifs <;> simp_all <;> omega

theorem target_entry_witness (lambda mu : ℝ) (a b : Nat) :
    (witness a b : ℝ) * targetEntry lambda mu a b =
      if a = 24 ∧ b = 24 then lambda * mu / 2 else 0 := by
  by_cases hab : a = b
  · subst b
    rw [diagonal_witness]
    by_cases ha : a = 24
    · subst a
      norm_num [targetEntry]
    · simp [ha]
  · have hnot : ¬ (a = 24 ∧ b = 24) := by
      rintro ⟨ha, hb⟩
      exact hab (ha.trans hb.symm)
    simp [targetEntry, hab, hnot]

theorem coordinate_last : ∀ c : Coord,
    ((coordinate c).1 = 24 ∧ (coordinate c).2 = 24) ↔ c = 324 := by
  decide +kernel

theorem target_witness_coefficient (lambda mu : ℝ) (c : Coord) :
    (witnessCoefficient c : ℝ) * target lambda mu c =
      if c = (324 : Coord) then lambda * mu / 2 else 0 := by
  unfold witnessCoefficient target
  simp only [target_entry_witness, coordinate_last]

theorem functional_target (lambda mu : ℝ) :
    functional (target lambda mu) = lambda * mu / 2 := by
  unfold functional
  simp_rw [target_witness_coefficient]
  simp

/-- No supported real symmetric coefficient decomposition can satisfy both
ordered homogeneous cones and the CPTP-gauge equality for positive switch weight.
Positivity is used elsewhere to force the support; it is not needed once these
explicit tensor-row hypotheses hold. -/
theorem no_supported_decomposition (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu)
    (XAB XBA : Vector)
    (hAB : ∀ k < 1088, rowValue (coefficient rowAB) k XAB = 0)
    (hBA : ∀ k < 1088, rowValue (coefficient rowBA) k XBA = 0)
    (hGauge : ∀ k < 16384, rowValue (coefficient rowGauge16) k
      (XAB + XBA - target lambda mu) = 0) : False := by
  have h1 := ab_functional_zero XAB hAB
  have h2 := ba_functional_zero XBA hBA
  have h3 := gauge_functional_zero (XAB + XBA - target lambda mu) hGauge
  rw [functional_sub, functional_add, functional_target, h1, h2] at h3
  have hp : 0 < lambda * mu := mul_pos hlambda hmu
  linarith

end
end ICO.ExactSeparation
