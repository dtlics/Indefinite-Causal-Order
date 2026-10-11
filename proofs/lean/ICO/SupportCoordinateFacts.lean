import ICO.ExactSeparation
import ICO.ExactSupportIndependence
import ICO.PositiveSupport
import Mathlib.Tactic

/-! Real symmetric coordinates of a supported positive Choi decomposition.
This connects complex Kraus vectors to the real325-coordinate convention used
by the exact tensor certificates. -/

namespace ICO.SupportCoordinates

open ICO.ExactSeparation ICO.ExactSupportIndependence ICO.ExactTensorCertificates
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable section

def pairIndex (a b : Fin 25) : Coord :=
  let lo := min a.val b.val
  let hi := max a.val b.val
  ⟨(25 * lo - lo * (lo - 1) / 2 + hi - lo) % 325, by omega⟩


theorem coordinate_bounds (c : Coord) : (coordinate c).1 ≤ (coordinate c).2 ∧ (coordinate c).2 < 25 := by
  exact ⟨(coordinateData[c.val]!).a_le_b, (coordinateData[c.val]!).b_lt25⟩

theorem pairIndex_coordinate_0_0 : coordinate (pairIndex (0 : Fin 25) (0 : Fin 25)) = (min 0 0, max 0 0) := by
  have hidx : pairIndex (0 : Fin 25) (0 : Fin 25) = (0 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_1 : coordinate (pairIndex (0 : Fin 25) (1 : Fin 25)) = (min 0 1, max 0 1) := by
  have hidx : pairIndex (0 : Fin 25) (1 : Fin 25) = (1 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_2 : coordinate (pairIndex (0 : Fin 25) (2 : Fin 25)) = (min 0 2, max 0 2) := by
  have hidx : pairIndex (0 : Fin 25) (2 : Fin 25) = (2 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_3 : coordinate (pairIndex (0 : Fin 25) (3 : Fin 25)) = (min 0 3, max 0 3) := by
  have hidx : pairIndex (0 : Fin 25) (3 : Fin 25) = (3 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_4 : coordinate (pairIndex (0 : Fin 25) (4 : Fin 25)) = (min 0 4, max 0 4) := by
  have hidx : pairIndex (0 : Fin 25) (4 : Fin 25) = (4 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_5 : coordinate (pairIndex (0 : Fin 25) (5 : Fin 25)) = (min 0 5, max 0 5) := by
  have hidx : pairIndex (0 : Fin 25) (5 : Fin 25) = (5 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_6 : coordinate (pairIndex (0 : Fin 25) (6 : Fin 25)) = (min 0 6, max 0 6) := by
  have hidx : pairIndex (0 : Fin 25) (6 : Fin 25) = (6 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_7 : coordinate (pairIndex (0 : Fin 25) (7 : Fin 25)) = (min 0 7, max 0 7) := by
  have hidx : pairIndex (0 : Fin 25) (7 : Fin 25) = (7 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_8 : coordinate (pairIndex (0 : Fin 25) (8 : Fin 25)) = (min 0 8, max 0 8) := by
  have hidx : pairIndex (0 : Fin 25) (8 : Fin 25) = (8 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_9 : coordinate (pairIndex (0 : Fin 25) (9 : Fin 25)) = (min 0 9, max 0 9) := by
  have hidx : pairIndex (0 : Fin 25) (9 : Fin 25) = (9 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_10 : coordinate (pairIndex (0 : Fin 25) (10 : Fin 25)) = (min 0 10, max 0 10) := by
  have hidx : pairIndex (0 : Fin 25) (10 : Fin 25) = (10 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_11 : coordinate (pairIndex (0 : Fin 25) (11 : Fin 25)) = (min 0 11, max 0 11) := by
  have hidx : pairIndex (0 : Fin 25) (11 : Fin 25) = (11 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_12 : coordinate (pairIndex (0 : Fin 25) (12 : Fin 25)) = (min 0 12, max 0 12) := by
  have hidx : pairIndex (0 : Fin 25) (12 : Fin 25) = (12 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_13 : coordinate (pairIndex (0 : Fin 25) (13 : Fin 25)) = (min 0 13, max 0 13) := by
  have hidx : pairIndex (0 : Fin 25) (13 : Fin 25) = (13 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_14 : coordinate (pairIndex (0 : Fin 25) (14 : Fin 25)) = (min 0 14, max 0 14) := by
  have hidx : pairIndex (0 : Fin 25) (14 : Fin 25) = (14 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_15 : coordinate (pairIndex (0 : Fin 25) (15 : Fin 25)) = (min 0 15, max 0 15) := by
  have hidx : pairIndex (0 : Fin 25) (15 : Fin 25) = (15 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_16 : coordinate (pairIndex (0 : Fin 25) (16 : Fin 25)) = (min 0 16, max 0 16) := by
  have hidx : pairIndex (0 : Fin 25) (16 : Fin 25) = (16 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_17 : coordinate (pairIndex (0 : Fin 25) (17 : Fin 25)) = (min 0 17, max 0 17) := by
  have hidx : pairIndex (0 : Fin 25) (17 : Fin 25) = (17 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_18 : coordinate (pairIndex (0 : Fin 25) (18 : Fin 25)) = (min 0 18, max 0 18) := by
  have hidx : pairIndex (0 : Fin 25) (18 : Fin 25) = (18 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_19 : coordinate (pairIndex (0 : Fin 25) (19 : Fin 25)) = (min 0 19, max 0 19) := by
  have hidx : pairIndex (0 : Fin 25) (19 : Fin 25) = (19 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_20 : coordinate (pairIndex (0 : Fin 25) (20 : Fin 25)) = (min 0 20, max 0 20) := by
  have hidx : pairIndex (0 : Fin 25) (20 : Fin 25) = (20 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_21 : coordinate (pairIndex (0 : Fin 25) (21 : Fin 25)) = (min 0 21, max 0 21) := by
  have hidx : pairIndex (0 : Fin 25) (21 : Fin 25) = (21 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_22 : coordinate (pairIndex (0 : Fin 25) (22 : Fin 25)) = (min 0 22, max 0 22) := by
  have hidx : pairIndex (0 : Fin 25) (22 : Fin 25) = (22 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_23 : coordinate (pairIndex (0 : Fin 25) (23 : Fin 25)) = (min 0 23, max 0 23) := by
  have hidx : pairIndex (0 : Fin 25) (23 : Fin 25) = (23 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_0_24 : coordinate (pairIndex (0 : Fin 25) (24 : Fin 25)) = (min 0 24, max 0 24) := by
  have hidx : pairIndex (0 : Fin 25) (24 : Fin 25) = (24 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_0 : coordinate (pairIndex (1 : Fin 25) (0 : Fin 25)) = (min 1 0, max 1 0) := by
  have hidx : pairIndex (1 : Fin 25) (0 : Fin 25) = (1 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_1 : coordinate (pairIndex (1 : Fin 25) (1 : Fin 25)) = (min 1 1, max 1 1) := by
  have hidx : pairIndex (1 : Fin 25) (1 : Fin 25) = (25 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_2 : coordinate (pairIndex (1 : Fin 25) (2 : Fin 25)) = (min 1 2, max 1 2) := by
  have hidx : pairIndex (1 : Fin 25) (2 : Fin 25) = (26 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_3 : coordinate (pairIndex (1 : Fin 25) (3 : Fin 25)) = (min 1 3, max 1 3) := by
  have hidx : pairIndex (1 : Fin 25) (3 : Fin 25) = (27 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_4 : coordinate (pairIndex (1 : Fin 25) (4 : Fin 25)) = (min 1 4, max 1 4) := by
  have hidx : pairIndex (1 : Fin 25) (4 : Fin 25) = (28 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_5 : coordinate (pairIndex (1 : Fin 25) (5 : Fin 25)) = (min 1 5, max 1 5) := by
  have hidx : pairIndex (1 : Fin 25) (5 : Fin 25) = (29 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_6 : coordinate (pairIndex (1 : Fin 25) (6 : Fin 25)) = (min 1 6, max 1 6) := by
  have hidx : pairIndex (1 : Fin 25) (6 : Fin 25) = (30 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_7 : coordinate (pairIndex (1 : Fin 25) (7 : Fin 25)) = (min 1 7, max 1 7) := by
  have hidx : pairIndex (1 : Fin 25) (7 : Fin 25) = (31 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_8 : coordinate (pairIndex (1 : Fin 25) (8 : Fin 25)) = (min 1 8, max 1 8) := by
  have hidx : pairIndex (1 : Fin 25) (8 : Fin 25) = (32 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_9 : coordinate (pairIndex (1 : Fin 25) (9 : Fin 25)) = (min 1 9, max 1 9) := by
  have hidx : pairIndex (1 : Fin 25) (9 : Fin 25) = (33 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_10 : coordinate (pairIndex (1 : Fin 25) (10 : Fin 25)) = (min 1 10, max 1 10) := by
  have hidx : pairIndex (1 : Fin 25) (10 : Fin 25) = (34 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_11 : coordinate (pairIndex (1 : Fin 25) (11 : Fin 25)) = (min 1 11, max 1 11) := by
  have hidx : pairIndex (1 : Fin 25) (11 : Fin 25) = (35 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_12 : coordinate (pairIndex (1 : Fin 25) (12 : Fin 25)) = (min 1 12, max 1 12) := by
  have hidx : pairIndex (1 : Fin 25) (12 : Fin 25) = (36 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_13 : coordinate (pairIndex (1 : Fin 25) (13 : Fin 25)) = (min 1 13, max 1 13) := by
  have hidx : pairIndex (1 : Fin 25) (13 : Fin 25) = (37 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_14 : coordinate (pairIndex (1 : Fin 25) (14 : Fin 25)) = (min 1 14, max 1 14) := by
  have hidx : pairIndex (1 : Fin 25) (14 : Fin 25) = (38 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_15 : coordinate (pairIndex (1 : Fin 25) (15 : Fin 25)) = (min 1 15, max 1 15) := by
  have hidx : pairIndex (1 : Fin 25) (15 : Fin 25) = (39 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_16 : coordinate (pairIndex (1 : Fin 25) (16 : Fin 25)) = (min 1 16, max 1 16) := by
  have hidx : pairIndex (1 : Fin 25) (16 : Fin 25) = (40 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_17 : coordinate (pairIndex (1 : Fin 25) (17 : Fin 25)) = (min 1 17, max 1 17) := by
  have hidx : pairIndex (1 : Fin 25) (17 : Fin 25) = (41 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_18 : coordinate (pairIndex (1 : Fin 25) (18 : Fin 25)) = (min 1 18, max 1 18) := by
  have hidx : pairIndex (1 : Fin 25) (18 : Fin 25) = (42 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_19 : coordinate (pairIndex (1 : Fin 25) (19 : Fin 25)) = (min 1 19, max 1 19) := by
  have hidx : pairIndex (1 : Fin 25) (19 : Fin 25) = (43 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_20 : coordinate (pairIndex (1 : Fin 25) (20 : Fin 25)) = (min 1 20, max 1 20) := by
  have hidx : pairIndex (1 : Fin 25) (20 : Fin 25) = (44 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_21 : coordinate (pairIndex (1 : Fin 25) (21 : Fin 25)) = (min 1 21, max 1 21) := by
  have hidx : pairIndex (1 : Fin 25) (21 : Fin 25) = (45 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_22 : coordinate (pairIndex (1 : Fin 25) (22 : Fin 25)) = (min 1 22, max 1 22) := by
  have hidx : pairIndex (1 : Fin 25) (22 : Fin 25) = (46 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_23 : coordinate (pairIndex (1 : Fin 25) (23 : Fin 25)) = (min 1 23, max 1 23) := by
  have hidx : pairIndex (1 : Fin 25) (23 : Fin 25) = (47 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_1_24 : coordinate (pairIndex (1 : Fin 25) (24 : Fin 25)) = (min 1 24, max 1 24) := by
  have hidx : pairIndex (1 : Fin 25) (24 : Fin 25) = (48 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_0 : coordinate (pairIndex (2 : Fin 25) (0 : Fin 25)) = (min 2 0, max 2 0) := by
  have hidx : pairIndex (2 : Fin 25) (0 : Fin 25) = (2 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_1 : coordinate (pairIndex (2 : Fin 25) (1 : Fin 25)) = (min 2 1, max 2 1) := by
  have hidx : pairIndex (2 : Fin 25) (1 : Fin 25) = (26 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_2 : coordinate (pairIndex (2 : Fin 25) (2 : Fin 25)) = (min 2 2, max 2 2) := by
  have hidx : pairIndex (2 : Fin 25) (2 : Fin 25) = (49 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_3 : coordinate (pairIndex (2 : Fin 25) (3 : Fin 25)) = (min 2 3, max 2 3) := by
  have hidx : pairIndex (2 : Fin 25) (3 : Fin 25) = (50 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_4 : coordinate (pairIndex (2 : Fin 25) (4 : Fin 25)) = (min 2 4, max 2 4) := by
  have hidx : pairIndex (2 : Fin 25) (4 : Fin 25) = (51 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_5 : coordinate (pairIndex (2 : Fin 25) (5 : Fin 25)) = (min 2 5, max 2 5) := by
  have hidx : pairIndex (2 : Fin 25) (5 : Fin 25) = (52 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_6 : coordinate (pairIndex (2 : Fin 25) (6 : Fin 25)) = (min 2 6, max 2 6) := by
  have hidx : pairIndex (2 : Fin 25) (6 : Fin 25) = (53 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_7 : coordinate (pairIndex (2 : Fin 25) (7 : Fin 25)) = (min 2 7, max 2 7) := by
  have hidx : pairIndex (2 : Fin 25) (7 : Fin 25) = (54 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_8 : coordinate (pairIndex (2 : Fin 25) (8 : Fin 25)) = (min 2 8, max 2 8) := by
  have hidx : pairIndex (2 : Fin 25) (8 : Fin 25) = (55 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_9 : coordinate (pairIndex (2 : Fin 25) (9 : Fin 25)) = (min 2 9, max 2 9) := by
  have hidx : pairIndex (2 : Fin 25) (9 : Fin 25) = (56 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_10 : coordinate (pairIndex (2 : Fin 25) (10 : Fin 25)) = (min 2 10, max 2 10) := by
  have hidx : pairIndex (2 : Fin 25) (10 : Fin 25) = (57 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_11 : coordinate (pairIndex (2 : Fin 25) (11 : Fin 25)) = (min 2 11, max 2 11) := by
  have hidx : pairIndex (2 : Fin 25) (11 : Fin 25) = (58 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_12 : coordinate (pairIndex (2 : Fin 25) (12 : Fin 25)) = (min 2 12, max 2 12) := by
  have hidx : pairIndex (2 : Fin 25) (12 : Fin 25) = (59 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_13 : coordinate (pairIndex (2 : Fin 25) (13 : Fin 25)) = (min 2 13, max 2 13) := by
  have hidx : pairIndex (2 : Fin 25) (13 : Fin 25) = (60 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_14 : coordinate (pairIndex (2 : Fin 25) (14 : Fin 25)) = (min 2 14, max 2 14) := by
  have hidx : pairIndex (2 : Fin 25) (14 : Fin 25) = (61 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_15 : coordinate (pairIndex (2 : Fin 25) (15 : Fin 25)) = (min 2 15, max 2 15) := by
  have hidx : pairIndex (2 : Fin 25) (15 : Fin 25) = (62 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_16 : coordinate (pairIndex (2 : Fin 25) (16 : Fin 25)) = (min 2 16, max 2 16) := by
  have hidx : pairIndex (2 : Fin 25) (16 : Fin 25) = (63 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_17 : coordinate (pairIndex (2 : Fin 25) (17 : Fin 25)) = (min 2 17, max 2 17) := by
  have hidx : pairIndex (2 : Fin 25) (17 : Fin 25) = (64 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_18 : coordinate (pairIndex (2 : Fin 25) (18 : Fin 25)) = (min 2 18, max 2 18) := by
  have hidx : pairIndex (2 : Fin 25) (18 : Fin 25) = (65 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_19 : coordinate (pairIndex (2 : Fin 25) (19 : Fin 25)) = (min 2 19, max 2 19) := by
  have hidx : pairIndex (2 : Fin 25) (19 : Fin 25) = (66 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_20 : coordinate (pairIndex (2 : Fin 25) (20 : Fin 25)) = (min 2 20, max 2 20) := by
  have hidx : pairIndex (2 : Fin 25) (20 : Fin 25) = (67 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_21 : coordinate (pairIndex (2 : Fin 25) (21 : Fin 25)) = (min 2 21, max 2 21) := by
  have hidx : pairIndex (2 : Fin 25) (21 : Fin 25) = (68 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_22 : coordinate (pairIndex (2 : Fin 25) (22 : Fin 25)) = (min 2 22, max 2 22) := by
  have hidx : pairIndex (2 : Fin 25) (22 : Fin 25) = (69 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_23 : coordinate (pairIndex (2 : Fin 25) (23 : Fin 25)) = (min 2 23, max 2 23) := by
  have hidx : pairIndex (2 : Fin 25) (23 : Fin 25) = (70 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_2_24 : coordinate (pairIndex (2 : Fin 25) (24 : Fin 25)) = (min 2 24, max 2 24) := by
  have hidx : pairIndex (2 : Fin 25) (24 : Fin 25) = (71 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_0 : coordinate (pairIndex (3 : Fin 25) (0 : Fin 25)) = (min 3 0, max 3 0) := by
  have hidx : pairIndex (3 : Fin 25) (0 : Fin 25) = (3 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_1 : coordinate (pairIndex (3 : Fin 25) (1 : Fin 25)) = (min 3 1, max 3 1) := by
  have hidx : pairIndex (3 : Fin 25) (1 : Fin 25) = (27 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_2 : coordinate (pairIndex (3 : Fin 25) (2 : Fin 25)) = (min 3 2, max 3 2) := by
  have hidx : pairIndex (3 : Fin 25) (2 : Fin 25) = (50 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_3 : coordinate (pairIndex (3 : Fin 25) (3 : Fin 25)) = (min 3 3, max 3 3) := by
  have hidx : pairIndex (3 : Fin 25) (3 : Fin 25) = (72 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_4 : coordinate (pairIndex (3 : Fin 25) (4 : Fin 25)) = (min 3 4, max 3 4) := by
  have hidx : pairIndex (3 : Fin 25) (4 : Fin 25) = (73 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_5 : coordinate (pairIndex (3 : Fin 25) (5 : Fin 25)) = (min 3 5, max 3 5) := by
  have hidx : pairIndex (3 : Fin 25) (5 : Fin 25) = (74 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_6 : coordinate (pairIndex (3 : Fin 25) (6 : Fin 25)) = (min 3 6, max 3 6) := by
  have hidx : pairIndex (3 : Fin 25) (6 : Fin 25) = (75 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_7 : coordinate (pairIndex (3 : Fin 25) (7 : Fin 25)) = (min 3 7, max 3 7) := by
  have hidx : pairIndex (3 : Fin 25) (7 : Fin 25) = (76 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_8 : coordinate (pairIndex (3 : Fin 25) (8 : Fin 25)) = (min 3 8, max 3 8) := by
  have hidx : pairIndex (3 : Fin 25) (8 : Fin 25) = (77 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_9 : coordinate (pairIndex (3 : Fin 25) (9 : Fin 25)) = (min 3 9, max 3 9) := by
  have hidx : pairIndex (3 : Fin 25) (9 : Fin 25) = (78 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_10 : coordinate (pairIndex (3 : Fin 25) (10 : Fin 25)) = (min 3 10, max 3 10) := by
  have hidx : pairIndex (3 : Fin 25) (10 : Fin 25) = (79 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_11 : coordinate (pairIndex (3 : Fin 25) (11 : Fin 25)) = (min 3 11, max 3 11) := by
  have hidx : pairIndex (3 : Fin 25) (11 : Fin 25) = (80 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_12 : coordinate (pairIndex (3 : Fin 25) (12 : Fin 25)) = (min 3 12, max 3 12) := by
  have hidx : pairIndex (3 : Fin 25) (12 : Fin 25) = (81 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_13 : coordinate (pairIndex (3 : Fin 25) (13 : Fin 25)) = (min 3 13, max 3 13) := by
  have hidx : pairIndex (3 : Fin 25) (13 : Fin 25) = (82 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_14 : coordinate (pairIndex (3 : Fin 25) (14 : Fin 25)) = (min 3 14, max 3 14) := by
  have hidx : pairIndex (3 : Fin 25) (14 : Fin 25) = (83 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_15 : coordinate (pairIndex (3 : Fin 25) (15 : Fin 25)) = (min 3 15, max 3 15) := by
  have hidx : pairIndex (3 : Fin 25) (15 : Fin 25) = (84 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_16 : coordinate (pairIndex (3 : Fin 25) (16 : Fin 25)) = (min 3 16, max 3 16) := by
  have hidx : pairIndex (3 : Fin 25) (16 : Fin 25) = (85 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_17 : coordinate (pairIndex (3 : Fin 25) (17 : Fin 25)) = (min 3 17, max 3 17) := by
  have hidx : pairIndex (3 : Fin 25) (17 : Fin 25) = (86 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_18 : coordinate (pairIndex (3 : Fin 25) (18 : Fin 25)) = (min 3 18, max 3 18) := by
  have hidx : pairIndex (3 : Fin 25) (18 : Fin 25) = (87 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_19 : coordinate (pairIndex (3 : Fin 25) (19 : Fin 25)) = (min 3 19, max 3 19) := by
  have hidx : pairIndex (3 : Fin 25) (19 : Fin 25) = (88 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_20 : coordinate (pairIndex (3 : Fin 25) (20 : Fin 25)) = (min 3 20, max 3 20) := by
  have hidx : pairIndex (3 : Fin 25) (20 : Fin 25) = (89 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_21 : coordinate (pairIndex (3 : Fin 25) (21 : Fin 25)) = (min 3 21, max 3 21) := by
  have hidx : pairIndex (3 : Fin 25) (21 : Fin 25) = (90 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_22 : coordinate (pairIndex (3 : Fin 25) (22 : Fin 25)) = (min 3 22, max 3 22) := by
  have hidx : pairIndex (3 : Fin 25) (22 : Fin 25) = (91 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_23 : coordinate (pairIndex (3 : Fin 25) (23 : Fin 25)) = (min 3 23, max 3 23) := by
  have hidx : pairIndex (3 : Fin 25) (23 : Fin 25) = (92 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_3_24 : coordinate (pairIndex (3 : Fin 25) (24 : Fin 25)) = (min 3 24, max 3 24) := by
  have hidx : pairIndex (3 : Fin 25) (24 : Fin 25) = (93 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_0 : coordinate (pairIndex (4 : Fin 25) (0 : Fin 25)) = (min 4 0, max 4 0) := by
  have hidx : pairIndex (4 : Fin 25) (0 : Fin 25) = (4 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_1 : coordinate (pairIndex (4 : Fin 25) (1 : Fin 25)) = (min 4 1, max 4 1) := by
  have hidx : pairIndex (4 : Fin 25) (1 : Fin 25) = (28 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_2 : coordinate (pairIndex (4 : Fin 25) (2 : Fin 25)) = (min 4 2, max 4 2) := by
  have hidx : pairIndex (4 : Fin 25) (2 : Fin 25) = (51 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_3 : coordinate (pairIndex (4 : Fin 25) (3 : Fin 25)) = (min 4 3, max 4 3) := by
  have hidx : pairIndex (4 : Fin 25) (3 : Fin 25) = (73 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_4 : coordinate (pairIndex (4 : Fin 25) (4 : Fin 25)) = (min 4 4, max 4 4) := by
  have hidx : pairIndex (4 : Fin 25) (4 : Fin 25) = (94 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_5 : coordinate (pairIndex (4 : Fin 25) (5 : Fin 25)) = (min 4 5, max 4 5) := by
  have hidx : pairIndex (4 : Fin 25) (5 : Fin 25) = (95 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_6 : coordinate (pairIndex (4 : Fin 25) (6 : Fin 25)) = (min 4 6, max 4 6) := by
  have hidx : pairIndex (4 : Fin 25) (6 : Fin 25) = (96 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_7 : coordinate (pairIndex (4 : Fin 25) (7 : Fin 25)) = (min 4 7, max 4 7) := by
  have hidx : pairIndex (4 : Fin 25) (7 : Fin 25) = (97 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_8 : coordinate (pairIndex (4 : Fin 25) (8 : Fin 25)) = (min 4 8, max 4 8) := by
  have hidx : pairIndex (4 : Fin 25) (8 : Fin 25) = (98 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_9 : coordinate (pairIndex (4 : Fin 25) (9 : Fin 25)) = (min 4 9, max 4 9) := by
  have hidx : pairIndex (4 : Fin 25) (9 : Fin 25) = (99 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_10 : coordinate (pairIndex (4 : Fin 25) (10 : Fin 25)) = (min 4 10, max 4 10) := by
  have hidx : pairIndex (4 : Fin 25) (10 : Fin 25) = (100 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_11 : coordinate (pairIndex (4 : Fin 25) (11 : Fin 25)) = (min 4 11, max 4 11) := by
  have hidx : pairIndex (4 : Fin 25) (11 : Fin 25) = (101 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_12 : coordinate (pairIndex (4 : Fin 25) (12 : Fin 25)) = (min 4 12, max 4 12) := by
  have hidx : pairIndex (4 : Fin 25) (12 : Fin 25) = (102 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_13 : coordinate (pairIndex (4 : Fin 25) (13 : Fin 25)) = (min 4 13, max 4 13) := by
  have hidx : pairIndex (4 : Fin 25) (13 : Fin 25) = (103 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_14 : coordinate (pairIndex (4 : Fin 25) (14 : Fin 25)) = (min 4 14, max 4 14) := by
  have hidx : pairIndex (4 : Fin 25) (14 : Fin 25) = (104 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_15 : coordinate (pairIndex (4 : Fin 25) (15 : Fin 25)) = (min 4 15, max 4 15) := by
  have hidx : pairIndex (4 : Fin 25) (15 : Fin 25) = (105 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_16 : coordinate (pairIndex (4 : Fin 25) (16 : Fin 25)) = (min 4 16, max 4 16) := by
  have hidx : pairIndex (4 : Fin 25) (16 : Fin 25) = (106 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_17 : coordinate (pairIndex (4 : Fin 25) (17 : Fin 25)) = (min 4 17, max 4 17) := by
  have hidx : pairIndex (4 : Fin 25) (17 : Fin 25) = (107 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_18 : coordinate (pairIndex (4 : Fin 25) (18 : Fin 25)) = (min 4 18, max 4 18) := by
  have hidx : pairIndex (4 : Fin 25) (18 : Fin 25) = (108 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_19 : coordinate (pairIndex (4 : Fin 25) (19 : Fin 25)) = (min 4 19, max 4 19) := by
  have hidx : pairIndex (4 : Fin 25) (19 : Fin 25) = (109 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_20 : coordinate (pairIndex (4 : Fin 25) (20 : Fin 25)) = (min 4 20, max 4 20) := by
  have hidx : pairIndex (4 : Fin 25) (20 : Fin 25) = (110 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_21 : coordinate (pairIndex (4 : Fin 25) (21 : Fin 25)) = (min 4 21, max 4 21) := by
  have hidx : pairIndex (4 : Fin 25) (21 : Fin 25) = (111 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_22 : coordinate (pairIndex (4 : Fin 25) (22 : Fin 25)) = (min 4 22, max 4 22) := by
  have hidx : pairIndex (4 : Fin 25) (22 : Fin 25) = (112 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_23 : coordinate (pairIndex (4 : Fin 25) (23 : Fin 25)) = (min 4 23, max 4 23) := by
  have hidx : pairIndex (4 : Fin 25) (23 : Fin 25) = (113 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_4_24 : coordinate (pairIndex (4 : Fin 25) (24 : Fin 25)) = (min 4 24, max 4 24) := by
  have hidx : pairIndex (4 : Fin 25) (24 : Fin 25) = (114 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_0 : coordinate (pairIndex (5 : Fin 25) (0 : Fin 25)) = (min 5 0, max 5 0) := by
  have hidx : pairIndex (5 : Fin 25) (0 : Fin 25) = (5 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_1 : coordinate (pairIndex (5 : Fin 25) (1 : Fin 25)) = (min 5 1, max 5 1) := by
  have hidx : pairIndex (5 : Fin 25) (1 : Fin 25) = (29 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_2 : coordinate (pairIndex (5 : Fin 25) (2 : Fin 25)) = (min 5 2, max 5 2) := by
  have hidx : pairIndex (5 : Fin 25) (2 : Fin 25) = (52 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_3 : coordinate (pairIndex (5 : Fin 25) (3 : Fin 25)) = (min 5 3, max 5 3) := by
  have hidx : pairIndex (5 : Fin 25) (3 : Fin 25) = (74 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_4 : coordinate (pairIndex (5 : Fin 25) (4 : Fin 25)) = (min 5 4, max 5 4) := by
  have hidx : pairIndex (5 : Fin 25) (4 : Fin 25) = (95 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_5 : coordinate (pairIndex (5 : Fin 25) (5 : Fin 25)) = (min 5 5, max 5 5) := by
  have hidx : pairIndex (5 : Fin 25) (5 : Fin 25) = (115 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_6 : coordinate (pairIndex (5 : Fin 25) (6 : Fin 25)) = (min 5 6, max 5 6) := by
  have hidx : pairIndex (5 : Fin 25) (6 : Fin 25) = (116 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_7 : coordinate (pairIndex (5 : Fin 25) (7 : Fin 25)) = (min 5 7, max 5 7) := by
  have hidx : pairIndex (5 : Fin 25) (7 : Fin 25) = (117 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_8 : coordinate (pairIndex (5 : Fin 25) (8 : Fin 25)) = (min 5 8, max 5 8) := by
  have hidx : pairIndex (5 : Fin 25) (8 : Fin 25) = (118 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_9 : coordinate (pairIndex (5 : Fin 25) (9 : Fin 25)) = (min 5 9, max 5 9) := by
  have hidx : pairIndex (5 : Fin 25) (9 : Fin 25) = (119 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_10 : coordinate (pairIndex (5 : Fin 25) (10 : Fin 25)) = (min 5 10, max 5 10) := by
  have hidx : pairIndex (5 : Fin 25) (10 : Fin 25) = (120 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_11 : coordinate (pairIndex (5 : Fin 25) (11 : Fin 25)) = (min 5 11, max 5 11) := by
  have hidx : pairIndex (5 : Fin 25) (11 : Fin 25) = (121 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_12 : coordinate (pairIndex (5 : Fin 25) (12 : Fin 25)) = (min 5 12, max 5 12) := by
  have hidx : pairIndex (5 : Fin 25) (12 : Fin 25) = (122 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_13 : coordinate (pairIndex (5 : Fin 25) (13 : Fin 25)) = (min 5 13, max 5 13) := by
  have hidx : pairIndex (5 : Fin 25) (13 : Fin 25) = (123 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_14 : coordinate (pairIndex (5 : Fin 25) (14 : Fin 25)) = (min 5 14, max 5 14) := by
  have hidx : pairIndex (5 : Fin 25) (14 : Fin 25) = (124 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_15 : coordinate (pairIndex (5 : Fin 25) (15 : Fin 25)) = (min 5 15, max 5 15) := by
  have hidx : pairIndex (5 : Fin 25) (15 : Fin 25) = (125 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_16 : coordinate (pairIndex (5 : Fin 25) (16 : Fin 25)) = (min 5 16, max 5 16) := by
  have hidx : pairIndex (5 : Fin 25) (16 : Fin 25) = (126 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_17 : coordinate (pairIndex (5 : Fin 25) (17 : Fin 25)) = (min 5 17, max 5 17) := by
  have hidx : pairIndex (5 : Fin 25) (17 : Fin 25) = (127 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_18 : coordinate (pairIndex (5 : Fin 25) (18 : Fin 25)) = (min 5 18, max 5 18) := by
  have hidx : pairIndex (5 : Fin 25) (18 : Fin 25) = (128 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_19 : coordinate (pairIndex (5 : Fin 25) (19 : Fin 25)) = (min 5 19, max 5 19) := by
  have hidx : pairIndex (5 : Fin 25) (19 : Fin 25) = (129 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_20 : coordinate (pairIndex (5 : Fin 25) (20 : Fin 25)) = (min 5 20, max 5 20) := by
  have hidx : pairIndex (5 : Fin 25) (20 : Fin 25) = (130 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_21 : coordinate (pairIndex (5 : Fin 25) (21 : Fin 25)) = (min 5 21, max 5 21) := by
  have hidx : pairIndex (5 : Fin 25) (21 : Fin 25) = (131 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_22 : coordinate (pairIndex (5 : Fin 25) (22 : Fin 25)) = (min 5 22, max 5 22) := by
  have hidx : pairIndex (5 : Fin 25) (22 : Fin 25) = (132 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_23 : coordinate (pairIndex (5 : Fin 25) (23 : Fin 25)) = (min 5 23, max 5 23) := by
  have hidx : pairIndex (5 : Fin 25) (23 : Fin 25) = (133 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_5_24 : coordinate (pairIndex (5 : Fin 25) (24 : Fin 25)) = (min 5 24, max 5 24) := by
  have hidx : pairIndex (5 : Fin 25) (24 : Fin 25) = (134 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_0 : coordinate (pairIndex (6 : Fin 25) (0 : Fin 25)) = (min 6 0, max 6 0) := by
  have hidx : pairIndex (6 : Fin 25) (0 : Fin 25) = (6 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_1 : coordinate (pairIndex (6 : Fin 25) (1 : Fin 25)) = (min 6 1, max 6 1) := by
  have hidx : pairIndex (6 : Fin 25) (1 : Fin 25) = (30 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_2 : coordinate (pairIndex (6 : Fin 25) (2 : Fin 25)) = (min 6 2, max 6 2) := by
  have hidx : pairIndex (6 : Fin 25) (2 : Fin 25) = (53 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_3 : coordinate (pairIndex (6 : Fin 25) (3 : Fin 25)) = (min 6 3, max 6 3) := by
  have hidx : pairIndex (6 : Fin 25) (3 : Fin 25) = (75 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_4 : coordinate (pairIndex (6 : Fin 25) (4 : Fin 25)) = (min 6 4, max 6 4) := by
  have hidx : pairIndex (6 : Fin 25) (4 : Fin 25) = (96 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_5 : coordinate (pairIndex (6 : Fin 25) (5 : Fin 25)) = (min 6 5, max 6 5) := by
  have hidx : pairIndex (6 : Fin 25) (5 : Fin 25) = (116 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_6 : coordinate (pairIndex (6 : Fin 25) (6 : Fin 25)) = (min 6 6, max 6 6) := by
  have hidx : pairIndex (6 : Fin 25) (6 : Fin 25) = (135 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_7 : coordinate (pairIndex (6 : Fin 25) (7 : Fin 25)) = (min 6 7, max 6 7) := by
  have hidx : pairIndex (6 : Fin 25) (7 : Fin 25) = (136 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_8 : coordinate (pairIndex (6 : Fin 25) (8 : Fin 25)) = (min 6 8, max 6 8) := by
  have hidx : pairIndex (6 : Fin 25) (8 : Fin 25) = (137 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_9 : coordinate (pairIndex (6 : Fin 25) (9 : Fin 25)) = (min 6 9, max 6 9) := by
  have hidx : pairIndex (6 : Fin 25) (9 : Fin 25) = (138 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_10 : coordinate (pairIndex (6 : Fin 25) (10 : Fin 25)) = (min 6 10, max 6 10) := by
  have hidx : pairIndex (6 : Fin 25) (10 : Fin 25) = (139 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_11 : coordinate (pairIndex (6 : Fin 25) (11 : Fin 25)) = (min 6 11, max 6 11) := by
  have hidx : pairIndex (6 : Fin 25) (11 : Fin 25) = (140 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_12 : coordinate (pairIndex (6 : Fin 25) (12 : Fin 25)) = (min 6 12, max 6 12) := by
  have hidx : pairIndex (6 : Fin 25) (12 : Fin 25) = (141 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_13 : coordinate (pairIndex (6 : Fin 25) (13 : Fin 25)) = (min 6 13, max 6 13) := by
  have hidx : pairIndex (6 : Fin 25) (13 : Fin 25) = (142 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_14 : coordinate (pairIndex (6 : Fin 25) (14 : Fin 25)) = (min 6 14, max 6 14) := by
  have hidx : pairIndex (6 : Fin 25) (14 : Fin 25) = (143 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_15 : coordinate (pairIndex (6 : Fin 25) (15 : Fin 25)) = (min 6 15, max 6 15) := by
  have hidx : pairIndex (6 : Fin 25) (15 : Fin 25) = (144 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_16 : coordinate (pairIndex (6 : Fin 25) (16 : Fin 25)) = (min 6 16, max 6 16) := by
  have hidx : pairIndex (6 : Fin 25) (16 : Fin 25) = (145 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_17 : coordinate (pairIndex (6 : Fin 25) (17 : Fin 25)) = (min 6 17, max 6 17) := by
  have hidx : pairIndex (6 : Fin 25) (17 : Fin 25) = (146 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_18 : coordinate (pairIndex (6 : Fin 25) (18 : Fin 25)) = (min 6 18, max 6 18) := by
  have hidx : pairIndex (6 : Fin 25) (18 : Fin 25) = (147 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_19 : coordinate (pairIndex (6 : Fin 25) (19 : Fin 25)) = (min 6 19, max 6 19) := by
  have hidx : pairIndex (6 : Fin 25) (19 : Fin 25) = (148 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_20 : coordinate (pairIndex (6 : Fin 25) (20 : Fin 25)) = (min 6 20, max 6 20) := by
  have hidx : pairIndex (6 : Fin 25) (20 : Fin 25) = (149 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_21 : coordinate (pairIndex (6 : Fin 25) (21 : Fin 25)) = (min 6 21, max 6 21) := by
  have hidx : pairIndex (6 : Fin 25) (21 : Fin 25) = (150 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_22 : coordinate (pairIndex (6 : Fin 25) (22 : Fin 25)) = (min 6 22, max 6 22) := by
  have hidx : pairIndex (6 : Fin 25) (22 : Fin 25) = (151 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_23 : coordinate (pairIndex (6 : Fin 25) (23 : Fin 25)) = (min 6 23, max 6 23) := by
  have hidx : pairIndex (6 : Fin 25) (23 : Fin 25) = (152 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_6_24 : coordinate (pairIndex (6 : Fin 25) (24 : Fin 25)) = (min 6 24, max 6 24) := by
  have hidx : pairIndex (6 : Fin 25) (24 : Fin 25) = (153 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_0 : coordinate (pairIndex (7 : Fin 25) (0 : Fin 25)) = (min 7 0, max 7 0) := by
  have hidx : pairIndex (7 : Fin 25) (0 : Fin 25) = (7 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_1 : coordinate (pairIndex (7 : Fin 25) (1 : Fin 25)) = (min 7 1, max 7 1) := by
  have hidx : pairIndex (7 : Fin 25) (1 : Fin 25) = (31 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_2 : coordinate (pairIndex (7 : Fin 25) (2 : Fin 25)) = (min 7 2, max 7 2) := by
  have hidx : pairIndex (7 : Fin 25) (2 : Fin 25) = (54 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_3 : coordinate (pairIndex (7 : Fin 25) (3 : Fin 25)) = (min 7 3, max 7 3) := by
  have hidx : pairIndex (7 : Fin 25) (3 : Fin 25) = (76 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_4 : coordinate (pairIndex (7 : Fin 25) (4 : Fin 25)) = (min 7 4, max 7 4) := by
  have hidx : pairIndex (7 : Fin 25) (4 : Fin 25) = (97 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_5 : coordinate (pairIndex (7 : Fin 25) (5 : Fin 25)) = (min 7 5, max 7 5) := by
  have hidx : pairIndex (7 : Fin 25) (5 : Fin 25) = (117 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_6 : coordinate (pairIndex (7 : Fin 25) (6 : Fin 25)) = (min 7 6, max 7 6) := by
  have hidx : pairIndex (7 : Fin 25) (6 : Fin 25) = (136 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_7 : coordinate (pairIndex (7 : Fin 25) (7 : Fin 25)) = (min 7 7, max 7 7) := by
  have hidx : pairIndex (7 : Fin 25) (7 : Fin 25) = (154 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_8 : coordinate (pairIndex (7 : Fin 25) (8 : Fin 25)) = (min 7 8, max 7 8) := by
  have hidx : pairIndex (7 : Fin 25) (8 : Fin 25) = (155 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_9 : coordinate (pairIndex (7 : Fin 25) (9 : Fin 25)) = (min 7 9, max 7 9) := by
  have hidx : pairIndex (7 : Fin 25) (9 : Fin 25) = (156 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_10 : coordinate (pairIndex (7 : Fin 25) (10 : Fin 25)) = (min 7 10, max 7 10) := by
  have hidx : pairIndex (7 : Fin 25) (10 : Fin 25) = (157 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_11 : coordinate (pairIndex (7 : Fin 25) (11 : Fin 25)) = (min 7 11, max 7 11) := by
  have hidx : pairIndex (7 : Fin 25) (11 : Fin 25) = (158 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_12 : coordinate (pairIndex (7 : Fin 25) (12 : Fin 25)) = (min 7 12, max 7 12) := by
  have hidx : pairIndex (7 : Fin 25) (12 : Fin 25) = (159 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_13 : coordinate (pairIndex (7 : Fin 25) (13 : Fin 25)) = (min 7 13, max 7 13) := by
  have hidx : pairIndex (7 : Fin 25) (13 : Fin 25) = (160 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_14 : coordinate (pairIndex (7 : Fin 25) (14 : Fin 25)) = (min 7 14, max 7 14) := by
  have hidx : pairIndex (7 : Fin 25) (14 : Fin 25) = (161 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_15 : coordinate (pairIndex (7 : Fin 25) (15 : Fin 25)) = (min 7 15, max 7 15) := by
  have hidx : pairIndex (7 : Fin 25) (15 : Fin 25) = (162 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_16 : coordinate (pairIndex (7 : Fin 25) (16 : Fin 25)) = (min 7 16, max 7 16) := by
  have hidx : pairIndex (7 : Fin 25) (16 : Fin 25) = (163 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_17 : coordinate (pairIndex (7 : Fin 25) (17 : Fin 25)) = (min 7 17, max 7 17) := by
  have hidx : pairIndex (7 : Fin 25) (17 : Fin 25) = (164 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_18 : coordinate (pairIndex (7 : Fin 25) (18 : Fin 25)) = (min 7 18, max 7 18) := by
  have hidx : pairIndex (7 : Fin 25) (18 : Fin 25) = (165 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_19 : coordinate (pairIndex (7 : Fin 25) (19 : Fin 25)) = (min 7 19, max 7 19) := by
  have hidx : pairIndex (7 : Fin 25) (19 : Fin 25) = (166 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_20 : coordinate (pairIndex (7 : Fin 25) (20 : Fin 25)) = (min 7 20, max 7 20) := by
  have hidx : pairIndex (7 : Fin 25) (20 : Fin 25) = (167 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_21 : coordinate (pairIndex (7 : Fin 25) (21 : Fin 25)) = (min 7 21, max 7 21) := by
  have hidx : pairIndex (7 : Fin 25) (21 : Fin 25) = (168 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_22 : coordinate (pairIndex (7 : Fin 25) (22 : Fin 25)) = (min 7 22, max 7 22) := by
  have hidx : pairIndex (7 : Fin 25) (22 : Fin 25) = (169 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_23 : coordinate (pairIndex (7 : Fin 25) (23 : Fin 25)) = (min 7 23, max 7 23) := by
  have hidx : pairIndex (7 : Fin 25) (23 : Fin 25) = (170 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_7_24 : coordinate (pairIndex (7 : Fin 25) (24 : Fin 25)) = (min 7 24, max 7 24) := by
  have hidx : pairIndex (7 : Fin 25) (24 : Fin 25) = (171 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_0 : coordinate (pairIndex (8 : Fin 25) (0 : Fin 25)) = (min 8 0, max 8 0) := by
  have hidx : pairIndex (8 : Fin 25) (0 : Fin 25) = (8 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_1 : coordinate (pairIndex (8 : Fin 25) (1 : Fin 25)) = (min 8 1, max 8 1) := by
  have hidx : pairIndex (8 : Fin 25) (1 : Fin 25) = (32 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_2 : coordinate (pairIndex (8 : Fin 25) (2 : Fin 25)) = (min 8 2, max 8 2) := by
  have hidx : pairIndex (8 : Fin 25) (2 : Fin 25) = (55 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_3 : coordinate (pairIndex (8 : Fin 25) (3 : Fin 25)) = (min 8 3, max 8 3) := by
  have hidx : pairIndex (8 : Fin 25) (3 : Fin 25) = (77 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_4 : coordinate (pairIndex (8 : Fin 25) (4 : Fin 25)) = (min 8 4, max 8 4) := by
  have hidx : pairIndex (8 : Fin 25) (4 : Fin 25) = (98 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_5 : coordinate (pairIndex (8 : Fin 25) (5 : Fin 25)) = (min 8 5, max 8 5) := by
  have hidx : pairIndex (8 : Fin 25) (5 : Fin 25) = (118 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_6 : coordinate (pairIndex (8 : Fin 25) (6 : Fin 25)) = (min 8 6, max 8 6) := by
  have hidx : pairIndex (8 : Fin 25) (6 : Fin 25) = (137 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_7 : coordinate (pairIndex (8 : Fin 25) (7 : Fin 25)) = (min 8 7, max 8 7) := by
  have hidx : pairIndex (8 : Fin 25) (7 : Fin 25) = (155 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_8 : coordinate (pairIndex (8 : Fin 25) (8 : Fin 25)) = (min 8 8, max 8 8) := by
  have hidx : pairIndex (8 : Fin 25) (8 : Fin 25) = (172 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_9 : coordinate (pairIndex (8 : Fin 25) (9 : Fin 25)) = (min 8 9, max 8 9) := by
  have hidx : pairIndex (8 : Fin 25) (9 : Fin 25) = (173 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_10 : coordinate (pairIndex (8 : Fin 25) (10 : Fin 25)) = (min 8 10, max 8 10) := by
  have hidx : pairIndex (8 : Fin 25) (10 : Fin 25) = (174 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_11 : coordinate (pairIndex (8 : Fin 25) (11 : Fin 25)) = (min 8 11, max 8 11) := by
  have hidx : pairIndex (8 : Fin 25) (11 : Fin 25) = (175 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_12 : coordinate (pairIndex (8 : Fin 25) (12 : Fin 25)) = (min 8 12, max 8 12) := by
  have hidx : pairIndex (8 : Fin 25) (12 : Fin 25) = (176 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_13 : coordinate (pairIndex (8 : Fin 25) (13 : Fin 25)) = (min 8 13, max 8 13) := by
  have hidx : pairIndex (8 : Fin 25) (13 : Fin 25) = (177 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_14 : coordinate (pairIndex (8 : Fin 25) (14 : Fin 25)) = (min 8 14, max 8 14) := by
  have hidx : pairIndex (8 : Fin 25) (14 : Fin 25) = (178 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_15 : coordinate (pairIndex (8 : Fin 25) (15 : Fin 25)) = (min 8 15, max 8 15) := by
  have hidx : pairIndex (8 : Fin 25) (15 : Fin 25) = (179 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_16 : coordinate (pairIndex (8 : Fin 25) (16 : Fin 25)) = (min 8 16, max 8 16) := by
  have hidx : pairIndex (8 : Fin 25) (16 : Fin 25) = (180 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_17 : coordinate (pairIndex (8 : Fin 25) (17 : Fin 25)) = (min 8 17, max 8 17) := by
  have hidx : pairIndex (8 : Fin 25) (17 : Fin 25) = (181 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_18 : coordinate (pairIndex (8 : Fin 25) (18 : Fin 25)) = (min 8 18, max 8 18) := by
  have hidx : pairIndex (8 : Fin 25) (18 : Fin 25) = (182 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_19 : coordinate (pairIndex (8 : Fin 25) (19 : Fin 25)) = (min 8 19, max 8 19) := by
  have hidx : pairIndex (8 : Fin 25) (19 : Fin 25) = (183 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_20 : coordinate (pairIndex (8 : Fin 25) (20 : Fin 25)) = (min 8 20, max 8 20) := by
  have hidx : pairIndex (8 : Fin 25) (20 : Fin 25) = (184 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_21 : coordinate (pairIndex (8 : Fin 25) (21 : Fin 25)) = (min 8 21, max 8 21) := by
  have hidx : pairIndex (8 : Fin 25) (21 : Fin 25) = (185 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_22 : coordinate (pairIndex (8 : Fin 25) (22 : Fin 25)) = (min 8 22, max 8 22) := by
  have hidx : pairIndex (8 : Fin 25) (22 : Fin 25) = (186 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_23 : coordinate (pairIndex (8 : Fin 25) (23 : Fin 25)) = (min 8 23, max 8 23) := by
  have hidx : pairIndex (8 : Fin 25) (23 : Fin 25) = (187 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_8_24 : coordinate (pairIndex (8 : Fin 25) (24 : Fin 25)) = (min 8 24, max 8 24) := by
  have hidx : pairIndex (8 : Fin 25) (24 : Fin 25) = (188 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_0 : coordinate (pairIndex (9 : Fin 25) (0 : Fin 25)) = (min 9 0, max 9 0) := by
  have hidx : pairIndex (9 : Fin 25) (0 : Fin 25) = (9 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_1 : coordinate (pairIndex (9 : Fin 25) (1 : Fin 25)) = (min 9 1, max 9 1) := by
  have hidx : pairIndex (9 : Fin 25) (1 : Fin 25) = (33 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_2 : coordinate (pairIndex (9 : Fin 25) (2 : Fin 25)) = (min 9 2, max 9 2) := by
  have hidx : pairIndex (9 : Fin 25) (2 : Fin 25) = (56 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_3 : coordinate (pairIndex (9 : Fin 25) (3 : Fin 25)) = (min 9 3, max 9 3) := by
  have hidx : pairIndex (9 : Fin 25) (3 : Fin 25) = (78 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_4 : coordinate (pairIndex (9 : Fin 25) (4 : Fin 25)) = (min 9 4, max 9 4) := by
  have hidx : pairIndex (9 : Fin 25) (4 : Fin 25) = (99 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_5 : coordinate (pairIndex (9 : Fin 25) (5 : Fin 25)) = (min 9 5, max 9 5) := by
  have hidx : pairIndex (9 : Fin 25) (5 : Fin 25) = (119 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_6 : coordinate (pairIndex (9 : Fin 25) (6 : Fin 25)) = (min 9 6, max 9 6) := by
  have hidx : pairIndex (9 : Fin 25) (6 : Fin 25) = (138 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_7 : coordinate (pairIndex (9 : Fin 25) (7 : Fin 25)) = (min 9 7, max 9 7) := by
  have hidx : pairIndex (9 : Fin 25) (7 : Fin 25) = (156 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_8 : coordinate (pairIndex (9 : Fin 25) (8 : Fin 25)) = (min 9 8, max 9 8) := by
  have hidx : pairIndex (9 : Fin 25) (8 : Fin 25) = (173 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_9 : coordinate (pairIndex (9 : Fin 25) (9 : Fin 25)) = (min 9 9, max 9 9) := by
  have hidx : pairIndex (9 : Fin 25) (9 : Fin 25) = (189 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_10 : coordinate (pairIndex (9 : Fin 25) (10 : Fin 25)) = (min 9 10, max 9 10) := by
  have hidx : pairIndex (9 : Fin 25) (10 : Fin 25) = (190 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_11 : coordinate (pairIndex (9 : Fin 25) (11 : Fin 25)) = (min 9 11, max 9 11) := by
  have hidx : pairIndex (9 : Fin 25) (11 : Fin 25) = (191 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_12 : coordinate (pairIndex (9 : Fin 25) (12 : Fin 25)) = (min 9 12, max 9 12) := by
  have hidx : pairIndex (9 : Fin 25) (12 : Fin 25) = (192 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_13 : coordinate (pairIndex (9 : Fin 25) (13 : Fin 25)) = (min 9 13, max 9 13) := by
  have hidx : pairIndex (9 : Fin 25) (13 : Fin 25) = (193 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_14 : coordinate (pairIndex (9 : Fin 25) (14 : Fin 25)) = (min 9 14, max 9 14) := by
  have hidx : pairIndex (9 : Fin 25) (14 : Fin 25) = (194 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_15 : coordinate (pairIndex (9 : Fin 25) (15 : Fin 25)) = (min 9 15, max 9 15) := by
  have hidx : pairIndex (9 : Fin 25) (15 : Fin 25) = (195 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_16 : coordinate (pairIndex (9 : Fin 25) (16 : Fin 25)) = (min 9 16, max 9 16) := by
  have hidx : pairIndex (9 : Fin 25) (16 : Fin 25) = (196 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_17 : coordinate (pairIndex (9 : Fin 25) (17 : Fin 25)) = (min 9 17, max 9 17) := by
  have hidx : pairIndex (9 : Fin 25) (17 : Fin 25) = (197 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_18 : coordinate (pairIndex (9 : Fin 25) (18 : Fin 25)) = (min 9 18, max 9 18) := by
  have hidx : pairIndex (9 : Fin 25) (18 : Fin 25) = (198 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_19 : coordinate (pairIndex (9 : Fin 25) (19 : Fin 25)) = (min 9 19, max 9 19) := by
  have hidx : pairIndex (9 : Fin 25) (19 : Fin 25) = (199 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_20 : coordinate (pairIndex (9 : Fin 25) (20 : Fin 25)) = (min 9 20, max 9 20) := by
  have hidx : pairIndex (9 : Fin 25) (20 : Fin 25) = (200 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_21 : coordinate (pairIndex (9 : Fin 25) (21 : Fin 25)) = (min 9 21, max 9 21) := by
  have hidx : pairIndex (9 : Fin 25) (21 : Fin 25) = (201 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_22 : coordinate (pairIndex (9 : Fin 25) (22 : Fin 25)) = (min 9 22, max 9 22) := by
  have hidx : pairIndex (9 : Fin 25) (22 : Fin 25) = (202 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_23 : coordinate (pairIndex (9 : Fin 25) (23 : Fin 25)) = (min 9 23, max 9 23) := by
  have hidx : pairIndex (9 : Fin 25) (23 : Fin 25) = (203 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_9_24 : coordinate (pairIndex (9 : Fin 25) (24 : Fin 25)) = (min 9 24, max 9 24) := by
  have hidx : pairIndex (9 : Fin 25) (24 : Fin 25) = (204 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_0 : coordinate (pairIndex (10 : Fin 25) (0 : Fin 25)) = (min 10 0, max 10 0) := by
  have hidx : pairIndex (10 : Fin 25) (0 : Fin 25) = (10 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_1 : coordinate (pairIndex (10 : Fin 25) (1 : Fin 25)) = (min 10 1, max 10 1) := by
  have hidx : pairIndex (10 : Fin 25) (1 : Fin 25) = (34 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_2 : coordinate (pairIndex (10 : Fin 25) (2 : Fin 25)) = (min 10 2, max 10 2) := by
  have hidx : pairIndex (10 : Fin 25) (2 : Fin 25) = (57 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_3 : coordinate (pairIndex (10 : Fin 25) (3 : Fin 25)) = (min 10 3, max 10 3) := by
  have hidx : pairIndex (10 : Fin 25) (3 : Fin 25) = (79 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_4 : coordinate (pairIndex (10 : Fin 25) (4 : Fin 25)) = (min 10 4, max 10 4) := by
  have hidx : pairIndex (10 : Fin 25) (4 : Fin 25) = (100 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_5 : coordinate (pairIndex (10 : Fin 25) (5 : Fin 25)) = (min 10 5, max 10 5) := by
  have hidx : pairIndex (10 : Fin 25) (5 : Fin 25) = (120 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_6 : coordinate (pairIndex (10 : Fin 25) (6 : Fin 25)) = (min 10 6, max 10 6) := by
  have hidx : pairIndex (10 : Fin 25) (6 : Fin 25) = (139 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_7 : coordinate (pairIndex (10 : Fin 25) (7 : Fin 25)) = (min 10 7, max 10 7) := by
  have hidx : pairIndex (10 : Fin 25) (7 : Fin 25) = (157 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_8 : coordinate (pairIndex (10 : Fin 25) (8 : Fin 25)) = (min 10 8, max 10 8) := by
  have hidx : pairIndex (10 : Fin 25) (8 : Fin 25) = (174 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_9 : coordinate (pairIndex (10 : Fin 25) (9 : Fin 25)) = (min 10 9, max 10 9) := by
  have hidx : pairIndex (10 : Fin 25) (9 : Fin 25) = (190 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_10 : coordinate (pairIndex (10 : Fin 25) (10 : Fin 25)) = (min 10 10, max 10 10) := by
  have hidx : pairIndex (10 : Fin 25) (10 : Fin 25) = (205 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_11 : coordinate (pairIndex (10 : Fin 25) (11 : Fin 25)) = (min 10 11, max 10 11) := by
  have hidx : pairIndex (10 : Fin 25) (11 : Fin 25) = (206 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_12 : coordinate (pairIndex (10 : Fin 25) (12 : Fin 25)) = (min 10 12, max 10 12) := by
  have hidx : pairIndex (10 : Fin 25) (12 : Fin 25) = (207 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_13 : coordinate (pairIndex (10 : Fin 25) (13 : Fin 25)) = (min 10 13, max 10 13) := by
  have hidx : pairIndex (10 : Fin 25) (13 : Fin 25) = (208 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_14 : coordinate (pairIndex (10 : Fin 25) (14 : Fin 25)) = (min 10 14, max 10 14) := by
  have hidx : pairIndex (10 : Fin 25) (14 : Fin 25) = (209 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_15 : coordinate (pairIndex (10 : Fin 25) (15 : Fin 25)) = (min 10 15, max 10 15) := by
  have hidx : pairIndex (10 : Fin 25) (15 : Fin 25) = (210 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_16 : coordinate (pairIndex (10 : Fin 25) (16 : Fin 25)) = (min 10 16, max 10 16) := by
  have hidx : pairIndex (10 : Fin 25) (16 : Fin 25) = (211 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_17 : coordinate (pairIndex (10 : Fin 25) (17 : Fin 25)) = (min 10 17, max 10 17) := by
  have hidx : pairIndex (10 : Fin 25) (17 : Fin 25) = (212 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_18 : coordinate (pairIndex (10 : Fin 25) (18 : Fin 25)) = (min 10 18, max 10 18) := by
  have hidx : pairIndex (10 : Fin 25) (18 : Fin 25) = (213 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_19 : coordinate (pairIndex (10 : Fin 25) (19 : Fin 25)) = (min 10 19, max 10 19) := by
  have hidx : pairIndex (10 : Fin 25) (19 : Fin 25) = (214 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_20 : coordinate (pairIndex (10 : Fin 25) (20 : Fin 25)) = (min 10 20, max 10 20) := by
  have hidx : pairIndex (10 : Fin 25) (20 : Fin 25) = (215 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_21 : coordinate (pairIndex (10 : Fin 25) (21 : Fin 25)) = (min 10 21, max 10 21) := by
  have hidx : pairIndex (10 : Fin 25) (21 : Fin 25) = (216 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_22 : coordinate (pairIndex (10 : Fin 25) (22 : Fin 25)) = (min 10 22, max 10 22) := by
  have hidx : pairIndex (10 : Fin 25) (22 : Fin 25) = (217 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_23 : coordinate (pairIndex (10 : Fin 25) (23 : Fin 25)) = (min 10 23, max 10 23) := by
  have hidx : pairIndex (10 : Fin 25) (23 : Fin 25) = (218 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_10_24 : coordinate (pairIndex (10 : Fin 25) (24 : Fin 25)) = (min 10 24, max 10 24) := by
  have hidx : pairIndex (10 : Fin 25) (24 : Fin 25) = (219 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_0 : coordinate (pairIndex (11 : Fin 25) (0 : Fin 25)) = (min 11 0, max 11 0) := by
  have hidx : pairIndex (11 : Fin 25) (0 : Fin 25) = (11 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_1 : coordinate (pairIndex (11 : Fin 25) (1 : Fin 25)) = (min 11 1, max 11 1) := by
  have hidx : pairIndex (11 : Fin 25) (1 : Fin 25) = (35 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_2 : coordinate (pairIndex (11 : Fin 25) (2 : Fin 25)) = (min 11 2, max 11 2) := by
  have hidx : pairIndex (11 : Fin 25) (2 : Fin 25) = (58 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_3 : coordinate (pairIndex (11 : Fin 25) (3 : Fin 25)) = (min 11 3, max 11 3) := by
  have hidx : pairIndex (11 : Fin 25) (3 : Fin 25) = (80 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_4 : coordinate (pairIndex (11 : Fin 25) (4 : Fin 25)) = (min 11 4, max 11 4) := by
  have hidx : pairIndex (11 : Fin 25) (4 : Fin 25) = (101 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_5 : coordinate (pairIndex (11 : Fin 25) (5 : Fin 25)) = (min 11 5, max 11 5) := by
  have hidx : pairIndex (11 : Fin 25) (5 : Fin 25) = (121 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_6 : coordinate (pairIndex (11 : Fin 25) (6 : Fin 25)) = (min 11 6, max 11 6) := by
  have hidx : pairIndex (11 : Fin 25) (6 : Fin 25) = (140 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_7 : coordinate (pairIndex (11 : Fin 25) (7 : Fin 25)) = (min 11 7, max 11 7) := by
  have hidx : pairIndex (11 : Fin 25) (7 : Fin 25) = (158 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_8 : coordinate (pairIndex (11 : Fin 25) (8 : Fin 25)) = (min 11 8, max 11 8) := by
  have hidx : pairIndex (11 : Fin 25) (8 : Fin 25) = (175 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_9 : coordinate (pairIndex (11 : Fin 25) (9 : Fin 25)) = (min 11 9, max 11 9) := by
  have hidx : pairIndex (11 : Fin 25) (9 : Fin 25) = (191 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_10 : coordinate (pairIndex (11 : Fin 25) (10 : Fin 25)) = (min 11 10, max 11 10) := by
  have hidx : pairIndex (11 : Fin 25) (10 : Fin 25) = (206 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_11 : coordinate (pairIndex (11 : Fin 25) (11 : Fin 25)) = (min 11 11, max 11 11) := by
  have hidx : pairIndex (11 : Fin 25) (11 : Fin 25) = (220 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_12 : coordinate (pairIndex (11 : Fin 25) (12 : Fin 25)) = (min 11 12, max 11 12) := by
  have hidx : pairIndex (11 : Fin 25) (12 : Fin 25) = (221 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_13 : coordinate (pairIndex (11 : Fin 25) (13 : Fin 25)) = (min 11 13, max 11 13) := by
  have hidx : pairIndex (11 : Fin 25) (13 : Fin 25) = (222 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_14 : coordinate (pairIndex (11 : Fin 25) (14 : Fin 25)) = (min 11 14, max 11 14) := by
  have hidx : pairIndex (11 : Fin 25) (14 : Fin 25) = (223 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_15 : coordinate (pairIndex (11 : Fin 25) (15 : Fin 25)) = (min 11 15, max 11 15) := by
  have hidx : pairIndex (11 : Fin 25) (15 : Fin 25) = (224 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_16 : coordinate (pairIndex (11 : Fin 25) (16 : Fin 25)) = (min 11 16, max 11 16) := by
  have hidx : pairIndex (11 : Fin 25) (16 : Fin 25) = (225 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_17 : coordinate (pairIndex (11 : Fin 25) (17 : Fin 25)) = (min 11 17, max 11 17) := by
  have hidx : pairIndex (11 : Fin 25) (17 : Fin 25) = (226 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_18 : coordinate (pairIndex (11 : Fin 25) (18 : Fin 25)) = (min 11 18, max 11 18) := by
  have hidx : pairIndex (11 : Fin 25) (18 : Fin 25) = (227 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_19 : coordinate (pairIndex (11 : Fin 25) (19 : Fin 25)) = (min 11 19, max 11 19) := by
  have hidx : pairIndex (11 : Fin 25) (19 : Fin 25) = (228 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_20 : coordinate (pairIndex (11 : Fin 25) (20 : Fin 25)) = (min 11 20, max 11 20) := by
  have hidx : pairIndex (11 : Fin 25) (20 : Fin 25) = (229 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_21 : coordinate (pairIndex (11 : Fin 25) (21 : Fin 25)) = (min 11 21, max 11 21) := by
  have hidx : pairIndex (11 : Fin 25) (21 : Fin 25) = (230 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_22 : coordinate (pairIndex (11 : Fin 25) (22 : Fin 25)) = (min 11 22, max 11 22) := by
  have hidx : pairIndex (11 : Fin 25) (22 : Fin 25) = (231 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_23 : coordinate (pairIndex (11 : Fin 25) (23 : Fin 25)) = (min 11 23, max 11 23) := by
  have hidx : pairIndex (11 : Fin 25) (23 : Fin 25) = (232 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_11_24 : coordinate (pairIndex (11 : Fin 25) (24 : Fin 25)) = (min 11 24, max 11 24) := by
  have hidx : pairIndex (11 : Fin 25) (24 : Fin 25) = (233 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_0 : coordinate (pairIndex (12 : Fin 25) (0 : Fin 25)) = (min 12 0, max 12 0) := by
  have hidx : pairIndex (12 : Fin 25) (0 : Fin 25) = (12 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_1 : coordinate (pairIndex (12 : Fin 25) (1 : Fin 25)) = (min 12 1, max 12 1) := by
  have hidx : pairIndex (12 : Fin 25) (1 : Fin 25) = (36 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_2 : coordinate (pairIndex (12 : Fin 25) (2 : Fin 25)) = (min 12 2, max 12 2) := by
  have hidx : pairIndex (12 : Fin 25) (2 : Fin 25) = (59 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_3 : coordinate (pairIndex (12 : Fin 25) (3 : Fin 25)) = (min 12 3, max 12 3) := by
  have hidx : pairIndex (12 : Fin 25) (3 : Fin 25) = (81 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_4 : coordinate (pairIndex (12 : Fin 25) (4 : Fin 25)) = (min 12 4, max 12 4) := by
  have hidx : pairIndex (12 : Fin 25) (4 : Fin 25) = (102 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_5 : coordinate (pairIndex (12 : Fin 25) (5 : Fin 25)) = (min 12 5, max 12 5) := by
  have hidx : pairIndex (12 : Fin 25) (5 : Fin 25) = (122 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_6 : coordinate (pairIndex (12 : Fin 25) (6 : Fin 25)) = (min 12 6, max 12 6) := by
  have hidx : pairIndex (12 : Fin 25) (6 : Fin 25) = (141 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_7 : coordinate (pairIndex (12 : Fin 25) (7 : Fin 25)) = (min 12 7, max 12 7) := by
  have hidx : pairIndex (12 : Fin 25) (7 : Fin 25) = (159 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_8 : coordinate (pairIndex (12 : Fin 25) (8 : Fin 25)) = (min 12 8, max 12 8) := by
  have hidx : pairIndex (12 : Fin 25) (8 : Fin 25) = (176 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_9 : coordinate (pairIndex (12 : Fin 25) (9 : Fin 25)) = (min 12 9, max 12 9) := by
  have hidx : pairIndex (12 : Fin 25) (9 : Fin 25) = (192 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_10 : coordinate (pairIndex (12 : Fin 25) (10 : Fin 25)) = (min 12 10, max 12 10) := by
  have hidx : pairIndex (12 : Fin 25) (10 : Fin 25) = (207 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_11 : coordinate (pairIndex (12 : Fin 25) (11 : Fin 25)) = (min 12 11, max 12 11) := by
  have hidx : pairIndex (12 : Fin 25) (11 : Fin 25) = (221 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_12 : coordinate (pairIndex (12 : Fin 25) (12 : Fin 25)) = (min 12 12, max 12 12) := by
  have hidx : pairIndex (12 : Fin 25) (12 : Fin 25) = (234 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_13 : coordinate (pairIndex (12 : Fin 25) (13 : Fin 25)) = (min 12 13, max 12 13) := by
  have hidx : pairIndex (12 : Fin 25) (13 : Fin 25) = (235 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_14 : coordinate (pairIndex (12 : Fin 25) (14 : Fin 25)) = (min 12 14, max 12 14) := by
  have hidx : pairIndex (12 : Fin 25) (14 : Fin 25) = (236 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_15 : coordinate (pairIndex (12 : Fin 25) (15 : Fin 25)) = (min 12 15, max 12 15) := by
  have hidx : pairIndex (12 : Fin 25) (15 : Fin 25) = (237 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_16 : coordinate (pairIndex (12 : Fin 25) (16 : Fin 25)) = (min 12 16, max 12 16) := by
  have hidx : pairIndex (12 : Fin 25) (16 : Fin 25) = (238 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_17 : coordinate (pairIndex (12 : Fin 25) (17 : Fin 25)) = (min 12 17, max 12 17) := by
  have hidx : pairIndex (12 : Fin 25) (17 : Fin 25) = (239 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_18 : coordinate (pairIndex (12 : Fin 25) (18 : Fin 25)) = (min 12 18, max 12 18) := by
  have hidx : pairIndex (12 : Fin 25) (18 : Fin 25) = (240 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_19 : coordinate (pairIndex (12 : Fin 25) (19 : Fin 25)) = (min 12 19, max 12 19) := by
  have hidx : pairIndex (12 : Fin 25) (19 : Fin 25) = (241 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_20 : coordinate (pairIndex (12 : Fin 25) (20 : Fin 25)) = (min 12 20, max 12 20) := by
  have hidx : pairIndex (12 : Fin 25) (20 : Fin 25) = (242 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_21 : coordinate (pairIndex (12 : Fin 25) (21 : Fin 25)) = (min 12 21, max 12 21) := by
  have hidx : pairIndex (12 : Fin 25) (21 : Fin 25) = (243 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_22 : coordinate (pairIndex (12 : Fin 25) (22 : Fin 25)) = (min 12 22, max 12 22) := by
  have hidx : pairIndex (12 : Fin 25) (22 : Fin 25) = (244 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_23 : coordinate (pairIndex (12 : Fin 25) (23 : Fin 25)) = (min 12 23, max 12 23) := by
  have hidx : pairIndex (12 : Fin 25) (23 : Fin 25) = (245 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_12_24 : coordinate (pairIndex (12 : Fin 25) (24 : Fin 25)) = (min 12 24, max 12 24) := by
  have hidx : pairIndex (12 : Fin 25) (24 : Fin 25) = (246 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_0 : coordinate (pairIndex (13 : Fin 25) (0 : Fin 25)) = (min 13 0, max 13 0) := by
  have hidx : pairIndex (13 : Fin 25) (0 : Fin 25) = (13 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_1 : coordinate (pairIndex (13 : Fin 25) (1 : Fin 25)) = (min 13 1, max 13 1) := by
  have hidx : pairIndex (13 : Fin 25) (1 : Fin 25) = (37 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_2 : coordinate (pairIndex (13 : Fin 25) (2 : Fin 25)) = (min 13 2, max 13 2) := by
  have hidx : pairIndex (13 : Fin 25) (2 : Fin 25) = (60 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_3 : coordinate (pairIndex (13 : Fin 25) (3 : Fin 25)) = (min 13 3, max 13 3) := by
  have hidx : pairIndex (13 : Fin 25) (3 : Fin 25) = (82 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_4 : coordinate (pairIndex (13 : Fin 25) (4 : Fin 25)) = (min 13 4, max 13 4) := by
  have hidx : pairIndex (13 : Fin 25) (4 : Fin 25) = (103 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_5 : coordinate (pairIndex (13 : Fin 25) (5 : Fin 25)) = (min 13 5, max 13 5) := by
  have hidx : pairIndex (13 : Fin 25) (5 : Fin 25) = (123 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_6 : coordinate (pairIndex (13 : Fin 25) (6 : Fin 25)) = (min 13 6, max 13 6) := by
  have hidx : pairIndex (13 : Fin 25) (6 : Fin 25) = (142 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_7 : coordinate (pairIndex (13 : Fin 25) (7 : Fin 25)) = (min 13 7, max 13 7) := by
  have hidx : pairIndex (13 : Fin 25) (7 : Fin 25) = (160 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_8 : coordinate (pairIndex (13 : Fin 25) (8 : Fin 25)) = (min 13 8, max 13 8) := by
  have hidx : pairIndex (13 : Fin 25) (8 : Fin 25) = (177 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_9 : coordinate (pairIndex (13 : Fin 25) (9 : Fin 25)) = (min 13 9, max 13 9) := by
  have hidx : pairIndex (13 : Fin 25) (9 : Fin 25) = (193 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_10 : coordinate (pairIndex (13 : Fin 25) (10 : Fin 25)) = (min 13 10, max 13 10) := by
  have hidx : pairIndex (13 : Fin 25) (10 : Fin 25) = (208 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_11 : coordinate (pairIndex (13 : Fin 25) (11 : Fin 25)) = (min 13 11, max 13 11) := by
  have hidx : pairIndex (13 : Fin 25) (11 : Fin 25) = (222 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_12 : coordinate (pairIndex (13 : Fin 25) (12 : Fin 25)) = (min 13 12, max 13 12) := by
  have hidx : pairIndex (13 : Fin 25) (12 : Fin 25) = (235 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_13 : coordinate (pairIndex (13 : Fin 25) (13 : Fin 25)) = (min 13 13, max 13 13) := by
  have hidx : pairIndex (13 : Fin 25) (13 : Fin 25) = (247 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_14 : coordinate (pairIndex (13 : Fin 25) (14 : Fin 25)) = (min 13 14, max 13 14) := by
  have hidx : pairIndex (13 : Fin 25) (14 : Fin 25) = (248 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_15 : coordinate (pairIndex (13 : Fin 25) (15 : Fin 25)) = (min 13 15, max 13 15) := by
  have hidx : pairIndex (13 : Fin 25) (15 : Fin 25) = (249 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_16 : coordinate (pairIndex (13 : Fin 25) (16 : Fin 25)) = (min 13 16, max 13 16) := by
  have hidx : pairIndex (13 : Fin 25) (16 : Fin 25) = (250 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_17 : coordinate (pairIndex (13 : Fin 25) (17 : Fin 25)) = (min 13 17, max 13 17) := by
  have hidx : pairIndex (13 : Fin 25) (17 : Fin 25) = (251 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_18 : coordinate (pairIndex (13 : Fin 25) (18 : Fin 25)) = (min 13 18, max 13 18) := by
  have hidx : pairIndex (13 : Fin 25) (18 : Fin 25) = (252 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_19 : coordinate (pairIndex (13 : Fin 25) (19 : Fin 25)) = (min 13 19, max 13 19) := by
  have hidx : pairIndex (13 : Fin 25) (19 : Fin 25) = (253 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_20 : coordinate (pairIndex (13 : Fin 25) (20 : Fin 25)) = (min 13 20, max 13 20) := by
  have hidx : pairIndex (13 : Fin 25) (20 : Fin 25) = (254 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_21 : coordinate (pairIndex (13 : Fin 25) (21 : Fin 25)) = (min 13 21, max 13 21) := by
  have hidx : pairIndex (13 : Fin 25) (21 : Fin 25) = (255 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_22 : coordinate (pairIndex (13 : Fin 25) (22 : Fin 25)) = (min 13 22, max 13 22) := by
  have hidx : pairIndex (13 : Fin 25) (22 : Fin 25) = (256 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_23 : coordinate (pairIndex (13 : Fin 25) (23 : Fin 25)) = (min 13 23, max 13 23) := by
  have hidx : pairIndex (13 : Fin 25) (23 : Fin 25) = (257 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_13_24 : coordinate (pairIndex (13 : Fin 25) (24 : Fin 25)) = (min 13 24, max 13 24) := by
  have hidx : pairIndex (13 : Fin 25) (24 : Fin 25) = (258 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_0 : coordinate (pairIndex (14 : Fin 25) (0 : Fin 25)) = (min 14 0, max 14 0) := by
  have hidx : pairIndex (14 : Fin 25) (0 : Fin 25) = (14 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_1 : coordinate (pairIndex (14 : Fin 25) (1 : Fin 25)) = (min 14 1, max 14 1) := by
  have hidx : pairIndex (14 : Fin 25) (1 : Fin 25) = (38 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_2 : coordinate (pairIndex (14 : Fin 25) (2 : Fin 25)) = (min 14 2, max 14 2) := by
  have hidx : pairIndex (14 : Fin 25) (2 : Fin 25) = (61 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_3 : coordinate (pairIndex (14 : Fin 25) (3 : Fin 25)) = (min 14 3, max 14 3) := by
  have hidx : pairIndex (14 : Fin 25) (3 : Fin 25) = (83 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_4 : coordinate (pairIndex (14 : Fin 25) (4 : Fin 25)) = (min 14 4, max 14 4) := by
  have hidx : pairIndex (14 : Fin 25) (4 : Fin 25) = (104 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_5 : coordinate (pairIndex (14 : Fin 25) (5 : Fin 25)) = (min 14 5, max 14 5) := by
  have hidx : pairIndex (14 : Fin 25) (5 : Fin 25) = (124 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_6 : coordinate (pairIndex (14 : Fin 25) (6 : Fin 25)) = (min 14 6, max 14 6) := by
  have hidx : pairIndex (14 : Fin 25) (6 : Fin 25) = (143 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_7 : coordinate (pairIndex (14 : Fin 25) (7 : Fin 25)) = (min 14 7, max 14 7) := by
  have hidx : pairIndex (14 : Fin 25) (7 : Fin 25) = (161 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_8 : coordinate (pairIndex (14 : Fin 25) (8 : Fin 25)) = (min 14 8, max 14 8) := by
  have hidx : pairIndex (14 : Fin 25) (8 : Fin 25) = (178 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_9 : coordinate (pairIndex (14 : Fin 25) (9 : Fin 25)) = (min 14 9, max 14 9) := by
  have hidx : pairIndex (14 : Fin 25) (9 : Fin 25) = (194 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_10 : coordinate (pairIndex (14 : Fin 25) (10 : Fin 25)) = (min 14 10, max 14 10) := by
  have hidx : pairIndex (14 : Fin 25) (10 : Fin 25) = (209 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_11 : coordinate (pairIndex (14 : Fin 25) (11 : Fin 25)) = (min 14 11, max 14 11) := by
  have hidx : pairIndex (14 : Fin 25) (11 : Fin 25) = (223 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_12 : coordinate (pairIndex (14 : Fin 25) (12 : Fin 25)) = (min 14 12, max 14 12) := by
  have hidx : pairIndex (14 : Fin 25) (12 : Fin 25) = (236 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_13 : coordinate (pairIndex (14 : Fin 25) (13 : Fin 25)) = (min 14 13, max 14 13) := by
  have hidx : pairIndex (14 : Fin 25) (13 : Fin 25) = (248 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_14 : coordinate (pairIndex (14 : Fin 25) (14 : Fin 25)) = (min 14 14, max 14 14) := by
  have hidx : pairIndex (14 : Fin 25) (14 : Fin 25) = (259 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_15 : coordinate (pairIndex (14 : Fin 25) (15 : Fin 25)) = (min 14 15, max 14 15) := by
  have hidx : pairIndex (14 : Fin 25) (15 : Fin 25) = (260 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_16 : coordinate (pairIndex (14 : Fin 25) (16 : Fin 25)) = (min 14 16, max 14 16) := by
  have hidx : pairIndex (14 : Fin 25) (16 : Fin 25) = (261 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_17 : coordinate (pairIndex (14 : Fin 25) (17 : Fin 25)) = (min 14 17, max 14 17) := by
  have hidx : pairIndex (14 : Fin 25) (17 : Fin 25) = (262 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_18 : coordinate (pairIndex (14 : Fin 25) (18 : Fin 25)) = (min 14 18, max 14 18) := by
  have hidx : pairIndex (14 : Fin 25) (18 : Fin 25) = (263 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_19 : coordinate (pairIndex (14 : Fin 25) (19 : Fin 25)) = (min 14 19, max 14 19) := by
  have hidx : pairIndex (14 : Fin 25) (19 : Fin 25) = (264 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_20 : coordinate (pairIndex (14 : Fin 25) (20 : Fin 25)) = (min 14 20, max 14 20) := by
  have hidx : pairIndex (14 : Fin 25) (20 : Fin 25) = (265 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_21 : coordinate (pairIndex (14 : Fin 25) (21 : Fin 25)) = (min 14 21, max 14 21) := by
  have hidx : pairIndex (14 : Fin 25) (21 : Fin 25) = (266 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_22 : coordinate (pairIndex (14 : Fin 25) (22 : Fin 25)) = (min 14 22, max 14 22) := by
  have hidx : pairIndex (14 : Fin 25) (22 : Fin 25) = (267 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_23 : coordinate (pairIndex (14 : Fin 25) (23 : Fin 25)) = (min 14 23, max 14 23) := by
  have hidx : pairIndex (14 : Fin 25) (23 : Fin 25) = (268 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_14_24 : coordinate (pairIndex (14 : Fin 25) (24 : Fin 25)) = (min 14 24, max 14 24) := by
  have hidx : pairIndex (14 : Fin 25) (24 : Fin 25) = (269 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_0 : coordinate (pairIndex (15 : Fin 25) (0 : Fin 25)) = (min 15 0, max 15 0) := by
  have hidx : pairIndex (15 : Fin 25) (0 : Fin 25) = (15 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_1 : coordinate (pairIndex (15 : Fin 25) (1 : Fin 25)) = (min 15 1, max 15 1) := by
  have hidx : pairIndex (15 : Fin 25) (1 : Fin 25) = (39 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_2 : coordinate (pairIndex (15 : Fin 25) (2 : Fin 25)) = (min 15 2, max 15 2) := by
  have hidx : pairIndex (15 : Fin 25) (2 : Fin 25) = (62 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_3 : coordinate (pairIndex (15 : Fin 25) (3 : Fin 25)) = (min 15 3, max 15 3) := by
  have hidx : pairIndex (15 : Fin 25) (3 : Fin 25) = (84 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_4 : coordinate (pairIndex (15 : Fin 25) (4 : Fin 25)) = (min 15 4, max 15 4) := by
  have hidx : pairIndex (15 : Fin 25) (4 : Fin 25) = (105 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_5 : coordinate (pairIndex (15 : Fin 25) (5 : Fin 25)) = (min 15 5, max 15 5) := by
  have hidx : pairIndex (15 : Fin 25) (5 : Fin 25) = (125 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_6 : coordinate (pairIndex (15 : Fin 25) (6 : Fin 25)) = (min 15 6, max 15 6) := by
  have hidx : pairIndex (15 : Fin 25) (6 : Fin 25) = (144 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_7 : coordinate (pairIndex (15 : Fin 25) (7 : Fin 25)) = (min 15 7, max 15 7) := by
  have hidx : pairIndex (15 : Fin 25) (7 : Fin 25) = (162 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_8 : coordinate (pairIndex (15 : Fin 25) (8 : Fin 25)) = (min 15 8, max 15 8) := by
  have hidx : pairIndex (15 : Fin 25) (8 : Fin 25) = (179 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_9 : coordinate (pairIndex (15 : Fin 25) (9 : Fin 25)) = (min 15 9, max 15 9) := by
  have hidx : pairIndex (15 : Fin 25) (9 : Fin 25) = (195 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_10 : coordinate (pairIndex (15 : Fin 25) (10 : Fin 25)) = (min 15 10, max 15 10) := by
  have hidx : pairIndex (15 : Fin 25) (10 : Fin 25) = (210 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_11 : coordinate (pairIndex (15 : Fin 25) (11 : Fin 25)) = (min 15 11, max 15 11) := by
  have hidx : pairIndex (15 : Fin 25) (11 : Fin 25) = (224 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_12 : coordinate (pairIndex (15 : Fin 25) (12 : Fin 25)) = (min 15 12, max 15 12) := by
  have hidx : pairIndex (15 : Fin 25) (12 : Fin 25) = (237 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_13 : coordinate (pairIndex (15 : Fin 25) (13 : Fin 25)) = (min 15 13, max 15 13) := by
  have hidx : pairIndex (15 : Fin 25) (13 : Fin 25) = (249 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_14 : coordinate (pairIndex (15 : Fin 25) (14 : Fin 25)) = (min 15 14, max 15 14) := by
  have hidx : pairIndex (15 : Fin 25) (14 : Fin 25) = (260 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_15 : coordinate (pairIndex (15 : Fin 25) (15 : Fin 25)) = (min 15 15, max 15 15) := by
  have hidx : pairIndex (15 : Fin 25) (15 : Fin 25) = (270 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_16 : coordinate (pairIndex (15 : Fin 25) (16 : Fin 25)) = (min 15 16, max 15 16) := by
  have hidx : pairIndex (15 : Fin 25) (16 : Fin 25) = (271 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_17 : coordinate (pairIndex (15 : Fin 25) (17 : Fin 25)) = (min 15 17, max 15 17) := by
  have hidx : pairIndex (15 : Fin 25) (17 : Fin 25) = (272 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_18 : coordinate (pairIndex (15 : Fin 25) (18 : Fin 25)) = (min 15 18, max 15 18) := by
  have hidx : pairIndex (15 : Fin 25) (18 : Fin 25) = (273 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_19 : coordinate (pairIndex (15 : Fin 25) (19 : Fin 25)) = (min 15 19, max 15 19) := by
  have hidx : pairIndex (15 : Fin 25) (19 : Fin 25) = (274 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_20 : coordinate (pairIndex (15 : Fin 25) (20 : Fin 25)) = (min 15 20, max 15 20) := by
  have hidx : pairIndex (15 : Fin 25) (20 : Fin 25) = (275 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_21 : coordinate (pairIndex (15 : Fin 25) (21 : Fin 25)) = (min 15 21, max 15 21) := by
  have hidx : pairIndex (15 : Fin 25) (21 : Fin 25) = (276 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_22 : coordinate (pairIndex (15 : Fin 25) (22 : Fin 25)) = (min 15 22, max 15 22) := by
  have hidx : pairIndex (15 : Fin 25) (22 : Fin 25) = (277 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_23 : coordinate (pairIndex (15 : Fin 25) (23 : Fin 25)) = (min 15 23, max 15 23) := by
  have hidx : pairIndex (15 : Fin 25) (23 : Fin 25) = (278 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_15_24 : coordinate (pairIndex (15 : Fin 25) (24 : Fin 25)) = (min 15 24, max 15 24) := by
  have hidx : pairIndex (15 : Fin 25) (24 : Fin 25) = (279 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_0 : coordinate (pairIndex (16 : Fin 25) (0 : Fin 25)) = (min 16 0, max 16 0) := by
  have hidx : pairIndex (16 : Fin 25) (0 : Fin 25) = (16 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_1 : coordinate (pairIndex (16 : Fin 25) (1 : Fin 25)) = (min 16 1, max 16 1) := by
  have hidx : pairIndex (16 : Fin 25) (1 : Fin 25) = (40 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_2 : coordinate (pairIndex (16 : Fin 25) (2 : Fin 25)) = (min 16 2, max 16 2) := by
  have hidx : pairIndex (16 : Fin 25) (2 : Fin 25) = (63 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_3 : coordinate (pairIndex (16 : Fin 25) (3 : Fin 25)) = (min 16 3, max 16 3) := by
  have hidx : pairIndex (16 : Fin 25) (3 : Fin 25) = (85 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_4 : coordinate (pairIndex (16 : Fin 25) (4 : Fin 25)) = (min 16 4, max 16 4) := by
  have hidx : pairIndex (16 : Fin 25) (4 : Fin 25) = (106 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_5 : coordinate (pairIndex (16 : Fin 25) (5 : Fin 25)) = (min 16 5, max 16 5) := by
  have hidx : pairIndex (16 : Fin 25) (5 : Fin 25) = (126 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_6 : coordinate (pairIndex (16 : Fin 25) (6 : Fin 25)) = (min 16 6, max 16 6) := by
  have hidx : pairIndex (16 : Fin 25) (6 : Fin 25) = (145 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_7 : coordinate (pairIndex (16 : Fin 25) (7 : Fin 25)) = (min 16 7, max 16 7) := by
  have hidx : pairIndex (16 : Fin 25) (7 : Fin 25) = (163 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_8 : coordinate (pairIndex (16 : Fin 25) (8 : Fin 25)) = (min 16 8, max 16 8) := by
  have hidx : pairIndex (16 : Fin 25) (8 : Fin 25) = (180 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_9 : coordinate (pairIndex (16 : Fin 25) (9 : Fin 25)) = (min 16 9, max 16 9) := by
  have hidx : pairIndex (16 : Fin 25) (9 : Fin 25) = (196 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_10 : coordinate (pairIndex (16 : Fin 25) (10 : Fin 25)) = (min 16 10, max 16 10) := by
  have hidx : pairIndex (16 : Fin 25) (10 : Fin 25) = (211 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_11 : coordinate (pairIndex (16 : Fin 25) (11 : Fin 25)) = (min 16 11, max 16 11) := by
  have hidx : pairIndex (16 : Fin 25) (11 : Fin 25) = (225 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_12 : coordinate (pairIndex (16 : Fin 25) (12 : Fin 25)) = (min 16 12, max 16 12) := by
  have hidx : pairIndex (16 : Fin 25) (12 : Fin 25) = (238 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_13 : coordinate (pairIndex (16 : Fin 25) (13 : Fin 25)) = (min 16 13, max 16 13) := by
  have hidx : pairIndex (16 : Fin 25) (13 : Fin 25) = (250 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_14 : coordinate (pairIndex (16 : Fin 25) (14 : Fin 25)) = (min 16 14, max 16 14) := by
  have hidx : pairIndex (16 : Fin 25) (14 : Fin 25) = (261 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_15 : coordinate (pairIndex (16 : Fin 25) (15 : Fin 25)) = (min 16 15, max 16 15) := by
  have hidx : pairIndex (16 : Fin 25) (15 : Fin 25) = (271 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_16 : coordinate (pairIndex (16 : Fin 25) (16 : Fin 25)) = (min 16 16, max 16 16) := by
  have hidx : pairIndex (16 : Fin 25) (16 : Fin 25) = (280 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_17 : coordinate (pairIndex (16 : Fin 25) (17 : Fin 25)) = (min 16 17, max 16 17) := by
  have hidx : pairIndex (16 : Fin 25) (17 : Fin 25) = (281 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_18 : coordinate (pairIndex (16 : Fin 25) (18 : Fin 25)) = (min 16 18, max 16 18) := by
  have hidx : pairIndex (16 : Fin 25) (18 : Fin 25) = (282 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_19 : coordinate (pairIndex (16 : Fin 25) (19 : Fin 25)) = (min 16 19, max 16 19) := by
  have hidx : pairIndex (16 : Fin 25) (19 : Fin 25) = (283 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_20 : coordinate (pairIndex (16 : Fin 25) (20 : Fin 25)) = (min 16 20, max 16 20) := by
  have hidx : pairIndex (16 : Fin 25) (20 : Fin 25) = (284 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_21 : coordinate (pairIndex (16 : Fin 25) (21 : Fin 25)) = (min 16 21, max 16 21) := by
  have hidx : pairIndex (16 : Fin 25) (21 : Fin 25) = (285 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_22 : coordinate (pairIndex (16 : Fin 25) (22 : Fin 25)) = (min 16 22, max 16 22) := by
  have hidx : pairIndex (16 : Fin 25) (22 : Fin 25) = (286 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_23 : coordinate (pairIndex (16 : Fin 25) (23 : Fin 25)) = (min 16 23, max 16 23) := by
  have hidx : pairIndex (16 : Fin 25) (23 : Fin 25) = (287 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_16_24 : coordinate (pairIndex (16 : Fin 25) (24 : Fin 25)) = (min 16 24, max 16 24) := by
  have hidx : pairIndex (16 : Fin 25) (24 : Fin 25) = (288 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_0 : coordinate (pairIndex (17 : Fin 25) (0 : Fin 25)) = (min 17 0, max 17 0) := by
  have hidx : pairIndex (17 : Fin 25) (0 : Fin 25) = (17 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_1 : coordinate (pairIndex (17 : Fin 25) (1 : Fin 25)) = (min 17 1, max 17 1) := by
  have hidx : pairIndex (17 : Fin 25) (1 : Fin 25) = (41 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_2 : coordinate (pairIndex (17 : Fin 25) (2 : Fin 25)) = (min 17 2, max 17 2) := by
  have hidx : pairIndex (17 : Fin 25) (2 : Fin 25) = (64 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_3 : coordinate (pairIndex (17 : Fin 25) (3 : Fin 25)) = (min 17 3, max 17 3) := by
  have hidx : pairIndex (17 : Fin 25) (3 : Fin 25) = (86 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_4 : coordinate (pairIndex (17 : Fin 25) (4 : Fin 25)) = (min 17 4, max 17 4) := by
  have hidx : pairIndex (17 : Fin 25) (4 : Fin 25) = (107 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_5 : coordinate (pairIndex (17 : Fin 25) (5 : Fin 25)) = (min 17 5, max 17 5) := by
  have hidx : pairIndex (17 : Fin 25) (5 : Fin 25) = (127 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_6 : coordinate (pairIndex (17 : Fin 25) (6 : Fin 25)) = (min 17 6, max 17 6) := by
  have hidx : pairIndex (17 : Fin 25) (6 : Fin 25) = (146 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_7 : coordinate (pairIndex (17 : Fin 25) (7 : Fin 25)) = (min 17 7, max 17 7) := by
  have hidx : pairIndex (17 : Fin 25) (7 : Fin 25) = (164 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_8 : coordinate (pairIndex (17 : Fin 25) (8 : Fin 25)) = (min 17 8, max 17 8) := by
  have hidx : pairIndex (17 : Fin 25) (8 : Fin 25) = (181 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_9 : coordinate (pairIndex (17 : Fin 25) (9 : Fin 25)) = (min 17 9, max 17 9) := by
  have hidx : pairIndex (17 : Fin 25) (9 : Fin 25) = (197 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_10 : coordinate (pairIndex (17 : Fin 25) (10 : Fin 25)) = (min 17 10, max 17 10) := by
  have hidx : pairIndex (17 : Fin 25) (10 : Fin 25) = (212 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_11 : coordinate (pairIndex (17 : Fin 25) (11 : Fin 25)) = (min 17 11, max 17 11) := by
  have hidx : pairIndex (17 : Fin 25) (11 : Fin 25) = (226 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_12 : coordinate (pairIndex (17 : Fin 25) (12 : Fin 25)) = (min 17 12, max 17 12) := by
  have hidx : pairIndex (17 : Fin 25) (12 : Fin 25) = (239 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_13 : coordinate (pairIndex (17 : Fin 25) (13 : Fin 25)) = (min 17 13, max 17 13) := by
  have hidx : pairIndex (17 : Fin 25) (13 : Fin 25) = (251 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_14 : coordinate (pairIndex (17 : Fin 25) (14 : Fin 25)) = (min 17 14, max 17 14) := by
  have hidx : pairIndex (17 : Fin 25) (14 : Fin 25) = (262 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_15 : coordinate (pairIndex (17 : Fin 25) (15 : Fin 25)) = (min 17 15, max 17 15) := by
  have hidx : pairIndex (17 : Fin 25) (15 : Fin 25) = (272 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_16 : coordinate (pairIndex (17 : Fin 25) (16 : Fin 25)) = (min 17 16, max 17 16) := by
  have hidx : pairIndex (17 : Fin 25) (16 : Fin 25) = (281 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_17 : coordinate (pairIndex (17 : Fin 25) (17 : Fin 25)) = (min 17 17, max 17 17) := by
  have hidx : pairIndex (17 : Fin 25) (17 : Fin 25) = (289 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_18 : coordinate (pairIndex (17 : Fin 25) (18 : Fin 25)) = (min 17 18, max 17 18) := by
  have hidx : pairIndex (17 : Fin 25) (18 : Fin 25) = (290 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_19 : coordinate (pairIndex (17 : Fin 25) (19 : Fin 25)) = (min 17 19, max 17 19) := by
  have hidx : pairIndex (17 : Fin 25) (19 : Fin 25) = (291 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_20 : coordinate (pairIndex (17 : Fin 25) (20 : Fin 25)) = (min 17 20, max 17 20) := by
  have hidx : pairIndex (17 : Fin 25) (20 : Fin 25) = (292 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_21 : coordinate (pairIndex (17 : Fin 25) (21 : Fin 25)) = (min 17 21, max 17 21) := by
  have hidx : pairIndex (17 : Fin 25) (21 : Fin 25) = (293 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_22 : coordinate (pairIndex (17 : Fin 25) (22 : Fin 25)) = (min 17 22, max 17 22) := by
  have hidx : pairIndex (17 : Fin 25) (22 : Fin 25) = (294 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_23 : coordinate (pairIndex (17 : Fin 25) (23 : Fin 25)) = (min 17 23, max 17 23) := by
  have hidx : pairIndex (17 : Fin 25) (23 : Fin 25) = (295 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_17_24 : coordinate (pairIndex (17 : Fin 25) (24 : Fin 25)) = (min 17 24, max 17 24) := by
  have hidx : pairIndex (17 : Fin 25) (24 : Fin 25) = (296 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_0 : coordinate (pairIndex (18 : Fin 25) (0 : Fin 25)) = (min 18 0, max 18 0) := by
  have hidx : pairIndex (18 : Fin 25) (0 : Fin 25) = (18 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_1 : coordinate (pairIndex (18 : Fin 25) (1 : Fin 25)) = (min 18 1, max 18 1) := by
  have hidx : pairIndex (18 : Fin 25) (1 : Fin 25) = (42 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_2 : coordinate (pairIndex (18 : Fin 25) (2 : Fin 25)) = (min 18 2, max 18 2) := by
  have hidx : pairIndex (18 : Fin 25) (2 : Fin 25) = (65 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_3 : coordinate (pairIndex (18 : Fin 25) (3 : Fin 25)) = (min 18 3, max 18 3) := by
  have hidx : pairIndex (18 : Fin 25) (3 : Fin 25) = (87 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_4 : coordinate (pairIndex (18 : Fin 25) (4 : Fin 25)) = (min 18 4, max 18 4) := by
  have hidx : pairIndex (18 : Fin 25) (4 : Fin 25) = (108 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_5 : coordinate (pairIndex (18 : Fin 25) (5 : Fin 25)) = (min 18 5, max 18 5) := by
  have hidx : pairIndex (18 : Fin 25) (5 : Fin 25) = (128 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_6 : coordinate (pairIndex (18 : Fin 25) (6 : Fin 25)) = (min 18 6, max 18 6) := by
  have hidx : pairIndex (18 : Fin 25) (6 : Fin 25) = (147 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_7 : coordinate (pairIndex (18 : Fin 25) (7 : Fin 25)) = (min 18 7, max 18 7) := by
  have hidx : pairIndex (18 : Fin 25) (7 : Fin 25) = (165 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_8 : coordinate (pairIndex (18 : Fin 25) (8 : Fin 25)) = (min 18 8, max 18 8) := by
  have hidx : pairIndex (18 : Fin 25) (8 : Fin 25) = (182 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_9 : coordinate (pairIndex (18 : Fin 25) (9 : Fin 25)) = (min 18 9, max 18 9) := by
  have hidx : pairIndex (18 : Fin 25) (9 : Fin 25) = (198 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_10 : coordinate (pairIndex (18 : Fin 25) (10 : Fin 25)) = (min 18 10, max 18 10) := by
  have hidx : pairIndex (18 : Fin 25) (10 : Fin 25) = (213 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_11 : coordinate (pairIndex (18 : Fin 25) (11 : Fin 25)) = (min 18 11, max 18 11) := by
  have hidx : pairIndex (18 : Fin 25) (11 : Fin 25) = (227 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_12 : coordinate (pairIndex (18 : Fin 25) (12 : Fin 25)) = (min 18 12, max 18 12) := by
  have hidx : pairIndex (18 : Fin 25) (12 : Fin 25) = (240 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_13 : coordinate (pairIndex (18 : Fin 25) (13 : Fin 25)) = (min 18 13, max 18 13) := by
  have hidx : pairIndex (18 : Fin 25) (13 : Fin 25) = (252 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_14 : coordinate (pairIndex (18 : Fin 25) (14 : Fin 25)) = (min 18 14, max 18 14) := by
  have hidx : pairIndex (18 : Fin 25) (14 : Fin 25) = (263 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_15 : coordinate (pairIndex (18 : Fin 25) (15 : Fin 25)) = (min 18 15, max 18 15) := by
  have hidx : pairIndex (18 : Fin 25) (15 : Fin 25) = (273 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_16 : coordinate (pairIndex (18 : Fin 25) (16 : Fin 25)) = (min 18 16, max 18 16) := by
  have hidx : pairIndex (18 : Fin 25) (16 : Fin 25) = (282 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_17 : coordinate (pairIndex (18 : Fin 25) (17 : Fin 25)) = (min 18 17, max 18 17) := by
  have hidx : pairIndex (18 : Fin 25) (17 : Fin 25) = (290 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_18 : coordinate (pairIndex (18 : Fin 25) (18 : Fin 25)) = (min 18 18, max 18 18) := by
  have hidx : pairIndex (18 : Fin 25) (18 : Fin 25) = (297 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_19 : coordinate (pairIndex (18 : Fin 25) (19 : Fin 25)) = (min 18 19, max 18 19) := by
  have hidx : pairIndex (18 : Fin 25) (19 : Fin 25) = (298 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_20 : coordinate (pairIndex (18 : Fin 25) (20 : Fin 25)) = (min 18 20, max 18 20) := by
  have hidx : pairIndex (18 : Fin 25) (20 : Fin 25) = (299 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_21 : coordinate (pairIndex (18 : Fin 25) (21 : Fin 25)) = (min 18 21, max 18 21) := by
  have hidx : pairIndex (18 : Fin 25) (21 : Fin 25) = (300 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_22 : coordinate (pairIndex (18 : Fin 25) (22 : Fin 25)) = (min 18 22, max 18 22) := by
  have hidx : pairIndex (18 : Fin 25) (22 : Fin 25) = (301 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_23 : coordinate (pairIndex (18 : Fin 25) (23 : Fin 25)) = (min 18 23, max 18 23) := by
  have hidx : pairIndex (18 : Fin 25) (23 : Fin 25) = (302 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_18_24 : coordinate (pairIndex (18 : Fin 25) (24 : Fin 25)) = (min 18 24, max 18 24) := by
  have hidx : pairIndex (18 : Fin 25) (24 : Fin 25) = (303 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_0 : coordinate (pairIndex (19 : Fin 25) (0 : Fin 25)) = (min 19 0, max 19 0) := by
  have hidx : pairIndex (19 : Fin 25) (0 : Fin 25) = (19 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_1 : coordinate (pairIndex (19 : Fin 25) (1 : Fin 25)) = (min 19 1, max 19 1) := by
  have hidx : pairIndex (19 : Fin 25) (1 : Fin 25) = (43 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_2 : coordinate (pairIndex (19 : Fin 25) (2 : Fin 25)) = (min 19 2, max 19 2) := by
  have hidx : pairIndex (19 : Fin 25) (2 : Fin 25) = (66 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_3 : coordinate (pairIndex (19 : Fin 25) (3 : Fin 25)) = (min 19 3, max 19 3) := by
  have hidx : pairIndex (19 : Fin 25) (3 : Fin 25) = (88 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_4 : coordinate (pairIndex (19 : Fin 25) (4 : Fin 25)) = (min 19 4, max 19 4) := by
  have hidx : pairIndex (19 : Fin 25) (4 : Fin 25) = (109 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_5 : coordinate (pairIndex (19 : Fin 25) (5 : Fin 25)) = (min 19 5, max 19 5) := by
  have hidx : pairIndex (19 : Fin 25) (5 : Fin 25) = (129 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_6 : coordinate (pairIndex (19 : Fin 25) (6 : Fin 25)) = (min 19 6, max 19 6) := by
  have hidx : pairIndex (19 : Fin 25) (6 : Fin 25) = (148 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_7 : coordinate (pairIndex (19 : Fin 25) (7 : Fin 25)) = (min 19 7, max 19 7) := by
  have hidx : pairIndex (19 : Fin 25) (7 : Fin 25) = (166 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_8 : coordinate (pairIndex (19 : Fin 25) (8 : Fin 25)) = (min 19 8, max 19 8) := by
  have hidx : pairIndex (19 : Fin 25) (8 : Fin 25) = (183 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_9 : coordinate (pairIndex (19 : Fin 25) (9 : Fin 25)) = (min 19 9, max 19 9) := by
  have hidx : pairIndex (19 : Fin 25) (9 : Fin 25) = (199 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_10 : coordinate (pairIndex (19 : Fin 25) (10 : Fin 25)) = (min 19 10, max 19 10) := by
  have hidx : pairIndex (19 : Fin 25) (10 : Fin 25) = (214 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_11 : coordinate (pairIndex (19 : Fin 25) (11 : Fin 25)) = (min 19 11, max 19 11) := by
  have hidx : pairIndex (19 : Fin 25) (11 : Fin 25) = (228 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_12 : coordinate (pairIndex (19 : Fin 25) (12 : Fin 25)) = (min 19 12, max 19 12) := by
  have hidx : pairIndex (19 : Fin 25) (12 : Fin 25) = (241 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_13 : coordinate (pairIndex (19 : Fin 25) (13 : Fin 25)) = (min 19 13, max 19 13) := by
  have hidx : pairIndex (19 : Fin 25) (13 : Fin 25) = (253 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_14 : coordinate (pairIndex (19 : Fin 25) (14 : Fin 25)) = (min 19 14, max 19 14) := by
  have hidx : pairIndex (19 : Fin 25) (14 : Fin 25) = (264 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_15 : coordinate (pairIndex (19 : Fin 25) (15 : Fin 25)) = (min 19 15, max 19 15) := by
  have hidx : pairIndex (19 : Fin 25) (15 : Fin 25) = (274 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_16 : coordinate (pairIndex (19 : Fin 25) (16 : Fin 25)) = (min 19 16, max 19 16) := by
  have hidx : pairIndex (19 : Fin 25) (16 : Fin 25) = (283 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_17 : coordinate (pairIndex (19 : Fin 25) (17 : Fin 25)) = (min 19 17, max 19 17) := by
  have hidx : pairIndex (19 : Fin 25) (17 : Fin 25) = (291 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_18 : coordinate (pairIndex (19 : Fin 25) (18 : Fin 25)) = (min 19 18, max 19 18) := by
  have hidx : pairIndex (19 : Fin 25) (18 : Fin 25) = (298 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_19 : coordinate (pairIndex (19 : Fin 25) (19 : Fin 25)) = (min 19 19, max 19 19) := by
  have hidx : pairIndex (19 : Fin 25) (19 : Fin 25) = (304 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_20 : coordinate (pairIndex (19 : Fin 25) (20 : Fin 25)) = (min 19 20, max 19 20) := by
  have hidx : pairIndex (19 : Fin 25) (20 : Fin 25) = (305 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_21 : coordinate (pairIndex (19 : Fin 25) (21 : Fin 25)) = (min 19 21, max 19 21) := by
  have hidx : pairIndex (19 : Fin 25) (21 : Fin 25) = (306 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_22 : coordinate (pairIndex (19 : Fin 25) (22 : Fin 25)) = (min 19 22, max 19 22) := by
  have hidx : pairIndex (19 : Fin 25) (22 : Fin 25) = (307 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_23 : coordinate (pairIndex (19 : Fin 25) (23 : Fin 25)) = (min 19 23, max 19 23) := by
  have hidx : pairIndex (19 : Fin 25) (23 : Fin 25) = (308 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_19_24 : coordinate (pairIndex (19 : Fin 25) (24 : Fin 25)) = (min 19 24, max 19 24) := by
  have hidx : pairIndex (19 : Fin 25) (24 : Fin 25) = (309 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_0 : coordinate (pairIndex (20 : Fin 25) (0 : Fin 25)) = (min 20 0, max 20 0) := by
  have hidx : pairIndex (20 : Fin 25) (0 : Fin 25) = (20 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_1 : coordinate (pairIndex (20 : Fin 25) (1 : Fin 25)) = (min 20 1, max 20 1) := by
  have hidx : pairIndex (20 : Fin 25) (1 : Fin 25) = (44 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_2 : coordinate (pairIndex (20 : Fin 25) (2 : Fin 25)) = (min 20 2, max 20 2) := by
  have hidx : pairIndex (20 : Fin 25) (2 : Fin 25) = (67 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_3 : coordinate (pairIndex (20 : Fin 25) (3 : Fin 25)) = (min 20 3, max 20 3) := by
  have hidx : pairIndex (20 : Fin 25) (3 : Fin 25) = (89 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_4 : coordinate (pairIndex (20 : Fin 25) (4 : Fin 25)) = (min 20 4, max 20 4) := by
  have hidx : pairIndex (20 : Fin 25) (4 : Fin 25) = (110 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_5 : coordinate (pairIndex (20 : Fin 25) (5 : Fin 25)) = (min 20 5, max 20 5) := by
  have hidx : pairIndex (20 : Fin 25) (5 : Fin 25) = (130 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_6 : coordinate (pairIndex (20 : Fin 25) (6 : Fin 25)) = (min 20 6, max 20 6) := by
  have hidx : pairIndex (20 : Fin 25) (6 : Fin 25) = (149 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_7 : coordinate (pairIndex (20 : Fin 25) (7 : Fin 25)) = (min 20 7, max 20 7) := by
  have hidx : pairIndex (20 : Fin 25) (7 : Fin 25) = (167 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_8 : coordinate (pairIndex (20 : Fin 25) (8 : Fin 25)) = (min 20 8, max 20 8) := by
  have hidx : pairIndex (20 : Fin 25) (8 : Fin 25) = (184 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_9 : coordinate (pairIndex (20 : Fin 25) (9 : Fin 25)) = (min 20 9, max 20 9) := by
  have hidx : pairIndex (20 : Fin 25) (9 : Fin 25) = (200 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_10 : coordinate (pairIndex (20 : Fin 25) (10 : Fin 25)) = (min 20 10, max 20 10) := by
  have hidx : pairIndex (20 : Fin 25) (10 : Fin 25) = (215 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_11 : coordinate (pairIndex (20 : Fin 25) (11 : Fin 25)) = (min 20 11, max 20 11) := by
  have hidx : pairIndex (20 : Fin 25) (11 : Fin 25) = (229 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_12 : coordinate (pairIndex (20 : Fin 25) (12 : Fin 25)) = (min 20 12, max 20 12) := by
  have hidx : pairIndex (20 : Fin 25) (12 : Fin 25) = (242 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_13 : coordinate (pairIndex (20 : Fin 25) (13 : Fin 25)) = (min 20 13, max 20 13) := by
  have hidx : pairIndex (20 : Fin 25) (13 : Fin 25) = (254 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_14 : coordinate (pairIndex (20 : Fin 25) (14 : Fin 25)) = (min 20 14, max 20 14) := by
  have hidx : pairIndex (20 : Fin 25) (14 : Fin 25) = (265 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_15 : coordinate (pairIndex (20 : Fin 25) (15 : Fin 25)) = (min 20 15, max 20 15) := by
  have hidx : pairIndex (20 : Fin 25) (15 : Fin 25) = (275 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_16 : coordinate (pairIndex (20 : Fin 25) (16 : Fin 25)) = (min 20 16, max 20 16) := by
  have hidx : pairIndex (20 : Fin 25) (16 : Fin 25) = (284 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_17 : coordinate (pairIndex (20 : Fin 25) (17 : Fin 25)) = (min 20 17, max 20 17) := by
  have hidx : pairIndex (20 : Fin 25) (17 : Fin 25) = (292 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_18 : coordinate (pairIndex (20 : Fin 25) (18 : Fin 25)) = (min 20 18, max 20 18) := by
  have hidx : pairIndex (20 : Fin 25) (18 : Fin 25) = (299 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_19 : coordinate (pairIndex (20 : Fin 25) (19 : Fin 25)) = (min 20 19, max 20 19) := by
  have hidx : pairIndex (20 : Fin 25) (19 : Fin 25) = (305 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_20 : coordinate (pairIndex (20 : Fin 25) (20 : Fin 25)) = (min 20 20, max 20 20) := by
  have hidx : pairIndex (20 : Fin 25) (20 : Fin 25) = (310 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_21 : coordinate (pairIndex (20 : Fin 25) (21 : Fin 25)) = (min 20 21, max 20 21) := by
  have hidx : pairIndex (20 : Fin 25) (21 : Fin 25) = (311 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_22 : coordinate (pairIndex (20 : Fin 25) (22 : Fin 25)) = (min 20 22, max 20 22) := by
  have hidx : pairIndex (20 : Fin 25) (22 : Fin 25) = (312 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_23 : coordinate (pairIndex (20 : Fin 25) (23 : Fin 25)) = (min 20 23, max 20 23) := by
  have hidx : pairIndex (20 : Fin 25) (23 : Fin 25) = (313 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_20_24 : coordinate (pairIndex (20 : Fin 25) (24 : Fin 25)) = (min 20 24, max 20 24) := by
  have hidx : pairIndex (20 : Fin 25) (24 : Fin 25) = (314 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_0 : coordinate (pairIndex (21 : Fin 25) (0 : Fin 25)) = (min 21 0, max 21 0) := by
  have hidx : pairIndex (21 : Fin 25) (0 : Fin 25) = (21 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_1 : coordinate (pairIndex (21 : Fin 25) (1 : Fin 25)) = (min 21 1, max 21 1) := by
  have hidx : pairIndex (21 : Fin 25) (1 : Fin 25) = (45 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_2 : coordinate (pairIndex (21 : Fin 25) (2 : Fin 25)) = (min 21 2, max 21 2) := by
  have hidx : pairIndex (21 : Fin 25) (2 : Fin 25) = (68 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_3 : coordinate (pairIndex (21 : Fin 25) (3 : Fin 25)) = (min 21 3, max 21 3) := by
  have hidx : pairIndex (21 : Fin 25) (3 : Fin 25) = (90 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_4 : coordinate (pairIndex (21 : Fin 25) (4 : Fin 25)) = (min 21 4, max 21 4) := by
  have hidx : pairIndex (21 : Fin 25) (4 : Fin 25) = (111 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_5 : coordinate (pairIndex (21 : Fin 25) (5 : Fin 25)) = (min 21 5, max 21 5) := by
  have hidx : pairIndex (21 : Fin 25) (5 : Fin 25) = (131 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_6 : coordinate (pairIndex (21 : Fin 25) (6 : Fin 25)) = (min 21 6, max 21 6) := by
  have hidx : pairIndex (21 : Fin 25) (6 : Fin 25) = (150 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_7 : coordinate (pairIndex (21 : Fin 25) (7 : Fin 25)) = (min 21 7, max 21 7) := by
  have hidx : pairIndex (21 : Fin 25) (7 : Fin 25) = (168 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_8 : coordinate (pairIndex (21 : Fin 25) (8 : Fin 25)) = (min 21 8, max 21 8) := by
  have hidx : pairIndex (21 : Fin 25) (8 : Fin 25) = (185 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_9 : coordinate (pairIndex (21 : Fin 25) (9 : Fin 25)) = (min 21 9, max 21 9) := by
  have hidx : pairIndex (21 : Fin 25) (9 : Fin 25) = (201 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_10 : coordinate (pairIndex (21 : Fin 25) (10 : Fin 25)) = (min 21 10, max 21 10) := by
  have hidx : pairIndex (21 : Fin 25) (10 : Fin 25) = (216 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_11 : coordinate (pairIndex (21 : Fin 25) (11 : Fin 25)) = (min 21 11, max 21 11) := by
  have hidx : pairIndex (21 : Fin 25) (11 : Fin 25) = (230 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_12 : coordinate (pairIndex (21 : Fin 25) (12 : Fin 25)) = (min 21 12, max 21 12) := by
  have hidx : pairIndex (21 : Fin 25) (12 : Fin 25) = (243 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_13 : coordinate (pairIndex (21 : Fin 25) (13 : Fin 25)) = (min 21 13, max 21 13) := by
  have hidx : pairIndex (21 : Fin 25) (13 : Fin 25) = (255 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_14 : coordinate (pairIndex (21 : Fin 25) (14 : Fin 25)) = (min 21 14, max 21 14) := by
  have hidx : pairIndex (21 : Fin 25) (14 : Fin 25) = (266 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_15 : coordinate (pairIndex (21 : Fin 25) (15 : Fin 25)) = (min 21 15, max 21 15) := by
  have hidx : pairIndex (21 : Fin 25) (15 : Fin 25) = (276 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_16 : coordinate (pairIndex (21 : Fin 25) (16 : Fin 25)) = (min 21 16, max 21 16) := by
  have hidx : pairIndex (21 : Fin 25) (16 : Fin 25) = (285 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_17 : coordinate (pairIndex (21 : Fin 25) (17 : Fin 25)) = (min 21 17, max 21 17) := by
  have hidx : pairIndex (21 : Fin 25) (17 : Fin 25) = (293 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_18 : coordinate (pairIndex (21 : Fin 25) (18 : Fin 25)) = (min 21 18, max 21 18) := by
  have hidx : pairIndex (21 : Fin 25) (18 : Fin 25) = (300 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_19 : coordinate (pairIndex (21 : Fin 25) (19 : Fin 25)) = (min 21 19, max 21 19) := by
  have hidx : pairIndex (21 : Fin 25) (19 : Fin 25) = (306 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_20 : coordinate (pairIndex (21 : Fin 25) (20 : Fin 25)) = (min 21 20, max 21 20) := by
  have hidx : pairIndex (21 : Fin 25) (20 : Fin 25) = (311 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_21 : coordinate (pairIndex (21 : Fin 25) (21 : Fin 25)) = (min 21 21, max 21 21) := by
  have hidx : pairIndex (21 : Fin 25) (21 : Fin 25) = (315 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_22 : coordinate (pairIndex (21 : Fin 25) (22 : Fin 25)) = (min 21 22, max 21 22) := by
  have hidx : pairIndex (21 : Fin 25) (22 : Fin 25) = (316 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_23 : coordinate (pairIndex (21 : Fin 25) (23 : Fin 25)) = (min 21 23, max 21 23) := by
  have hidx : pairIndex (21 : Fin 25) (23 : Fin 25) = (317 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_21_24 : coordinate (pairIndex (21 : Fin 25) (24 : Fin 25)) = (min 21 24, max 21 24) := by
  have hidx : pairIndex (21 : Fin 25) (24 : Fin 25) = (318 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_0 : coordinate (pairIndex (22 : Fin 25) (0 : Fin 25)) = (min 22 0, max 22 0) := by
  have hidx : pairIndex (22 : Fin 25) (0 : Fin 25) = (22 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_1 : coordinate (pairIndex (22 : Fin 25) (1 : Fin 25)) = (min 22 1, max 22 1) := by
  have hidx : pairIndex (22 : Fin 25) (1 : Fin 25) = (46 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_2 : coordinate (pairIndex (22 : Fin 25) (2 : Fin 25)) = (min 22 2, max 22 2) := by
  have hidx : pairIndex (22 : Fin 25) (2 : Fin 25) = (69 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_3 : coordinate (pairIndex (22 : Fin 25) (3 : Fin 25)) = (min 22 3, max 22 3) := by
  have hidx : pairIndex (22 : Fin 25) (3 : Fin 25) = (91 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_4 : coordinate (pairIndex (22 : Fin 25) (4 : Fin 25)) = (min 22 4, max 22 4) := by
  have hidx : pairIndex (22 : Fin 25) (4 : Fin 25) = (112 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_5 : coordinate (pairIndex (22 : Fin 25) (5 : Fin 25)) = (min 22 5, max 22 5) := by
  have hidx : pairIndex (22 : Fin 25) (5 : Fin 25) = (132 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_6 : coordinate (pairIndex (22 : Fin 25) (6 : Fin 25)) = (min 22 6, max 22 6) := by
  have hidx : pairIndex (22 : Fin 25) (6 : Fin 25) = (151 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_7 : coordinate (pairIndex (22 : Fin 25) (7 : Fin 25)) = (min 22 7, max 22 7) := by
  have hidx : pairIndex (22 : Fin 25) (7 : Fin 25) = (169 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_8 : coordinate (pairIndex (22 : Fin 25) (8 : Fin 25)) = (min 22 8, max 22 8) := by
  have hidx : pairIndex (22 : Fin 25) (8 : Fin 25) = (186 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_9 : coordinate (pairIndex (22 : Fin 25) (9 : Fin 25)) = (min 22 9, max 22 9) := by
  have hidx : pairIndex (22 : Fin 25) (9 : Fin 25) = (202 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_10 : coordinate (pairIndex (22 : Fin 25) (10 : Fin 25)) = (min 22 10, max 22 10) := by
  have hidx : pairIndex (22 : Fin 25) (10 : Fin 25) = (217 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_11 : coordinate (pairIndex (22 : Fin 25) (11 : Fin 25)) = (min 22 11, max 22 11) := by
  have hidx : pairIndex (22 : Fin 25) (11 : Fin 25) = (231 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_12 : coordinate (pairIndex (22 : Fin 25) (12 : Fin 25)) = (min 22 12, max 22 12) := by
  have hidx : pairIndex (22 : Fin 25) (12 : Fin 25) = (244 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_13 : coordinate (pairIndex (22 : Fin 25) (13 : Fin 25)) = (min 22 13, max 22 13) := by
  have hidx : pairIndex (22 : Fin 25) (13 : Fin 25) = (256 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_14 : coordinate (pairIndex (22 : Fin 25) (14 : Fin 25)) = (min 22 14, max 22 14) := by
  have hidx : pairIndex (22 : Fin 25) (14 : Fin 25) = (267 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_15 : coordinate (pairIndex (22 : Fin 25) (15 : Fin 25)) = (min 22 15, max 22 15) := by
  have hidx : pairIndex (22 : Fin 25) (15 : Fin 25) = (277 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_16 : coordinate (pairIndex (22 : Fin 25) (16 : Fin 25)) = (min 22 16, max 22 16) := by
  have hidx : pairIndex (22 : Fin 25) (16 : Fin 25) = (286 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_17 : coordinate (pairIndex (22 : Fin 25) (17 : Fin 25)) = (min 22 17, max 22 17) := by
  have hidx : pairIndex (22 : Fin 25) (17 : Fin 25) = (294 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_18 : coordinate (pairIndex (22 : Fin 25) (18 : Fin 25)) = (min 22 18, max 22 18) := by
  have hidx : pairIndex (22 : Fin 25) (18 : Fin 25) = (301 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_19 : coordinate (pairIndex (22 : Fin 25) (19 : Fin 25)) = (min 22 19, max 22 19) := by
  have hidx : pairIndex (22 : Fin 25) (19 : Fin 25) = (307 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_20 : coordinate (pairIndex (22 : Fin 25) (20 : Fin 25)) = (min 22 20, max 22 20) := by
  have hidx : pairIndex (22 : Fin 25) (20 : Fin 25) = (312 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_21 : coordinate (pairIndex (22 : Fin 25) (21 : Fin 25)) = (min 22 21, max 22 21) := by
  have hidx : pairIndex (22 : Fin 25) (21 : Fin 25) = (316 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_22 : coordinate (pairIndex (22 : Fin 25) (22 : Fin 25)) = (min 22 22, max 22 22) := by
  have hidx : pairIndex (22 : Fin 25) (22 : Fin 25) = (319 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_23 : coordinate (pairIndex (22 : Fin 25) (23 : Fin 25)) = (min 22 23, max 22 23) := by
  have hidx : pairIndex (22 : Fin 25) (23 : Fin 25) = (320 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_22_24 : coordinate (pairIndex (22 : Fin 25) (24 : Fin 25)) = (min 22 24, max 22 24) := by
  have hidx : pairIndex (22 : Fin 25) (24 : Fin 25) = (321 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_0 : coordinate (pairIndex (23 : Fin 25) (0 : Fin 25)) = (min 23 0, max 23 0) := by
  have hidx : pairIndex (23 : Fin 25) (0 : Fin 25) = (23 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_1 : coordinate (pairIndex (23 : Fin 25) (1 : Fin 25)) = (min 23 1, max 23 1) := by
  have hidx : pairIndex (23 : Fin 25) (1 : Fin 25) = (47 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_2 : coordinate (pairIndex (23 : Fin 25) (2 : Fin 25)) = (min 23 2, max 23 2) := by
  have hidx : pairIndex (23 : Fin 25) (2 : Fin 25) = (70 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_3 : coordinate (pairIndex (23 : Fin 25) (3 : Fin 25)) = (min 23 3, max 23 3) := by
  have hidx : pairIndex (23 : Fin 25) (3 : Fin 25) = (92 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_4 : coordinate (pairIndex (23 : Fin 25) (4 : Fin 25)) = (min 23 4, max 23 4) := by
  have hidx : pairIndex (23 : Fin 25) (4 : Fin 25) = (113 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_5 : coordinate (pairIndex (23 : Fin 25) (5 : Fin 25)) = (min 23 5, max 23 5) := by
  have hidx : pairIndex (23 : Fin 25) (5 : Fin 25) = (133 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_6 : coordinate (pairIndex (23 : Fin 25) (6 : Fin 25)) = (min 23 6, max 23 6) := by
  have hidx : pairIndex (23 : Fin 25) (6 : Fin 25) = (152 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_7 : coordinate (pairIndex (23 : Fin 25) (7 : Fin 25)) = (min 23 7, max 23 7) := by
  have hidx : pairIndex (23 : Fin 25) (7 : Fin 25) = (170 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_8 : coordinate (pairIndex (23 : Fin 25) (8 : Fin 25)) = (min 23 8, max 23 8) := by
  have hidx : pairIndex (23 : Fin 25) (8 : Fin 25) = (187 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_9 : coordinate (pairIndex (23 : Fin 25) (9 : Fin 25)) = (min 23 9, max 23 9) := by
  have hidx : pairIndex (23 : Fin 25) (9 : Fin 25) = (203 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_10 : coordinate (pairIndex (23 : Fin 25) (10 : Fin 25)) = (min 23 10, max 23 10) := by
  have hidx : pairIndex (23 : Fin 25) (10 : Fin 25) = (218 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_11 : coordinate (pairIndex (23 : Fin 25) (11 : Fin 25)) = (min 23 11, max 23 11) := by
  have hidx : pairIndex (23 : Fin 25) (11 : Fin 25) = (232 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_12 : coordinate (pairIndex (23 : Fin 25) (12 : Fin 25)) = (min 23 12, max 23 12) := by
  have hidx : pairIndex (23 : Fin 25) (12 : Fin 25) = (245 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_13 : coordinate (pairIndex (23 : Fin 25) (13 : Fin 25)) = (min 23 13, max 23 13) := by
  have hidx : pairIndex (23 : Fin 25) (13 : Fin 25) = (257 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_14 : coordinate (pairIndex (23 : Fin 25) (14 : Fin 25)) = (min 23 14, max 23 14) := by
  have hidx : pairIndex (23 : Fin 25) (14 : Fin 25) = (268 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_15 : coordinate (pairIndex (23 : Fin 25) (15 : Fin 25)) = (min 23 15, max 23 15) := by
  have hidx : pairIndex (23 : Fin 25) (15 : Fin 25) = (278 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_16 : coordinate (pairIndex (23 : Fin 25) (16 : Fin 25)) = (min 23 16, max 23 16) := by
  have hidx : pairIndex (23 : Fin 25) (16 : Fin 25) = (287 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_17 : coordinate (pairIndex (23 : Fin 25) (17 : Fin 25)) = (min 23 17, max 23 17) := by
  have hidx : pairIndex (23 : Fin 25) (17 : Fin 25) = (295 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_18 : coordinate (pairIndex (23 : Fin 25) (18 : Fin 25)) = (min 23 18, max 23 18) := by
  have hidx : pairIndex (23 : Fin 25) (18 : Fin 25) = (302 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_19 : coordinate (pairIndex (23 : Fin 25) (19 : Fin 25)) = (min 23 19, max 23 19) := by
  have hidx : pairIndex (23 : Fin 25) (19 : Fin 25) = (308 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_20 : coordinate (pairIndex (23 : Fin 25) (20 : Fin 25)) = (min 23 20, max 23 20) := by
  have hidx : pairIndex (23 : Fin 25) (20 : Fin 25) = (313 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_21 : coordinate (pairIndex (23 : Fin 25) (21 : Fin 25)) = (min 23 21, max 23 21) := by
  have hidx : pairIndex (23 : Fin 25) (21 : Fin 25) = (317 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_22 : coordinate (pairIndex (23 : Fin 25) (22 : Fin 25)) = (min 23 22, max 23 22) := by
  have hidx : pairIndex (23 : Fin 25) (22 : Fin 25) = (320 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_23 : coordinate (pairIndex (23 : Fin 25) (23 : Fin 25)) = (min 23 23, max 23 23) := by
  have hidx : pairIndex (23 : Fin 25) (23 : Fin 25) = (322 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_23_24 : coordinate (pairIndex (23 : Fin 25) (24 : Fin 25)) = (min 23 24, max 23 24) := by
  have hidx : pairIndex (23 : Fin 25) (24 : Fin 25) = (323 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_0 : coordinate (pairIndex (24 : Fin 25) (0 : Fin 25)) = (min 24 0, max 24 0) := by
  have hidx : pairIndex (24 : Fin 25) (0 : Fin 25) = (24 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_1 : coordinate (pairIndex (24 : Fin 25) (1 : Fin 25)) = (min 24 1, max 24 1) := by
  have hidx : pairIndex (24 : Fin 25) (1 : Fin 25) = (48 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_2 : coordinate (pairIndex (24 : Fin 25) (2 : Fin 25)) = (min 24 2, max 24 2) := by
  have hidx : pairIndex (24 : Fin 25) (2 : Fin 25) = (71 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_3 : coordinate (pairIndex (24 : Fin 25) (3 : Fin 25)) = (min 24 3, max 24 3) := by
  have hidx : pairIndex (24 : Fin 25) (3 : Fin 25) = (93 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_4 : coordinate (pairIndex (24 : Fin 25) (4 : Fin 25)) = (min 24 4, max 24 4) := by
  have hidx : pairIndex (24 : Fin 25) (4 : Fin 25) = (114 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_5 : coordinate (pairIndex (24 : Fin 25) (5 : Fin 25)) = (min 24 5, max 24 5) := by
  have hidx : pairIndex (24 : Fin 25) (5 : Fin 25) = (134 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_6 : coordinate (pairIndex (24 : Fin 25) (6 : Fin 25)) = (min 24 6, max 24 6) := by
  have hidx : pairIndex (24 : Fin 25) (6 : Fin 25) = (153 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_7 : coordinate (pairIndex (24 : Fin 25) (7 : Fin 25)) = (min 24 7, max 24 7) := by
  have hidx : pairIndex (24 : Fin 25) (7 : Fin 25) = (171 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_8 : coordinate (pairIndex (24 : Fin 25) (8 : Fin 25)) = (min 24 8, max 24 8) := by
  have hidx : pairIndex (24 : Fin 25) (8 : Fin 25) = (188 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_9 : coordinate (pairIndex (24 : Fin 25) (9 : Fin 25)) = (min 24 9, max 24 9) := by
  have hidx : pairIndex (24 : Fin 25) (9 : Fin 25) = (204 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_10 : coordinate (pairIndex (24 : Fin 25) (10 : Fin 25)) = (min 24 10, max 24 10) := by
  have hidx : pairIndex (24 : Fin 25) (10 : Fin 25) = (219 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_11 : coordinate (pairIndex (24 : Fin 25) (11 : Fin 25)) = (min 24 11, max 24 11) := by
  have hidx : pairIndex (24 : Fin 25) (11 : Fin 25) = (233 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_12 : coordinate (pairIndex (24 : Fin 25) (12 : Fin 25)) = (min 24 12, max 24 12) := by
  have hidx : pairIndex (24 : Fin 25) (12 : Fin 25) = (246 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_13 : coordinate (pairIndex (24 : Fin 25) (13 : Fin 25)) = (min 24 13, max 24 13) := by
  have hidx : pairIndex (24 : Fin 25) (13 : Fin 25) = (258 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_14 : coordinate (pairIndex (24 : Fin 25) (14 : Fin 25)) = (min 24 14, max 24 14) := by
  have hidx : pairIndex (24 : Fin 25) (14 : Fin 25) = (269 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_15 : coordinate (pairIndex (24 : Fin 25) (15 : Fin 25)) = (min 24 15, max 24 15) := by
  have hidx : pairIndex (24 : Fin 25) (15 : Fin 25) = (279 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_16 : coordinate (pairIndex (24 : Fin 25) (16 : Fin 25)) = (min 24 16, max 24 16) := by
  have hidx : pairIndex (24 : Fin 25) (16 : Fin 25) = (288 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_17 : coordinate (pairIndex (24 : Fin 25) (17 : Fin 25)) = (min 24 17, max 24 17) := by
  have hidx : pairIndex (24 : Fin 25) (17 : Fin 25) = (296 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_18 : coordinate (pairIndex (24 : Fin 25) (18 : Fin 25)) = (min 24 18, max 24 18) := by
  have hidx : pairIndex (24 : Fin 25) (18 : Fin 25) = (303 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_19 : coordinate (pairIndex (24 : Fin 25) (19 : Fin 25)) = (min 24 19, max 24 19) := by
  have hidx : pairIndex (24 : Fin 25) (19 : Fin 25) = (309 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_20 : coordinate (pairIndex (24 : Fin 25) (20 : Fin 25)) = (min 24 20, max 24 20) := by
  have hidx : pairIndex (24 : Fin 25) (20 : Fin 25) = (314 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_21 : coordinate (pairIndex (24 : Fin 25) (21 : Fin 25)) = (min 24 21, max 24 21) := by
  have hidx : pairIndex (24 : Fin 25) (21 : Fin 25) = (318 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_22 : coordinate (pairIndex (24 : Fin 25) (22 : Fin 25)) = (min 24 22, max 24 22) := by
  have hidx : pairIndex (24 : Fin 25) (22 : Fin 25) = (321 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_23 : coordinate (pairIndex (24 : Fin 25) (23 : Fin 25)) = (min 24 23, max 24 23) := by
  have hidx : pairIndex (24 : Fin 25) (23 : Fin 25) = (323 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl
theorem pairIndex_coordinate_24_24 : coordinate (pairIndex (24 : Fin 25) (24 : Fin 25)) = (min 24 24, max 24 24) := by
  have hidx : pairIndex (24 : Fin 25) (24 : Fin 25) = (324 : Coord) := by
    apply Fin.ext
    norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
  rw [hidx]
  rfl

theorem pairIndex_coordinate_row_0 (b : Fin 25) : coordinate (pairIndex (0 : Fin 25) b) = (min 0 b.val, max 0 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_0_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_0_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_0_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_0_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_0_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_0_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_0_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_0_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_0_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_0_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_0_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_0_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_0_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_0_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_0_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_0_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_0_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_0_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_0_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_0_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_0_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_0_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_0_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_0_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_0_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_1 (b : Fin 25) : coordinate (pairIndex (1 : Fin 25) b) = (min 1 b.val, max 1 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_1_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_1_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_1_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_1_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_1_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_1_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_1_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_1_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_1_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_1_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_1_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_1_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_1_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_1_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_1_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_1_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_1_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_1_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_1_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_1_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_1_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_1_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_1_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_1_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_1_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_2 (b : Fin 25) : coordinate (pairIndex (2 : Fin 25) b) = (min 2 b.val, max 2 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_2_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_2_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_2_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_2_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_2_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_2_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_2_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_2_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_2_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_2_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_2_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_2_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_2_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_2_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_2_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_2_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_2_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_2_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_2_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_2_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_2_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_2_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_2_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_2_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_2_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_3 (b : Fin 25) : coordinate (pairIndex (3 : Fin 25) b) = (min 3 b.val, max 3 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_3_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_3_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_3_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_3_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_3_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_3_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_3_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_3_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_3_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_3_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_3_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_3_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_3_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_3_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_3_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_3_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_3_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_3_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_3_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_3_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_3_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_3_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_3_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_3_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_3_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_4 (b : Fin 25) : coordinate (pairIndex (4 : Fin 25) b) = (min 4 b.val, max 4 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_4_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_4_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_4_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_4_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_4_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_4_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_4_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_4_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_4_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_4_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_4_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_4_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_4_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_4_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_4_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_4_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_4_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_4_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_4_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_4_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_4_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_4_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_4_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_4_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_4_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_5 (b : Fin 25) : coordinate (pairIndex (5 : Fin 25) b) = (min 5 b.val, max 5 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_5_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_5_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_5_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_5_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_5_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_5_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_5_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_5_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_5_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_5_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_5_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_5_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_5_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_5_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_5_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_5_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_5_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_5_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_5_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_5_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_5_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_5_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_5_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_5_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_5_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_6 (b : Fin 25) : coordinate (pairIndex (6 : Fin 25) b) = (min 6 b.val, max 6 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_6_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_6_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_6_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_6_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_6_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_6_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_6_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_6_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_6_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_6_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_6_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_6_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_6_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_6_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_6_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_6_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_6_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_6_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_6_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_6_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_6_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_6_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_6_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_6_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_6_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_7 (b : Fin 25) : coordinate (pairIndex (7 : Fin 25) b) = (min 7 b.val, max 7 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_7_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_7_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_7_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_7_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_7_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_7_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_7_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_7_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_7_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_7_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_7_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_7_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_7_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_7_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_7_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_7_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_7_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_7_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_7_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_7_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_7_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_7_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_7_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_7_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_7_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_8 (b : Fin 25) : coordinate (pairIndex (8 : Fin 25) b) = (min 8 b.val, max 8 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_8_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_8_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_8_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_8_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_8_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_8_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_8_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_8_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_8_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_8_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_8_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_8_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_8_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_8_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_8_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_8_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_8_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_8_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_8_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_8_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_8_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_8_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_8_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_8_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_8_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_9 (b : Fin 25) : coordinate (pairIndex (9 : Fin 25) b) = (min 9 b.val, max 9 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_9_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_9_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_9_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_9_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_9_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_9_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_9_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_9_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_9_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_9_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_9_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_9_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_9_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_9_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_9_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_9_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_9_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_9_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_9_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_9_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_9_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_9_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_9_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_9_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_9_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_10 (b : Fin 25) : coordinate (pairIndex (10 : Fin 25) b) = (min 10 b.val, max 10 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_10_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_10_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_10_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_10_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_10_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_10_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_10_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_10_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_10_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_10_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_10_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_10_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_10_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_10_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_10_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_10_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_10_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_10_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_10_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_10_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_10_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_10_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_10_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_10_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_10_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_11 (b : Fin 25) : coordinate (pairIndex (11 : Fin 25) b) = (min 11 b.val, max 11 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_11_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_11_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_11_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_11_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_11_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_11_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_11_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_11_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_11_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_11_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_11_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_11_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_11_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_11_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_11_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_11_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_11_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_11_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_11_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_11_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_11_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_11_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_11_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_11_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_11_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_12 (b : Fin 25) : coordinate (pairIndex (12 : Fin 25) b) = (min 12 b.val, max 12 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_12_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_12_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_12_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_12_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_12_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_12_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_12_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_12_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_12_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_12_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_12_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_12_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_12_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_12_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_12_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_12_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_12_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_12_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_12_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_12_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_12_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_12_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_12_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_12_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_12_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_13 (b : Fin 25) : coordinate (pairIndex (13 : Fin 25) b) = (min 13 b.val, max 13 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_13_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_13_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_13_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_13_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_13_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_13_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_13_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_13_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_13_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_13_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_13_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_13_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_13_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_13_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_13_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_13_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_13_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_13_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_13_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_13_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_13_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_13_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_13_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_13_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_13_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_14 (b : Fin 25) : coordinate (pairIndex (14 : Fin 25) b) = (min 14 b.val, max 14 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_14_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_14_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_14_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_14_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_14_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_14_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_14_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_14_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_14_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_14_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_14_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_14_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_14_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_14_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_14_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_14_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_14_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_14_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_14_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_14_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_14_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_14_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_14_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_14_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_14_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_15 (b : Fin 25) : coordinate (pairIndex (15 : Fin 25) b) = (min 15 b.val, max 15 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_15_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_15_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_15_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_15_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_15_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_15_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_15_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_15_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_15_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_15_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_15_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_15_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_15_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_15_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_15_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_15_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_15_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_15_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_15_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_15_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_15_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_15_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_15_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_15_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_15_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_16 (b : Fin 25) : coordinate (pairIndex (16 : Fin 25) b) = (min 16 b.val, max 16 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_16_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_16_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_16_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_16_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_16_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_16_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_16_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_16_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_16_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_16_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_16_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_16_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_16_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_16_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_16_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_16_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_16_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_16_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_16_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_16_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_16_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_16_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_16_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_16_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_16_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_17 (b : Fin 25) : coordinate (pairIndex (17 : Fin 25) b) = (min 17 b.val, max 17 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_17_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_17_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_17_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_17_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_17_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_17_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_17_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_17_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_17_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_17_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_17_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_17_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_17_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_17_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_17_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_17_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_17_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_17_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_17_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_17_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_17_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_17_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_17_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_17_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_17_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_18 (b : Fin 25) : coordinate (pairIndex (18 : Fin 25) b) = (min 18 b.val, max 18 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_18_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_18_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_18_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_18_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_18_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_18_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_18_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_18_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_18_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_18_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_18_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_18_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_18_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_18_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_18_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_18_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_18_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_18_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_18_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_18_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_18_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_18_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_18_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_18_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_18_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_19 (b : Fin 25) : coordinate (pairIndex (19 : Fin 25) b) = (min 19 b.val, max 19 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_19_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_19_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_19_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_19_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_19_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_19_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_19_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_19_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_19_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_19_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_19_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_19_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_19_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_19_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_19_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_19_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_19_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_19_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_19_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_19_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_19_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_19_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_19_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_19_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_19_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_20 (b : Fin 25) : coordinate (pairIndex (20 : Fin 25) b) = (min 20 b.val, max 20 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_20_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_20_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_20_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_20_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_20_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_20_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_20_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_20_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_20_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_20_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_20_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_20_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_20_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_20_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_20_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_20_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_20_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_20_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_20_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_20_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_20_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_20_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_20_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_20_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_20_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_21 (b : Fin 25) : coordinate (pairIndex (21 : Fin 25) b) = (min 21 b.val, max 21 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_21_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_21_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_21_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_21_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_21_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_21_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_21_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_21_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_21_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_21_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_21_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_21_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_21_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_21_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_21_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_21_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_21_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_21_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_21_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_21_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_21_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_21_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_21_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_21_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_21_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_22 (b : Fin 25) : coordinate (pairIndex (22 : Fin 25) b) = (min 22 b.val, max 22 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_22_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_22_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_22_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_22_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_22_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_22_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_22_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_22_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_22_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_22_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_22_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_22_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_22_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_22_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_22_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_22_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_22_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_22_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_22_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_22_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_22_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_22_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_22_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_22_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_22_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_23 (b : Fin 25) : coordinate (pairIndex (23 : Fin 25) b) = (min 23 b.val, max 23 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_23_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_23_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_23_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_23_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_23_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_23_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_23_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_23_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_23_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_23_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_23_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_23_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_23_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_23_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_23_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_23_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_23_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_23_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_23_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_23_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_23_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_23_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_23_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_23_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_23_24
  | ⟨n + 25, h⟩ => omega
theorem pairIndex_coordinate_row_24 (b : Fin 25) : coordinate (pairIndex (24 : Fin 25) b) = (min 24 b.val, max 24 b.val) := by
  match b with
  | ⟨0, _⟩ => exact pairIndex_coordinate_24_0
  | ⟨1, _⟩ => exact pairIndex_coordinate_24_1
  | ⟨2, _⟩ => exact pairIndex_coordinate_24_2
  | ⟨3, _⟩ => exact pairIndex_coordinate_24_3
  | ⟨4, _⟩ => exact pairIndex_coordinate_24_4
  | ⟨5, _⟩ => exact pairIndex_coordinate_24_5
  | ⟨6, _⟩ => exact pairIndex_coordinate_24_6
  | ⟨7, _⟩ => exact pairIndex_coordinate_24_7
  | ⟨8, _⟩ => exact pairIndex_coordinate_24_8
  | ⟨9, _⟩ => exact pairIndex_coordinate_24_9
  | ⟨10, _⟩ => exact pairIndex_coordinate_24_10
  | ⟨11, _⟩ => exact pairIndex_coordinate_24_11
  | ⟨12, _⟩ => exact pairIndex_coordinate_24_12
  | ⟨13, _⟩ => exact pairIndex_coordinate_24_13
  | ⟨14, _⟩ => exact pairIndex_coordinate_24_14
  | ⟨15, _⟩ => exact pairIndex_coordinate_24_15
  | ⟨16, _⟩ => exact pairIndex_coordinate_24_16
  | ⟨17, _⟩ => exact pairIndex_coordinate_24_17
  | ⟨18, _⟩ => exact pairIndex_coordinate_24_18
  | ⟨19, _⟩ => exact pairIndex_coordinate_24_19
  | ⟨20, _⟩ => exact pairIndex_coordinate_24_20
  | ⟨21, _⟩ => exact pairIndex_coordinate_24_21
  | ⟨22, _⟩ => exact pairIndex_coordinate_24_22
  | ⟨23, _⟩ => exact pairIndex_coordinate_24_23
  | ⟨24, _⟩ => exact pairIndex_coordinate_24_24
  | ⟨n + 25, h⟩ => omega

theorem pairIndex_coordinate (a b : Fin 25) : coordinate (pairIndex a b) = (min a.val b.val, max a.val b.val) := by
  match a with
  | ⟨0, _⟩ => exact pairIndex_coordinate_row_0 b
  | ⟨1, _⟩ => exact pairIndex_coordinate_row_1 b
  | ⟨2, _⟩ => exact pairIndex_coordinate_row_2 b
  | ⟨3, _⟩ => exact pairIndex_coordinate_row_3 b
  | ⟨4, _⟩ => exact pairIndex_coordinate_row_4 b
  | ⟨5, _⟩ => exact pairIndex_coordinate_row_5 b
  | ⟨6, _⟩ => exact pairIndex_coordinate_row_6 b
  | ⟨7, _⟩ => exact pairIndex_coordinate_row_7 b
  | ⟨8, _⟩ => exact pairIndex_coordinate_row_8 b
  | ⟨9, _⟩ => exact pairIndex_coordinate_row_9 b
  | ⟨10, _⟩ => exact pairIndex_coordinate_row_10 b
  | ⟨11, _⟩ => exact pairIndex_coordinate_row_11 b
  | ⟨12, _⟩ => exact pairIndex_coordinate_row_12 b
  | ⟨13, _⟩ => exact pairIndex_coordinate_row_13 b
  | ⟨14, _⟩ => exact pairIndex_coordinate_row_14 b
  | ⟨15, _⟩ => exact pairIndex_coordinate_row_15 b
  | ⟨16, _⟩ => exact pairIndex_coordinate_row_16 b
  | ⟨17, _⟩ => exact pairIndex_coordinate_row_17 b
  | ⟨18, _⟩ => exact pairIndex_coordinate_row_18 b
  | ⟨19, _⟩ => exact pairIndex_coordinate_row_19 b
  | ⟨20, _⟩ => exact pairIndex_coordinate_row_20 b
  | ⟨21, _⟩ => exact pairIndex_coordinate_row_21 b
  | ⟨22, _⟩ => exact pairIndex_coordinate_row_22 b
  | ⟨23, _⟩ => exact pairIndex_coordinate_row_23 b
  | ⟨24, _⟩ => exact pairIndex_coordinate_row_24 b
  | ⟨n + 25, h⟩ => omega

theorem coordinate_pairIndex_0 : pairIndex ⟨(coordinate (0 : Coord)).1, by have h := coordinate_bounds (0 : Coord); omega⟩ ⟨(coordinate (0 : Coord)).2, (coordinate_bounds (0 : Coord)).2⟩ = (0 : Coord) := by
  change pairIndex (0 : Fin 25) (0 : Fin 25) = (0 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_1 : pairIndex ⟨(coordinate (1 : Coord)).1, by have h := coordinate_bounds (1 : Coord); omega⟩ ⟨(coordinate (1 : Coord)).2, (coordinate_bounds (1 : Coord)).2⟩ = (1 : Coord) := by
  change pairIndex (0 : Fin 25) (1 : Fin 25) = (1 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_2 : pairIndex ⟨(coordinate (2 : Coord)).1, by have h := coordinate_bounds (2 : Coord); omega⟩ ⟨(coordinate (2 : Coord)).2, (coordinate_bounds (2 : Coord)).2⟩ = (2 : Coord) := by
  change pairIndex (0 : Fin 25) (2 : Fin 25) = (2 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_3 : pairIndex ⟨(coordinate (3 : Coord)).1, by have h := coordinate_bounds (3 : Coord); omega⟩ ⟨(coordinate (3 : Coord)).2, (coordinate_bounds (3 : Coord)).2⟩ = (3 : Coord) := by
  change pairIndex (0 : Fin 25) (3 : Fin 25) = (3 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_4 : pairIndex ⟨(coordinate (4 : Coord)).1, by have h := coordinate_bounds (4 : Coord); omega⟩ ⟨(coordinate (4 : Coord)).2, (coordinate_bounds (4 : Coord)).2⟩ = (4 : Coord) := by
  change pairIndex (0 : Fin 25) (4 : Fin 25) = (4 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_5 : pairIndex ⟨(coordinate (5 : Coord)).1, by have h := coordinate_bounds (5 : Coord); omega⟩ ⟨(coordinate (5 : Coord)).2, (coordinate_bounds (5 : Coord)).2⟩ = (5 : Coord) := by
  change pairIndex (0 : Fin 25) (5 : Fin 25) = (5 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_6 : pairIndex ⟨(coordinate (6 : Coord)).1, by have h := coordinate_bounds (6 : Coord); omega⟩ ⟨(coordinate (6 : Coord)).2, (coordinate_bounds (6 : Coord)).2⟩ = (6 : Coord) := by
  change pairIndex (0 : Fin 25) (6 : Fin 25) = (6 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_7 : pairIndex ⟨(coordinate (7 : Coord)).1, by have h := coordinate_bounds (7 : Coord); omega⟩ ⟨(coordinate (7 : Coord)).2, (coordinate_bounds (7 : Coord)).2⟩ = (7 : Coord) := by
  change pairIndex (0 : Fin 25) (7 : Fin 25) = (7 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_8 : pairIndex ⟨(coordinate (8 : Coord)).1, by have h := coordinate_bounds (8 : Coord); omega⟩ ⟨(coordinate (8 : Coord)).2, (coordinate_bounds (8 : Coord)).2⟩ = (8 : Coord) := by
  change pairIndex (0 : Fin 25) (8 : Fin 25) = (8 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_9 : pairIndex ⟨(coordinate (9 : Coord)).1, by have h := coordinate_bounds (9 : Coord); omega⟩ ⟨(coordinate (9 : Coord)).2, (coordinate_bounds (9 : Coord)).2⟩ = (9 : Coord) := by
  change pairIndex (0 : Fin 25) (9 : Fin 25) = (9 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_10 : pairIndex ⟨(coordinate (10 : Coord)).1, by have h := coordinate_bounds (10 : Coord); omega⟩ ⟨(coordinate (10 : Coord)).2, (coordinate_bounds (10 : Coord)).2⟩ = (10 : Coord) := by
  change pairIndex (0 : Fin 25) (10 : Fin 25) = (10 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_11 : pairIndex ⟨(coordinate (11 : Coord)).1, by have h := coordinate_bounds (11 : Coord); omega⟩ ⟨(coordinate (11 : Coord)).2, (coordinate_bounds (11 : Coord)).2⟩ = (11 : Coord) := by
  change pairIndex (0 : Fin 25) (11 : Fin 25) = (11 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_12 : pairIndex ⟨(coordinate (12 : Coord)).1, by have h := coordinate_bounds (12 : Coord); omega⟩ ⟨(coordinate (12 : Coord)).2, (coordinate_bounds (12 : Coord)).2⟩ = (12 : Coord) := by
  change pairIndex (0 : Fin 25) (12 : Fin 25) = (12 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_13 : pairIndex ⟨(coordinate (13 : Coord)).1, by have h := coordinate_bounds (13 : Coord); omega⟩ ⟨(coordinate (13 : Coord)).2, (coordinate_bounds (13 : Coord)).2⟩ = (13 : Coord) := by
  change pairIndex (0 : Fin 25) (13 : Fin 25) = (13 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_14 : pairIndex ⟨(coordinate (14 : Coord)).1, by have h := coordinate_bounds (14 : Coord); omega⟩ ⟨(coordinate (14 : Coord)).2, (coordinate_bounds (14 : Coord)).2⟩ = (14 : Coord) := by
  change pairIndex (0 : Fin 25) (14 : Fin 25) = (14 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_15 : pairIndex ⟨(coordinate (15 : Coord)).1, by have h := coordinate_bounds (15 : Coord); omega⟩ ⟨(coordinate (15 : Coord)).2, (coordinate_bounds (15 : Coord)).2⟩ = (15 : Coord) := by
  change pairIndex (0 : Fin 25) (15 : Fin 25) = (15 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_16 : pairIndex ⟨(coordinate (16 : Coord)).1, by have h := coordinate_bounds (16 : Coord); omega⟩ ⟨(coordinate (16 : Coord)).2, (coordinate_bounds (16 : Coord)).2⟩ = (16 : Coord) := by
  change pairIndex (0 : Fin 25) (16 : Fin 25) = (16 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_17 : pairIndex ⟨(coordinate (17 : Coord)).1, by have h := coordinate_bounds (17 : Coord); omega⟩ ⟨(coordinate (17 : Coord)).2, (coordinate_bounds (17 : Coord)).2⟩ = (17 : Coord) := by
  change pairIndex (0 : Fin 25) (17 : Fin 25) = (17 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_18 : pairIndex ⟨(coordinate (18 : Coord)).1, by have h := coordinate_bounds (18 : Coord); omega⟩ ⟨(coordinate (18 : Coord)).2, (coordinate_bounds (18 : Coord)).2⟩ = (18 : Coord) := by
  change pairIndex (0 : Fin 25) (18 : Fin 25) = (18 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_19 : pairIndex ⟨(coordinate (19 : Coord)).1, by have h := coordinate_bounds (19 : Coord); omega⟩ ⟨(coordinate (19 : Coord)).2, (coordinate_bounds (19 : Coord)).2⟩ = (19 : Coord) := by
  change pairIndex (0 : Fin 25) (19 : Fin 25) = (19 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_20 : pairIndex ⟨(coordinate (20 : Coord)).1, by have h := coordinate_bounds (20 : Coord); omega⟩ ⟨(coordinate (20 : Coord)).2, (coordinate_bounds (20 : Coord)).2⟩ = (20 : Coord) := by
  change pairIndex (0 : Fin 25) (20 : Fin 25) = (20 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_21 : pairIndex ⟨(coordinate (21 : Coord)).1, by have h := coordinate_bounds (21 : Coord); omega⟩ ⟨(coordinate (21 : Coord)).2, (coordinate_bounds (21 : Coord)).2⟩ = (21 : Coord) := by
  change pairIndex (0 : Fin 25) (21 : Fin 25) = (21 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_22 : pairIndex ⟨(coordinate (22 : Coord)).1, by have h := coordinate_bounds (22 : Coord); omega⟩ ⟨(coordinate (22 : Coord)).2, (coordinate_bounds (22 : Coord)).2⟩ = (22 : Coord) := by
  change pairIndex (0 : Fin 25) (22 : Fin 25) = (22 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_23 : pairIndex ⟨(coordinate (23 : Coord)).1, by have h := coordinate_bounds (23 : Coord); omega⟩ ⟨(coordinate (23 : Coord)).2, (coordinate_bounds (23 : Coord)).2⟩ = (23 : Coord) := by
  change pairIndex (0 : Fin 25) (23 : Fin 25) = (23 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_24 : pairIndex ⟨(coordinate (24 : Coord)).1, by have h := coordinate_bounds (24 : Coord); omega⟩ ⟨(coordinate (24 : Coord)).2, (coordinate_bounds (24 : Coord)).2⟩ = (24 : Coord) := by
  change pairIndex (0 : Fin 25) (24 : Fin 25) = (24 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_25 : pairIndex ⟨(coordinate (25 : Coord)).1, by have h := coordinate_bounds (25 : Coord); omega⟩ ⟨(coordinate (25 : Coord)).2, (coordinate_bounds (25 : Coord)).2⟩ = (25 : Coord) := by
  change pairIndex (1 : Fin 25) (1 : Fin 25) = (25 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_26 : pairIndex ⟨(coordinate (26 : Coord)).1, by have h := coordinate_bounds (26 : Coord); omega⟩ ⟨(coordinate (26 : Coord)).2, (coordinate_bounds (26 : Coord)).2⟩ = (26 : Coord) := by
  change pairIndex (1 : Fin 25) (2 : Fin 25) = (26 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_27 : pairIndex ⟨(coordinate (27 : Coord)).1, by have h := coordinate_bounds (27 : Coord); omega⟩ ⟨(coordinate (27 : Coord)).2, (coordinate_bounds (27 : Coord)).2⟩ = (27 : Coord) := by
  change pairIndex (1 : Fin 25) (3 : Fin 25) = (27 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_28 : pairIndex ⟨(coordinate (28 : Coord)).1, by have h := coordinate_bounds (28 : Coord); omega⟩ ⟨(coordinate (28 : Coord)).2, (coordinate_bounds (28 : Coord)).2⟩ = (28 : Coord) := by
  change pairIndex (1 : Fin 25) (4 : Fin 25) = (28 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_29 : pairIndex ⟨(coordinate (29 : Coord)).1, by have h := coordinate_bounds (29 : Coord); omega⟩ ⟨(coordinate (29 : Coord)).2, (coordinate_bounds (29 : Coord)).2⟩ = (29 : Coord) := by
  change pairIndex (1 : Fin 25) (5 : Fin 25) = (29 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_30 : pairIndex ⟨(coordinate (30 : Coord)).1, by have h := coordinate_bounds (30 : Coord); omega⟩ ⟨(coordinate (30 : Coord)).2, (coordinate_bounds (30 : Coord)).2⟩ = (30 : Coord) := by
  change pairIndex (1 : Fin 25) (6 : Fin 25) = (30 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_31 : pairIndex ⟨(coordinate (31 : Coord)).1, by have h := coordinate_bounds (31 : Coord); omega⟩ ⟨(coordinate (31 : Coord)).2, (coordinate_bounds (31 : Coord)).2⟩ = (31 : Coord) := by
  change pairIndex (1 : Fin 25) (7 : Fin 25) = (31 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_32 : pairIndex ⟨(coordinate (32 : Coord)).1, by have h := coordinate_bounds (32 : Coord); omega⟩ ⟨(coordinate (32 : Coord)).2, (coordinate_bounds (32 : Coord)).2⟩ = (32 : Coord) := by
  change pairIndex (1 : Fin 25) (8 : Fin 25) = (32 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_33 : pairIndex ⟨(coordinate (33 : Coord)).1, by have h := coordinate_bounds (33 : Coord); omega⟩ ⟨(coordinate (33 : Coord)).2, (coordinate_bounds (33 : Coord)).2⟩ = (33 : Coord) := by
  change pairIndex (1 : Fin 25) (9 : Fin 25) = (33 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_34 : pairIndex ⟨(coordinate (34 : Coord)).1, by have h := coordinate_bounds (34 : Coord); omega⟩ ⟨(coordinate (34 : Coord)).2, (coordinate_bounds (34 : Coord)).2⟩ = (34 : Coord) := by
  change pairIndex (1 : Fin 25) (10 : Fin 25) = (34 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_35 : pairIndex ⟨(coordinate (35 : Coord)).1, by have h := coordinate_bounds (35 : Coord); omega⟩ ⟨(coordinate (35 : Coord)).2, (coordinate_bounds (35 : Coord)).2⟩ = (35 : Coord) := by
  change pairIndex (1 : Fin 25) (11 : Fin 25) = (35 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_36 : pairIndex ⟨(coordinate (36 : Coord)).1, by have h := coordinate_bounds (36 : Coord); omega⟩ ⟨(coordinate (36 : Coord)).2, (coordinate_bounds (36 : Coord)).2⟩ = (36 : Coord) := by
  change pairIndex (1 : Fin 25) (12 : Fin 25) = (36 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_37 : pairIndex ⟨(coordinate (37 : Coord)).1, by have h := coordinate_bounds (37 : Coord); omega⟩ ⟨(coordinate (37 : Coord)).2, (coordinate_bounds (37 : Coord)).2⟩ = (37 : Coord) := by
  change pairIndex (1 : Fin 25) (13 : Fin 25) = (37 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_38 : pairIndex ⟨(coordinate (38 : Coord)).1, by have h := coordinate_bounds (38 : Coord); omega⟩ ⟨(coordinate (38 : Coord)).2, (coordinate_bounds (38 : Coord)).2⟩ = (38 : Coord) := by
  change pairIndex (1 : Fin 25) (14 : Fin 25) = (38 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_39 : pairIndex ⟨(coordinate (39 : Coord)).1, by have h := coordinate_bounds (39 : Coord); omega⟩ ⟨(coordinate (39 : Coord)).2, (coordinate_bounds (39 : Coord)).2⟩ = (39 : Coord) := by
  change pairIndex (1 : Fin 25) (15 : Fin 25) = (39 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_40 : pairIndex ⟨(coordinate (40 : Coord)).1, by have h := coordinate_bounds (40 : Coord); omega⟩ ⟨(coordinate (40 : Coord)).2, (coordinate_bounds (40 : Coord)).2⟩ = (40 : Coord) := by
  change pairIndex (1 : Fin 25) (16 : Fin 25) = (40 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_41 : pairIndex ⟨(coordinate (41 : Coord)).1, by have h := coordinate_bounds (41 : Coord); omega⟩ ⟨(coordinate (41 : Coord)).2, (coordinate_bounds (41 : Coord)).2⟩ = (41 : Coord) := by
  change pairIndex (1 : Fin 25) (17 : Fin 25) = (41 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_42 : pairIndex ⟨(coordinate (42 : Coord)).1, by have h := coordinate_bounds (42 : Coord); omega⟩ ⟨(coordinate (42 : Coord)).2, (coordinate_bounds (42 : Coord)).2⟩ = (42 : Coord) := by
  change pairIndex (1 : Fin 25) (18 : Fin 25) = (42 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_43 : pairIndex ⟨(coordinate (43 : Coord)).1, by have h := coordinate_bounds (43 : Coord); omega⟩ ⟨(coordinate (43 : Coord)).2, (coordinate_bounds (43 : Coord)).2⟩ = (43 : Coord) := by
  change pairIndex (1 : Fin 25) (19 : Fin 25) = (43 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_44 : pairIndex ⟨(coordinate (44 : Coord)).1, by have h := coordinate_bounds (44 : Coord); omega⟩ ⟨(coordinate (44 : Coord)).2, (coordinate_bounds (44 : Coord)).2⟩ = (44 : Coord) := by
  change pairIndex (1 : Fin 25) (20 : Fin 25) = (44 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_45 : pairIndex ⟨(coordinate (45 : Coord)).1, by have h := coordinate_bounds (45 : Coord); omega⟩ ⟨(coordinate (45 : Coord)).2, (coordinate_bounds (45 : Coord)).2⟩ = (45 : Coord) := by
  change pairIndex (1 : Fin 25) (21 : Fin 25) = (45 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_46 : pairIndex ⟨(coordinate (46 : Coord)).1, by have h := coordinate_bounds (46 : Coord); omega⟩ ⟨(coordinate (46 : Coord)).2, (coordinate_bounds (46 : Coord)).2⟩ = (46 : Coord) := by
  change pairIndex (1 : Fin 25) (22 : Fin 25) = (46 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_47 : pairIndex ⟨(coordinate (47 : Coord)).1, by have h := coordinate_bounds (47 : Coord); omega⟩ ⟨(coordinate (47 : Coord)).2, (coordinate_bounds (47 : Coord)).2⟩ = (47 : Coord) := by
  change pairIndex (1 : Fin 25) (23 : Fin 25) = (47 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_48 : pairIndex ⟨(coordinate (48 : Coord)).1, by have h := coordinate_bounds (48 : Coord); omega⟩ ⟨(coordinate (48 : Coord)).2, (coordinate_bounds (48 : Coord)).2⟩ = (48 : Coord) := by
  change pairIndex (1 : Fin 25) (24 : Fin 25) = (48 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_49 : pairIndex ⟨(coordinate (49 : Coord)).1, by have h := coordinate_bounds (49 : Coord); omega⟩ ⟨(coordinate (49 : Coord)).2, (coordinate_bounds (49 : Coord)).2⟩ = (49 : Coord) := by
  change pairIndex (2 : Fin 25) (2 : Fin 25) = (49 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_50 : pairIndex ⟨(coordinate (50 : Coord)).1, by have h := coordinate_bounds (50 : Coord); omega⟩ ⟨(coordinate (50 : Coord)).2, (coordinate_bounds (50 : Coord)).2⟩ = (50 : Coord) := by
  change pairIndex (2 : Fin 25) (3 : Fin 25) = (50 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_51 : pairIndex ⟨(coordinate (51 : Coord)).1, by have h := coordinate_bounds (51 : Coord); omega⟩ ⟨(coordinate (51 : Coord)).2, (coordinate_bounds (51 : Coord)).2⟩ = (51 : Coord) := by
  change pairIndex (2 : Fin 25) (4 : Fin 25) = (51 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_52 : pairIndex ⟨(coordinate (52 : Coord)).1, by have h := coordinate_bounds (52 : Coord); omega⟩ ⟨(coordinate (52 : Coord)).2, (coordinate_bounds (52 : Coord)).2⟩ = (52 : Coord) := by
  change pairIndex (2 : Fin 25) (5 : Fin 25) = (52 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_53 : pairIndex ⟨(coordinate (53 : Coord)).1, by have h := coordinate_bounds (53 : Coord); omega⟩ ⟨(coordinate (53 : Coord)).2, (coordinate_bounds (53 : Coord)).2⟩ = (53 : Coord) := by
  change pairIndex (2 : Fin 25) (6 : Fin 25) = (53 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_54 : pairIndex ⟨(coordinate (54 : Coord)).1, by have h := coordinate_bounds (54 : Coord); omega⟩ ⟨(coordinate (54 : Coord)).2, (coordinate_bounds (54 : Coord)).2⟩ = (54 : Coord) := by
  change pairIndex (2 : Fin 25) (7 : Fin 25) = (54 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_55 : pairIndex ⟨(coordinate (55 : Coord)).1, by have h := coordinate_bounds (55 : Coord); omega⟩ ⟨(coordinate (55 : Coord)).2, (coordinate_bounds (55 : Coord)).2⟩ = (55 : Coord) := by
  change pairIndex (2 : Fin 25) (8 : Fin 25) = (55 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_56 : pairIndex ⟨(coordinate (56 : Coord)).1, by have h := coordinate_bounds (56 : Coord); omega⟩ ⟨(coordinate (56 : Coord)).2, (coordinate_bounds (56 : Coord)).2⟩ = (56 : Coord) := by
  change pairIndex (2 : Fin 25) (9 : Fin 25) = (56 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_57 : pairIndex ⟨(coordinate (57 : Coord)).1, by have h := coordinate_bounds (57 : Coord); omega⟩ ⟨(coordinate (57 : Coord)).2, (coordinate_bounds (57 : Coord)).2⟩ = (57 : Coord) := by
  change pairIndex (2 : Fin 25) (10 : Fin 25) = (57 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_58 : pairIndex ⟨(coordinate (58 : Coord)).1, by have h := coordinate_bounds (58 : Coord); omega⟩ ⟨(coordinate (58 : Coord)).2, (coordinate_bounds (58 : Coord)).2⟩ = (58 : Coord) := by
  change pairIndex (2 : Fin 25) (11 : Fin 25) = (58 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_59 : pairIndex ⟨(coordinate (59 : Coord)).1, by have h := coordinate_bounds (59 : Coord); omega⟩ ⟨(coordinate (59 : Coord)).2, (coordinate_bounds (59 : Coord)).2⟩ = (59 : Coord) := by
  change pairIndex (2 : Fin 25) (12 : Fin 25) = (59 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_60 : pairIndex ⟨(coordinate (60 : Coord)).1, by have h := coordinate_bounds (60 : Coord); omega⟩ ⟨(coordinate (60 : Coord)).2, (coordinate_bounds (60 : Coord)).2⟩ = (60 : Coord) := by
  change pairIndex (2 : Fin 25) (13 : Fin 25) = (60 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_61 : pairIndex ⟨(coordinate (61 : Coord)).1, by have h := coordinate_bounds (61 : Coord); omega⟩ ⟨(coordinate (61 : Coord)).2, (coordinate_bounds (61 : Coord)).2⟩ = (61 : Coord) := by
  change pairIndex (2 : Fin 25) (14 : Fin 25) = (61 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_62 : pairIndex ⟨(coordinate (62 : Coord)).1, by have h := coordinate_bounds (62 : Coord); omega⟩ ⟨(coordinate (62 : Coord)).2, (coordinate_bounds (62 : Coord)).2⟩ = (62 : Coord) := by
  change pairIndex (2 : Fin 25) (15 : Fin 25) = (62 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_63 : pairIndex ⟨(coordinate (63 : Coord)).1, by have h := coordinate_bounds (63 : Coord); omega⟩ ⟨(coordinate (63 : Coord)).2, (coordinate_bounds (63 : Coord)).2⟩ = (63 : Coord) := by
  change pairIndex (2 : Fin 25) (16 : Fin 25) = (63 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_64 : pairIndex ⟨(coordinate (64 : Coord)).1, by have h := coordinate_bounds (64 : Coord); omega⟩ ⟨(coordinate (64 : Coord)).2, (coordinate_bounds (64 : Coord)).2⟩ = (64 : Coord) := by
  change pairIndex (2 : Fin 25) (17 : Fin 25) = (64 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_65 : pairIndex ⟨(coordinate (65 : Coord)).1, by have h := coordinate_bounds (65 : Coord); omega⟩ ⟨(coordinate (65 : Coord)).2, (coordinate_bounds (65 : Coord)).2⟩ = (65 : Coord) := by
  change pairIndex (2 : Fin 25) (18 : Fin 25) = (65 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_66 : pairIndex ⟨(coordinate (66 : Coord)).1, by have h := coordinate_bounds (66 : Coord); omega⟩ ⟨(coordinate (66 : Coord)).2, (coordinate_bounds (66 : Coord)).2⟩ = (66 : Coord) := by
  change pairIndex (2 : Fin 25) (19 : Fin 25) = (66 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_67 : pairIndex ⟨(coordinate (67 : Coord)).1, by have h := coordinate_bounds (67 : Coord); omega⟩ ⟨(coordinate (67 : Coord)).2, (coordinate_bounds (67 : Coord)).2⟩ = (67 : Coord) := by
  change pairIndex (2 : Fin 25) (20 : Fin 25) = (67 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_68 : pairIndex ⟨(coordinate (68 : Coord)).1, by have h := coordinate_bounds (68 : Coord); omega⟩ ⟨(coordinate (68 : Coord)).2, (coordinate_bounds (68 : Coord)).2⟩ = (68 : Coord) := by
  change pairIndex (2 : Fin 25) (21 : Fin 25) = (68 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_69 : pairIndex ⟨(coordinate (69 : Coord)).1, by have h := coordinate_bounds (69 : Coord); omega⟩ ⟨(coordinate (69 : Coord)).2, (coordinate_bounds (69 : Coord)).2⟩ = (69 : Coord) := by
  change pairIndex (2 : Fin 25) (22 : Fin 25) = (69 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_70 : pairIndex ⟨(coordinate (70 : Coord)).1, by have h := coordinate_bounds (70 : Coord); omega⟩ ⟨(coordinate (70 : Coord)).2, (coordinate_bounds (70 : Coord)).2⟩ = (70 : Coord) := by
  change pairIndex (2 : Fin 25) (23 : Fin 25) = (70 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_71 : pairIndex ⟨(coordinate (71 : Coord)).1, by have h := coordinate_bounds (71 : Coord); omega⟩ ⟨(coordinate (71 : Coord)).2, (coordinate_bounds (71 : Coord)).2⟩ = (71 : Coord) := by
  change pairIndex (2 : Fin 25) (24 : Fin 25) = (71 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_72 : pairIndex ⟨(coordinate (72 : Coord)).1, by have h := coordinate_bounds (72 : Coord); omega⟩ ⟨(coordinate (72 : Coord)).2, (coordinate_bounds (72 : Coord)).2⟩ = (72 : Coord) := by
  change pairIndex (3 : Fin 25) (3 : Fin 25) = (72 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_73 : pairIndex ⟨(coordinate (73 : Coord)).1, by have h := coordinate_bounds (73 : Coord); omega⟩ ⟨(coordinate (73 : Coord)).2, (coordinate_bounds (73 : Coord)).2⟩ = (73 : Coord) := by
  change pairIndex (3 : Fin 25) (4 : Fin 25) = (73 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_74 : pairIndex ⟨(coordinate (74 : Coord)).1, by have h := coordinate_bounds (74 : Coord); omega⟩ ⟨(coordinate (74 : Coord)).2, (coordinate_bounds (74 : Coord)).2⟩ = (74 : Coord) := by
  change pairIndex (3 : Fin 25) (5 : Fin 25) = (74 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_75 : pairIndex ⟨(coordinate (75 : Coord)).1, by have h := coordinate_bounds (75 : Coord); omega⟩ ⟨(coordinate (75 : Coord)).2, (coordinate_bounds (75 : Coord)).2⟩ = (75 : Coord) := by
  change pairIndex (3 : Fin 25) (6 : Fin 25) = (75 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_76 : pairIndex ⟨(coordinate (76 : Coord)).1, by have h := coordinate_bounds (76 : Coord); omega⟩ ⟨(coordinate (76 : Coord)).2, (coordinate_bounds (76 : Coord)).2⟩ = (76 : Coord) := by
  change pairIndex (3 : Fin 25) (7 : Fin 25) = (76 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_77 : pairIndex ⟨(coordinate (77 : Coord)).1, by have h := coordinate_bounds (77 : Coord); omega⟩ ⟨(coordinate (77 : Coord)).2, (coordinate_bounds (77 : Coord)).2⟩ = (77 : Coord) := by
  change pairIndex (3 : Fin 25) (8 : Fin 25) = (77 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_78 : pairIndex ⟨(coordinate (78 : Coord)).1, by have h := coordinate_bounds (78 : Coord); omega⟩ ⟨(coordinate (78 : Coord)).2, (coordinate_bounds (78 : Coord)).2⟩ = (78 : Coord) := by
  change pairIndex (3 : Fin 25) (9 : Fin 25) = (78 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_79 : pairIndex ⟨(coordinate (79 : Coord)).1, by have h := coordinate_bounds (79 : Coord); omega⟩ ⟨(coordinate (79 : Coord)).2, (coordinate_bounds (79 : Coord)).2⟩ = (79 : Coord) := by
  change pairIndex (3 : Fin 25) (10 : Fin 25) = (79 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_80 : pairIndex ⟨(coordinate (80 : Coord)).1, by have h := coordinate_bounds (80 : Coord); omega⟩ ⟨(coordinate (80 : Coord)).2, (coordinate_bounds (80 : Coord)).2⟩ = (80 : Coord) := by
  change pairIndex (3 : Fin 25) (11 : Fin 25) = (80 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_81 : pairIndex ⟨(coordinate (81 : Coord)).1, by have h := coordinate_bounds (81 : Coord); omega⟩ ⟨(coordinate (81 : Coord)).2, (coordinate_bounds (81 : Coord)).2⟩ = (81 : Coord) := by
  change pairIndex (3 : Fin 25) (12 : Fin 25) = (81 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_82 : pairIndex ⟨(coordinate (82 : Coord)).1, by have h := coordinate_bounds (82 : Coord); omega⟩ ⟨(coordinate (82 : Coord)).2, (coordinate_bounds (82 : Coord)).2⟩ = (82 : Coord) := by
  change pairIndex (3 : Fin 25) (13 : Fin 25) = (82 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_83 : pairIndex ⟨(coordinate (83 : Coord)).1, by have h := coordinate_bounds (83 : Coord); omega⟩ ⟨(coordinate (83 : Coord)).2, (coordinate_bounds (83 : Coord)).2⟩ = (83 : Coord) := by
  change pairIndex (3 : Fin 25) (14 : Fin 25) = (83 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_84 : pairIndex ⟨(coordinate (84 : Coord)).1, by have h := coordinate_bounds (84 : Coord); omega⟩ ⟨(coordinate (84 : Coord)).2, (coordinate_bounds (84 : Coord)).2⟩ = (84 : Coord) := by
  change pairIndex (3 : Fin 25) (15 : Fin 25) = (84 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_85 : pairIndex ⟨(coordinate (85 : Coord)).1, by have h := coordinate_bounds (85 : Coord); omega⟩ ⟨(coordinate (85 : Coord)).2, (coordinate_bounds (85 : Coord)).2⟩ = (85 : Coord) := by
  change pairIndex (3 : Fin 25) (16 : Fin 25) = (85 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_86 : pairIndex ⟨(coordinate (86 : Coord)).1, by have h := coordinate_bounds (86 : Coord); omega⟩ ⟨(coordinate (86 : Coord)).2, (coordinate_bounds (86 : Coord)).2⟩ = (86 : Coord) := by
  change pairIndex (3 : Fin 25) (17 : Fin 25) = (86 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_87 : pairIndex ⟨(coordinate (87 : Coord)).1, by have h := coordinate_bounds (87 : Coord); omega⟩ ⟨(coordinate (87 : Coord)).2, (coordinate_bounds (87 : Coord)).2⟩ = (87 : Coord) := by
  change pairIndex (3 : Fin 25) (18 : Fin 25) = (87 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_88 : pairIndex ⟨(coordinate (88 : Coord)).1, by have h := coordinate_bounds (88 : Coord); omega⟩ ⟨(coordinate (88 : Coord)).2, (coordinate_bounds (88 : Coord)).2⟩ = (88 : Coord) := by
  change pairIndex (3 : Fin 25) (19 : Fin 25) = (88 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_89 : pairIndex ⟨(coordinate (89 : Coord)).1, by have h := coordinate_bounds (89 : Coord); omega⟩ ⟨(coordinate (89 : Coord)).2, (coordinate_bounds (89 : Coord)).2⟩ = (89 : Coord) := by
  change pairIndex (3 : Fin 25) (20 : Fin 25) = (89 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_90 : pairIndex ⟨(coordinate (90 : Coord)).1, by have h := coordinate_bounds (90 : Coord); omega⟩ ⟨(coordinate (90 : Coord)).2, (coordinate_bounds (90 : Coord)).2⟩ = (90 : Coord) := by
  change pairIndex (3 : Fin 25) (21 : Fin 25) = (90 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_91 : pairIndex ⟨(coordinate (91 : Coord)).1, by have h := coordinate_bounds (91 : Coord); omega⟩ ⟨(coordinate (91 : Coord)).2, (coordinate_bounds (91 : Coord)).2⟩ = (91 : Coord) := by
  change pairIndex (3 : Fin 25) (22 : Fin 25) = (91 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_92 : pairIndex ⟨(coordinate (92 : Coord)).1, by have h := coordinate_bounds (92 : Coord); omega⟩ ⟨(coordinate (92 : Coord)).2, (coordinate_bounds (92 : Coord)).2⟩ = (92 : Coord) := by
  change pairIndex (3 : Fin 25) (23 : Fin 25) = (92 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_93 : pairIndex ⟨(coordinate (93 : Coord)).1, by have h := coordinate_bounds (93 : Coord); omega⟩ ⟨(coordinate (93 : Coord)).2, (coordinate_bounds (93 : Coord)).2⟩ = (93 : Coord) := by
  change pairIndex (3 : Fin 25) (24 : Fin 25) = (93 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_94 : pairIndex ⟨(coordinate (94 : Coord)).1, by have h := coordinate_bounds (94 : Coord); omega⟩ ⟨(coordinate (94 : Coord)).2, (coordinate_bounds (94 : Coord)).2⟩ = (94 : Coord) := by
  change pairIndex (4 : Fin 25) (4 : Fin 25) = (94 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_95 : pairIndex ⟨(coordinate (95 : Coord)).1, by have h := coordinate_bounds (95 : Coord); omega⟩ ⟨(coordinate (95 : Coord)).2, (coordinate_bounds (95 : Coord)).2⟩ = (95 : Coord) := by
  change pairIndex (4 : Fin 25) (5 : Fin 25) = (95 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_96 : pairIndex ⟨(coordinate (96 : Coord)).1, by have h := coordinate_bounds (96 : Coord); omega⟩ ⟨(coordinate (96 : Coord)).2, (coordinate_bounds (96 : Coord)).2⟩ = (96 : Coord) := by
  change pairIndex (4 : Fin 25) (6 : Fin 25) = (96 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_97 : pairIndex ⟨(coordinate (97 : Coord)).1, by have h := coordinate_bounds (97 : Coord); omega⟩ ⟨(coordinate (97 : Coord)).2, (coordinate_bounds (97 : Coord)).2⟩ = (97 : Coord) := by
  change pairIndex (4 : Fin 25) (7 : Fin 25) = (97 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_98 : pairIndex ⟨(coordinate (98 : Coord)).1, by have h := coordinate_bounds (98 : Coord); omega⟩ ⟨(coordinate (98 : Coord)).2, (coordinate_bounds (98 : Coord)).2⟩ = (98 : Coord) := by
  change pairIndex (4 : Fin 25) (8 : Fin 25) = (98 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_99 : pairIndex ⟨(coordinate (99 : Coord)).1, by have h := coordinate_bounds (99 : Coord); omega⟩ ⟨(coordinate (99 : Coord)).2, (coordinate_bounds (99 : Coord)).2⟩ = (99 : Coord) := by
  change pairIndex (4 : Fin 25) (9 : Fin 25) = (99 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_100 : pairIndex ⟨(coordinate (100 : Coord)).1, by have h := coordinate_bounds (100 : Coord); omega⟩ ⟨(coordinate (100 : Coord)).2, (coordinate_bounds (100 : Coord)).2⟩ = (100 : Coord) := by
  change pairIndex (4 : Fin 25) (10 : Fin 25) = (100 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_101 : pairIndex ⟨(coordinate (101 : Coord)).1, by have h := coordinate_bounds (101 : Coord); omega⟩ ⟨(coordinate (101 : Coord)).2, (coordinate_bounds (101 : Coord)).2⟩ = (101 : Coord) := by
  change pairIndex (4 : Fin 25) (11 : Fin 25) = (101 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_102 : pairIndex ⟨(coordinate (102 : Coord)).1, by have h := coordinate_bounds (102 : Coord); omega⟩ ⟨(coordinate (102 : Coord)).2, (coordinate_bounds (102 : Coord)).2⟩ = (102 : Coord) := by
  change pairIndex (4 : Fin 25) (12 : Fin 25) = (102 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_103 : pairIndex ⟨(coordinate (103 : Coord)).1, by have h := coordinate_bounds (103 : Coord); omega⟩ ⟨(coordinate (103 : Coord)).2, (coordinate_bounds (103 : Coord)).2⟩ = (103 : Coord) := by
  change pairIndex (4 : Fin 25) (13 : Fin 25) = (103 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_104 : pairIndex ⟨(coordinate (104 : Coord)).1, by have h := coordinate_bounds (104 : Coord); omega⟩ ⟨(coordinate (104 : Coord)).2, (coordinate_bounds (104 : Coord)).2⟩ = (104 : Coord) := by
  change pairIndex (4 : Fin 25) (14 : Fin 25) = (104 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_105 : pairIndex ⟨(coordinate (105 : Coord)).1, by have h := coordinate_bounds (105 : Coord); omega⟩ ⟨(coordinate (105 : Coord)).2, (coordinate_bounds (105 : Coord)).2⟩ = (105 : Coord) := by
  change pairIndex (4 : Fin 25) (15 : Fin 25) = (105 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_106 : pairIndex ⟨(coordinate (106 : Coord)).1, by have h := coordinate_bounds (106 : Coord); omega⟩ ⟨(coordinate (106 : Coord)).2, (coordinate_bounds (106 : Coord)).2⟩ = (106 : Coord) := by
  change pairIndex (4 : Fin 25) (16 : Fin 25) = (106 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_107 : pairIndex ⟨(coordinate (107 : Coord)).1, by have h := coordinate_bounds (107 : Coord); omega⟩ ⟨(coordinate (107 : Coord)).2, (coordinate_bounds (107 : Coord)).2⟩ = (107 : Coord) := by
  change pairIndex (4 : Fin 25) (17 : Fin 25) = (107 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_108 : pairIndex ⟨(coordinate (108 : Coord)).1, by have h := coordinate_bounds (108 : Coord); omega⟩ ⟨(coordinate (108 : Coord)).2, (coordinate_bounds (108 : Coord)).2⟩ = (108 : Coord) := by
  change pairIndex (4 : Fin 25) (18 : Fin 25) = (108 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_109 : pairIndex ⟨(coordinate (109 : Coord)).1, by have h := coordinate_bounds (109 : Coord); omega⟩ ⟨(coordinate (109 : Coord)).2, (coordinate_bounds (109 : Coord)).2⟩ = (109 : Coord) := by
  change pairIndex (4 : Fin 25) (19 : Fin 25) = (109 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_110 : pairIndex ⟨(coordinate (110 : Coord)).1, by have h := coordinate_bounds (110 : Coord); omega⟩ ⟨(coordinate (110 : Coord)).2, (coordinate_bounds (110 : Coord)).2⟩ = (110 : Coord) := by
  change pairIndex (4 : Fin 25) (20 : Fin 25) = (110 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_111 : pairIndex ⟨(coordinate (111 : Coord)).1, by have h := coordinate_bounds (111 : Coord); omega⟩ ⟨(coordinate (111 : Coord)).2, (coordinate_bounds (111 : Coord)).2⟩ = (111 : Coord) := by
  change pairIndex (4 : Fin 25) (21 : Fin 25) = (111 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_112 : pairIndex ⟨(coordinate (112 : Coord)).1, by have h := coordinate_bounds (112 : Coord); omega⟩ ⟨(coordinate (112 : Coord)).2, (coordinate_bounds (112 : Coord)).2⟩ = (112 : Coord) := by
  change pairIndex (4 : Fin 25) (22 : Fin 25) = (112 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_113 : pairIndex ⟨(coordinate (113 : Coord)).1, by have h := coordinate_bounds (113 : Coord); omega⟩ ⟨(coordinate (113 : Coord)).2, (coordinate_bounds (113 : Coord)).2⟩ = (113 : Coord) := by
  change pairIndex (4 : Fin 25) (23 : Fin 25) = (113 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_114 : pairIndex ⟨(coordinate (114 : Coord)).1, by have h := coordinate_bounds (114 : Coord); omega⟩ ⟨(coordinate (114 : Coord)).2, (coordinate_bounds (114 : Coord)).2⟩ = (114 : Coord) := by
  change pairIndex (4 : Fin 25) (24 : Fin 25) = (114 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_115 : pairIndex ⟨(coordinate (115 : Coord)).1, by have h := coordinate_bounds (115 : Coord); omega⟩ ⟨(coordinate (115 : Coord)).2, (coordinate_bounds (115 : Coord)).2⟩ = (115 : Coord) := by
  change pairIndex (5 : Fin 25) (5 : Fin 25) = (115 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_116 : pairIndex ⟨(coordinate (116 : Coord)).1, by have h := coordinate_bounds (116 : Coord); omega⟩ ⟨(coordinate (116 : Coord)).2, (coordinate_bounds (116 : Coord)).2⟩ = (116 : Coord) := by
  change pairIndex (5 : Fin 25) (6 : Fin 25) = (116 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_117 : pairIndex ⟨(coordinate (117 : Coord)).1, by have h := coordinate_bounds (117 : Coord); omega⟩ ⟨(coordinate (117 : Coord)).2, (coordinate_bounds (117 : Coord)).2⟩ = (117 : Coord) := by
  change pairIndex (5 : Fin 25) (7 : Fin 25) = (117 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_118 : pairIndex ⟨(coordinate (118 : Coord)).1, by have h := coordinate_bounds (118 : Coord); omega⟩ ⟨(coordinate (118 : Coord)).2, (coordinate_bounds (118 : Coord)).2⟩ = (118 : Coord) := by
  change pairIndex (5 : Fin 25) (8 : Fin 25) = (118 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_119 : pairIndex ⟨(coordinate (119 : Coord)).1, by have h := coordinate_bounds (119 : Coord); omega⟩ ⟨(coordinate (119 : Coord)).2, (coordinate_bounds (119 : Coord)).2⟩ = (119 : Coord) := by
  change pairIndex (5 : Fin 25) (9 : Fin 25) = (119 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_120 : pairIndex ⟨(coordinate (120 : Coord)).1, by have h := coordinate_bounds (120 : Coord); omega⟩ ⟨(coordinate (120 : Coord)).2, (coordinate_bounds (120 : Coord)).2⟩ = (120 : Coord) := by
  change pairIndex (5 : Fin 25) (10 : Fin 25) = (120 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_121 : pairIndex ⟨(coordinate (121 : Coord)).1, by have h := coordinate_bounds (121 : Coord); omega⟩ ⟨(coordinate (121 : Coord)).2, (coordinate_bounds (121 : Coord)).2⟩ = (121 : Coord) := by
  change pairIndex (5 : Fin 25) (11 : Fin 25) = (121 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_122 : pairIndex ⟨(coordinate (122 : Coord)).1, by have h := coordinate_bounds (122 : Coord); omega⟩ ⟨(coordinate (122 : Coord)).2, (coordinate_bounds (122 : Coord)).2⟩ = (122 : Coord) := by
  change pairIndex (5 : Fin 25) (12 : Fin 25) = (122 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_123 : pairIndex ⟨(coordinate (123 : Coord)).1, by have h := coordinate_bounds (123 : Coord); omega⟩ ⟨(coordinate (123 : Coord)).2, (coordinate_bounds (123 : Coord)).2⟩ = (123 : Coord) := by
  change pairIndex (5 : Fin 25) (13 : Fin 25) = (123 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_124 : pairIndex ⟨(coordinate (124 : Coord)).1, by have h := coordinate_bounds (124 : Coord); omega⟩ ⟨(coordinate (124 : Coord)).2, (coordinate_bounds (124 : Coord)).2⟩ = (124 : Coord) := by
  change pairIndex (5 : Fin 25) (14 : Fin 25) = (124 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_125 : pairIndex ⟨(coordinate (125 : Coord)).1, by have h := coordinate_bounds (125 : Coord); omega⟩ ⟨(coordinate (125 : Coord)).2, (coordinate_bounds (125 : Coord)).2⟩ = (125 : Coord) := by
  change pairIndex (5 : Fin 25) (15 : Fin 25) = (125 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_126 : pairIndex ⟨(coordinate (126 : Coord)).1, by have h := coordinate_bounds (126 : Coord); omega⟩ ⟨(coordinate (126 : Coord)).2, (coordinate_bounds (126 : Coord)).2⟩ = (126 : Coord) := by
  change pairIndex (5 : Fin 25) (16 : Fin 25) = (126 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_127 : pairIndex ⟨(coordinate (127 : Coord)).1, by have h := coordinate_bounds (127 : Coord); omega⟩ ⟨(coordinate (127 : Coord)).2, (coordinate_bounds (127 : Coord)).2⟩ = (127 : Coord) := by
  change pairIndex (5 : Fin 25) (17 : Fin 25) = (127 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_128 : pairIndex ⟨(coordinate (128 : Coord)).1, by have h := coordinate_bounds (128 : Coord); omega⟩ ⟨(coordinate (128 : Coord)).2, (coordinate_bounds (128 : Coord)).2⟩ = (128 : Coord) := by
  change pairIndex (5 : Fin 25) (18 : Fin 25) = (128 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_129 : pairIndex ⟨(coordinate (129 : Coord)).1, by have h := coordinate_bounds (129 : Coord); omega⟩ ⟨(coordinate (129 : Coord)).2, (coordinate_bounds (129 : Coord)).2⟩ = (129 : Coord) := by
  change pairIndex (5 : Fin 25) (19 : Fin 25) = (129 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_130 : pairIndex ⟨(coordinate (130 : Coord)).1, by have h := coordinate_bounds (130 : Coord); omega⟩ ⟨(coordinate (130 : Coord)).2, (coordinate_bounds (130 : Coord)).2⟩ = (130 : Coord) := by
  change pairIndex (5 : Fin 25) (20 : Fin 25) = (130 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_131 : pairIndex ⟨(coordinate (131 : Coord)).1, by have h := coordinate_bounds (131 : Coord); omega⟩ ⟨(coordinate (131 : Coord)).2, (coordinate_bounds (131 : Coord)).2⟩ = (131 : Coord) := by
  change pairIndex (5 : Fin 25) (21 : Fin 25) = (131 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_132 : pairIndex ⟨(coordinate (132 : Coord)).1, by have h := coordinate_bounds (132 : Coord); omega⟩ ⟨(coordinate (132 : Coord)).2, (coordinate_bounds (132 : Coord)).2⟩ = (132 : Coord) := by
  change pairIndex (5 : Fin 25) (22 : Fin 25) = (132 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_133 : pairIndex ⟨(coordinate (133 : Coord)).1, by have h := coordinate_bounds (133 : Coord); omega⟩ ⟨(coordinate (133 : Coord)).2, (coordinate_bounds (133 : Coord)).2⟩ = (133 : Coord) := by
  change pairIndex (5 : Fin 25) (23 : Fin 25) = (133 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_134 : pairIndex ⟨(coordinate (134 : Coord)).1, by have h := coordinate_bounds (134 : Coord); omega⟩ ⟨(coordinate (134 : Coord)).2, (coordinate_bounds (134 : Coord)).2⟩ = (134 : Coord) := by
  change pairIndex (5 : Fin 25) (24 : Fin 25) = (134 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_135 : pairIndex ⟨(coordinate (135 : Coord)).1, by have h := coordinate_bounds (135 : Coord); omega⟩ ⟨(coordinate (135 : Coord)).2, (coordinate_bounds (135 : Coord)).2⟩ = (135 : Coord) := by
  change pairIndex (6 : Fin 25) (6 : Fin 25) = (135 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_136 : pairIndex ⟨(coordinate (136 : Coord)).1, by have h := coordinate_bounds (136 : Coord); omega⟩ ⟨(coordinate (136 : Coord)).2, (coordinate_bounds (136 : Coord)).2⟩ = (136 : Coord) := by
  change pairIndex (6 : Fin 25) (7 : Fin 25) = (136 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_137 : pairIndex ⟨(coordinate (137 : Coord)).1, by have h := coordinate_bounds (137 : Coord); omega⟩ ⟨(coordinate (137 : Coord)).2, (coordinate_bounds (137 : Coord)).2⟩ = (137 : Coord) := by
  change pairIndex (6 : Fin 25) (8 : Fin 25) = (137 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_138 : pairIndex ⟨(coordinate (138 : Coord)).1, by have h := coordinate_bounds (138 : Coord); omega⟩ ⟨(coordinate (138 : Coord)).2, (coordinate_bounds (138 : Coord)).2⟩ = (138 : Coord) := by
  change pairIndex (6 : Fin 25) (9 : Fin 25) = (138 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_139 : pairIndex ⟨(coordinate (139 : Coord)).1, by have h := coordinate_bounds (139 : Coord); omega⟩ ⟨(coordinate (139 : Coord)).2, (coordinate_bounds (139 : Coord)).2⟩ = (139 : Coord) := by
  change pairIndex (6 : Fin 25) (10 : Fin 25) = (139 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_140 : pairIndex ⟨(coordinate (140 : Coord)).1, by have h := coordinate_bounds (140 : Coord); omega⟩ ⟨(coordinate (140 : Coord)).2, (coordinate_bounds (140 : Coord)).2⟩ = (140 : Coord) := by
  change pairIndex (6 : Fin 25) (11 : Fin 25) = (140 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_141 : pairIndex ⟨(coordinate (141 : Coord)).1, by have h := coordinate_bounds (141 : Coord); omega⟩ ⟨(coordinate (141 : Coord)).2, (coordinate_bounds (141 : Coord)).2⟩ = (141 : Coord) := by
  change pairIndex (6 : Fin 25) (12 : Fin 25) = (141 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_142 : pairIndex ⟨(coordinate (142 : Coord)).1, by have h := coordinate_bounds (142 : Coord); omega⟩ ⟨(coordinate (142 : Coord)).2, (coordinate_bounds (142 : Coord)).2⟩ = (142 : Coord) := by
  change pairIndex (6 : Fin 25) (13 : Fin 25) = (142 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_143 : pairIndex ⟨(coordinate (143 : Coord)).1, by have h := coordinate_bounds (143 : Coord); omega⟩ ⟨(coordinate (143 : Coord)).2, (coordinate_bounds (143 : Coord)).2⟩ = (143 : Coord) := by
  change pairIndex (6 : Fin 25) (14 : Fin 25) = (143 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_144 : pairIndex ⟨(coordinate (144 : Coord)).1, by have h := coordinate_bounds (144 : Coord); omega⟩ ⟨(coordinate (144 : Coord)).2, (coordinate_bounds (144 : Coord)).2⟩ = (144 : Coord) := by
  change pairIndex (6 : Fin 25) (15 : Fin 25) = (144 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_145 : pairIndex ⟨(coordinate (145 : Coord)).1, by have h := coordinate_bounds (145 : Coord); omega⟩ ⟨(coordinate (145 : Coord)).2, (coordinate_bounds (145 : Coord)).2⟩ = (145 : Coord) := by
  change pairIndex (6 : Fin 25) (16 : Fin 25) = (145 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_146 : pairIndex ⟨(coordinate (146 : Coord)).1, by have h := coordinate_bounds (146 : Coord); omega⟩ ⟨(coordinate (146 : Coord)).2, (coordinate_bounds (146 : Coord)).2⟩ = (146 : Coord) := by
  change pairIndex (6 : Fin 25) (17 : Fin 25) = (146 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_147 : pairIndex ⟨(coordinate (147 : Coord)).1, by have h := coordinate_bounds (147 : Coord); omega⟩ ⟨(coordinate (147 : Coord)).2, (coordinate_bounds (147 : Coord)).2⟩ = (147 : Coord) := by
  change pairIndex (6 : Fin 25) (18 : Fin 25) = (147 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_148 : pairIndex ⟨(coordinate (148 : Coord)).1, by have h := coordinate_bounds (148 : Coord); omega⟩ ⟨(coordinate (148 : Coord)).2, (coordinate_bounds (148 : Coord)).2⟩ = (148 : Coord) := by
  change pairIndex (6 : Fin 25) (19 : Fin 25) = (148 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_149 : pairIndex ⟨(coordinate (149 : Coord)).1, by have h := coordinate_bounds (149 : Coord); omega⟩ ⟨(coordinate (149 : Coord)).2, (coordinate_bounds (149 : Coord)).2⟩ = (149 : Coord) := by
  change pairIndex (6 : Fin 25) (20 : Fin 25) = (149 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_150 : pairIndex ⟨(coordinate (150 : Coord)).1, by have h := coordinate_bounds (150 : Coord); omega⟩ ⟨(coordinate (150 : Coord)).2, (coordinate_bounds (150 : Coord)).2⟩ = (150 : Coord) := by
  change pairIndex (6 : Fin 25) (21 : Fin 25) = (150 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_151 : pairIndex ⟨(coordinate (151 : Coord)).1, by have h := coordinate_bounds (151 : Coord); omega⟩ ⟨(coordinate (151 : Coord)).2, (coordinate_bounds (151 : Coord)).2⟩ = (151 : Coord) := by
  change pairIndex (6 : Fin 25) (22 : Fin 25) = (151 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_152 : pairIndex ⟨(coordinate (152 : Coord)).1, by have h := coordinate_bounds (152 : Coord); omega⟩ ⟨(coordinate (152 : Coord)).2, (coordinate_bounds (152 : Coord)).2⟩ = (152 : Coord) := by
  change pairIndex (6 : Fin 25) (23 : Fin 25) = (152 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_153 : pairIndex ⟨(coordinate (153 : Coord)).1, by have h := coordinate_bounds (153 : Coord); omega⟩ ⟨(coordinate (153 : Coord)).2, (coordinate_bounds (153 : Coord)).2⟩ = (153 : Coord) := by
  change pairIndex (6 : Fin 25) (24 : Fin 25) = (153 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_154 : pairIndex ⟨(coordinate (154 : Coord)).1, by have h := coordinate_bounds (154 : Coord); omega⟩ ⟨(coordinate (154 : Coord)).2, (coordinate_bounds (154 : Coord)).2⟩ = (154 : Coord) := by
  change pairIndex (7 : Fin 25) (7 : Fin 25) = (154 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_155 : pairIndex ⟨(coordinate (155 : Coord)).1, by have h := coordinate_bounds (155 : Coord); omega⟩ ⟨(coordinate (155 : Coord)).2, (coordinate_bounds (155 : Coord)).2⟩ = (155 : Coord) := by
  change pairIndex (7 : Fin 25) (8 : Fin 25) = (155 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_156 : pairIndex ⟨(coordinate (156 : Coord)).1, by have h := coordinate_bounds (156 : Coord); omega⟩ ⟨(coordinate (156 : Coord)).2, (coordinate_bounds (156 : Coord)).2⟩ = (156 : Coord) := by
  change pairIndex (7 : Fin 25) (9 : Fin 25) = (156 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_157 : pairIndex ⟨(coordinate (157 : Coord)).1, by have h := coordinate_bounds (157 : Coord); omega⟩ ⟨(coordinate (157 : Coord)).2, (coordinate_bounds (157 : Coord)).2⟩ = (157 : Coord) := by
  change pairIndex (7 : Fin 25) (10 : Fin 25) = (157 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_158 : pairIndex ⟨(coordinate (158 : Coord)).1, by have h := coordinate_bounds (158 : Coord); omega⟩ ⟨(coordinate (158 : Coord)).2, (coordinate_bounds (158 : Coord)).2⟩ = (158 : Coord) := by
  change pairIndex (7 : Fin 25) (11 : Fin 25) = (158 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_159 : pairIndex ⟨(coordinate (159 : Coord)).1, by have h := coordinate_bounds (159 : Coord); omega⟩ ⟨(coordinate (159 : Coord)).2, (coordinate_bounds (159 : Coord)).2⟩ = (159 : Coord) := by
  change pairIndex (7 : Fin 25) (12 : Fin 25) = (159 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_160 : pairIndex ⟨(coordinate (160 : Coord)).1, by have h := coordinate_bounds (160 : Coord); omega⟩ ⟨(coordinate (160 : Coord)).2, (coordinate_bounds (160 : Coord)).2⟩ = (160 : Coord) := by
  change pairIndex (7 : Fin 25) (13 : Fin 25) = (160 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_161 : pairIndex ⟨(coordinate (161 : Coord)).1, by have h := coordinate_bounds (161 : Coord); omega⟩ ⟨(coordinate (161 : Coord)).2, (coordinate_bounds (161 : Coord)).2⟩ = (161 : Coord) := by
  change pairIndex (7 : Fin 25) (14 : Fin 25) = (161 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_162 : pairIndex ⟨(coordinate (162 : Coord)).1, by have h := coordinate_bounds (162 : Coord); omega⟩ ⟨(coordinate (162 : Coord)).2, (coordinate_bounds (162 : Coord)).2⟩ = (162 : Coord) := by
  change pairIndex (7 : Fin 25) (15 : Fin 25) = (162 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_163 : pairIndex ⟨(coordinate (163 : Coord)).1, by have h := coordinate_bounds (163 : Coord); omega⟩ ⟨(coordinate (163 : Coord)).2, (coordinate_bounds (163 : Coord)).2⟩ = (163 : Coord) := by
  change pairIndex (7 : Fin 25) (16 : Fin 25) = (163 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_164 : pairIndex ⟨(coordinate (164 : Coord)).1, by have h := coordinate_bounds (164 : Coord); omega⟩ ⟨(coordinate (164 : Coord)).2, (coordinate_bounds (164 : Coord)).2⟩ = (164 : Coord) := by
  change pairIndex (7 : Fin 25) (17 : Fin 25) = (164 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_165 : pairIndex ⟨(coordinate (165 : Coord)).1, by have h := coordinate_bounds (165 : Coord); omega⟩ ⟨(coordinate (165 : Coord)).2, (coordinate_bounds (165 : Coord)).2⟩ = (165 : Coord) := by
  change pairIndex (7 : Fin 25) (18 : Fin 25) = (165 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_166 : pairIndex ⟨(coordinate (166 : Coord)).1, by have h := coordinate_bounds (166 : Coord); omega⟩ ⟨(coordinate (166 : Coord)).2, (coordinate_bounds (166 : Coord)).2⟩ = (166 : Coord) := by
  change pairIndex (7 : Fin 25) (19 : Fin 25) = (166 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_167 : pairIndex ⟨(coordinate (167 : Coord)).1, by have h := coordinate_bounds (167 : Coord); omega⟩ ⟨(coordinate (167 : Coord)).2, (coordinate_bounds (167 : Coord)).2⟩ = (167 : Coord) := by
  change pairIndex (7 : Fin 25) (20 : Fin 25) = (167 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_168 : pairIndex ⟨(coordinate (168 : Coord)).1, by have h := coordinate_bounds (168 : Coord); omega⟩ ⟨(coordinate (168 : Coord)).2, (coordinate_bounds (168 : Coord)).2⟩ = (168 : Coord) := by
  change pairIndex (7 : Fin 25) (21 : Fin 25) = (168 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_169 : pairIndex ⟨(coordinate (169 : Coord)).1, by have h := coordinate_bounds (169 : Coord); omega⟩ ⟨(coordinate (169 : Coord)).2, (coordinate_bounds (169 : Coord)).2⟩ = (169 : Coord) := by
  change pairIndex (7 : Fin 25) (22 : Fin 25) = (169 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_170 : pairIndex ⟨(coordinate (170 : Coord)).1, by have h := coordinate_bounds (170 : Coord); omega⟩ ⟨(coordinate (170 : Coord)).2, (coordinate_bounds (170 : Coord)).2⟩ = (170 : Coord) := by
  change pairIndex (7 : Fin 25) (23 : Fin 25) = (170 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_171 : pairIndex ⟨(coordinate (171 : Coord)).1, by have h := coordinate_bounds (171 : Coord); omega⟩ ⟨(coordinate (171 : Coord)).2, (coordinate_bounds (171 : Coord)).2⟩ = (171 : Coord) := by
  change pairIndex (7 : Fin 25) (24 : Fin 25) = (171 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_172 : pairIndex ⟨(coordinate (172 : Coord)).1, by have h := coordinate_bounds (172 : Coord); omega⟩ ⟨(coordinate (172 : Coord)).2, (coordinate_bounds (172 : Coord)).2⟩ = (172 : Coord) := by
  change pairIndex (8 : Fin 25) (8 : Fin 25) = (172 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_173 : pairIndex ⟨(coordinate (173 : Coord)).1, by have h := coordinate_bounds (173 : Coord); omega⟩ ⟨(coordinate (173 : Coord)).2, (coordinate_bounds (173 : Coord)).2⟩ = (173 : Coord) := by
  change pairIndex (8 : Fin 25) (9 : Fin 25) = (173 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_174 : pairIndex ⟨(coordinate (174 : Coord)).1, by have h := coordinate_bounds (174 : Coord); omega⟩ ⟨(coordinate (174 : Coord)).2, (coordinate_bounds (174 : Coord)).2⟩ = (174 : Coord) := by
  change pairIndex (8 : Fin 25) (10 : Fin 25) = (174 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_175 : pairIndex ⟨(coordinate (175 : Coord)).1, by have h := coordinate_bounds (175 : Coord); omega⟩ ⟨(coordinate (175 : Coord)).2, (coordinate_bounds (175 : Coord)).2⟩ = (175 : Coord) := by
  change pairIndex (8 : Fin 25) (11 : Fin 25) = (175 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_176 : pairIndex ⟨(coordinate (176 : Coord)).1, by have h := coordinate_bounds (176 : Coord); omega⟩ ⟨(coordinate (176 : Coord)).2, (coordinate_bounds (176 : Coord)).2⟩ = (176 : Coord) := by
  change pairIndex (8 : Fin 25) (12 : Fin 25) = (176 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_177 : pairIndex ⟨(coordinate (177 : Coord)).1, by have h := coordinate_bounds (177 : Coord); omega⟩ ⟨(coordinate (177 : Coord)).2, (coordinate_bounds (177 : Coord)).2⟩ = (177 : Coord) := by
  change pairIndex (8 : Fin 25) (13 : Fin 25) = (177 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_178 : pairIndex ⟨(coordinate (178 : Coord)).1, by have h := coordinate_bounds (178 : Coord); omega⟩ ⟨(coordinate (178 : Coord)).2, (coordinate_bounds (178 : Coord)).2⟩ = (178 : Coord) := by
  change pairIndex (8 : Fin 25) (14 : Fin 25) = (178 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_179 : pairIndex ⟨(coordinate (179 : Coord)).1, by have h := coordinate_bounds (179 : Coord); omega⟩ ⟨(coordinate (179 : Coord)).2, (coordinate_bounds (179 : Coord)).2⟩ = (179 : Coord) := by
  change pairIndex (8 : Fin 25) (15 : Fin 25) = (179 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_180 : pairIndex ⟨(coordinate (180 : Coord)).1, by have h := coordinate_bounds (180 : Coord); omega⟩ ⟨(coordinate (180 : Coord)).2, (coordinate_bounds (180 : Coord)).2⟩ = (180 : Coord) := by
  change pairIndex (8 : Fin 25) (16 : Fin 25) = (180 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_181 : pairIndex ⟨(coordinate (181 : Coord)).1, by have h := coordinate_bounds (181 : Coord); omega⟩ ⟨(coordinate (181 : Coord)).2, (coordinate_bounds (181 : Coord)).2⟩ = (181 : Coord) := by
  change pairIndex (8 : Fin 25) (17 : Fin 25) = (181 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_182 : pairIndex ⟨(coordinate (182 : Coord)).1, by have h := coordinate_bounds (182 : Coord); omega⟩ ⟨(coordinate (182 : Coord)).2, (coordinate_bounds (182 : Coord)).2⟩ = (182 : Coord) := by
  change pairIndex (8 : Fin 25) (18 : Fin 25) = (182 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_183 : pairIndex ⟨(coordinate (183 : Coord)).1, by have h := coordinate_bounds (183 : Coord); omega⟩ ⟨(coordinate (183 : Coord)).2, (coordinate_bounds (183 : Coord)).2⟩ = (183 : Coord) := by
  change pairIndex (8 : Fin 25) (19 : Fin 25) = (183 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_184 : pairIndex ⟨(coordinate (184 : Coord)).1, by have h := coordinate_bounds (184 : Coord); omega⟩ ⟨(coordinate (184 : Coord)).2, (coordinate_bounds (184 : Coord)).2⟩ = (184 : Coord) := by
  change pairIndex (8 : Fin 25) (20 : Fin 25) = (184 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_185 : pairIndex ⟨(coordinate (185 : Coord)).1, by have h := coordinate_bounds (185 : Coord); omega⟩ ⟨(coordinate (185 : Coord)).2, (coordinate_bounds (185 : Coord)).2⟩ = (185 : Coord) := by
  change pairIndex (8 : Fin 25) (21 : Fin 25) = (185 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_186 : pairIndex ⟨(coordinate (186 : Coord)).1, by have h := coordinate_bounds (186 : Coord); omega⟩ ⟨(coordinate (186 : Coord)).2, (coordinate_bounds (186 : Coord)).2⟩ = (186 : Coord) := by
  change pairIndex (8 : Fin 25) (22 : Fin 25) = (186 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_187 : pairIndex ⟨(coordinate (187 : Coord)).1, by have h := coordinate_bounds (187 : Coord); omega⟩ ⟨(coordinate (187 : Coord)).2, (coordinate_bounds (187 : Coord)).2⟩ = (187 : Coord) := by
  change pairIndex (8 : Fin 25) (23 : Fin 25) = (187 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_188 : pairIndex ⟨(coordinate (188 : Coord)).1, by have h := coordinate_bounds (188 : Coord); omega⟩ ⟨(coordinate (188 : Coord)).2, (coordinate_bounds (188 : Coord)).2⟩ = (188 : Coord) := by
  change pairIndex (8 : Fin 25) (24 : Fin 25) = (188 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_189 : pairIndex ⟨(coordinate (189 : Coord)).1, by have h := coordinate_bounds (189 : Coord); omega⟩ ⟨(coordinate (189 : Coord)).2, (coordinate_bounds (189 : Coord)).2⟩ = (189 : Coord) := by
  change pairIndex (9 : Fin 25) (9 : Fin 25) = (189 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_190 : pairIndex ⟨(coordinate (190 : Coord)).1, by have h := coordinate_bounds (190 : Coord); omega⟩ ⟨(coordinate (190 : Coord)).2, (coordinate_bounds (190 : Coord)).2⟩ = (190 : Coord) := by
  change pairIndex (9 : Fin 25) (10 : Fin 25) = (190 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_191 : pairIndex ⟨(coordinate (191 : Coord)).1, by have h := coordinate_bounds (191 : Coord); omega⟩ ⟨(coordinate (191 : Coord)).2, (coordinate_bounds (191 : Coord)).2⟩ = (191 : Coord) := by
  change pairIndex (9 : Fin 25) (11 : Fin 25) = (191 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_192 : pairIndex ⟨(coordinate (192 : Coord)).1, by have h := coordinate_bounds (192 : Coord); omega⟩ ⟨(coordinate (192 : Coord)).2, (coordinate_bounds (192 : Coord)).2⟩ = (192 : Coord) := by
  change pairIndex (9 : Fin 25) (12 : Fin 25) = (192 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_193 : pairIndex ⟨(coordinate (193 : Coord)).1, by have h := coordinate_bounds (193 : Coord); omega⟩ ⟨(coordinate (193 : Coord)).2, (coordinate_bounds (193 : Coord)).2⟩ = (193 : Coord) := by
  change pairIndex (9 : Fin 25) (13 : Fin 25) = (193 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_194 : pairIndex ⟨(coordinate (194 : Coord)).1, by have h := coordinate_bounds (194 : Coord); omega⟩ ⟨(coordinate (194 : Coord)).2, (coordinate_bounds (194 : Coord)).2⟩ = (194 : Coord) := by
  change pairIndex (9 : Fin 25) (14 : Fin 25) = (194 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_195 : pairIndex ⟨(coordinate (195 : Coord)).1, by have h := coordinate_bounds (195 : Coord); omega⟩ ⟨(coordinate (195 : Coord)).2, (coordinate_bounds (195 : Coord)).2⟩ = (195 : Coord) := by
  change pairIndex (9 : Fin 25) (15 : Fin 25) = (195 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_196 : pairIndex ⟨(coordinate (196 : Coord)).1, by have h := coordinate_bounds (196 : Coord); omega⟩ ⟨(coordinate (196 : Coord)).2, (coordinate_bounds (196 : Coord)).2⟩ = (196 : Coord) := by
  change pairIndex (9 : Fin 25) (16 : Fin 25) = (196 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_197 : pairIndex ⟨(coordinate (197 : Coord)).1, by have h := coordinate_bounds (197 : Coord); omega⟩ ⟨(coordinate (197 : Coord)).2, (coordinate_bounds (197 : Coord)).2⟩ = (197 : Coord) := by
  change pairIndex (9 : Fin 25) (17 : Fin 25) = (197 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_198 : pairIndex ⟨(coordinate (198 : Coord)).1, by have h := coordinate_bounds (198 : Coord); omega⟩ ⟨(coordinate (198 : Coord)).2, (coordinate_bounds (198 : Coord)).2⟩ = (198 : Coord) := by
  change pairIndex (9 : Fin 25) (18 : Fin 25) = (198 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_199 : pairIndex ⟨(coordinate (199 : Coord)).1, by have h := coordinate_bounds (199 : Coord); omega⟩ ⟨(coordinate (199 : Coord)).2, (coordinate_bounds (199 : Coord)).2⟩ = (199 : Coord) := by
  change pairIndex (9 : Fin 25) (19 : Fin 25) = (199 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_200 : pairIndex ⟨(coordinate (200 : Coord)).1, by have h := coordinate_bounds (200 : Coord); omega⟩ ⟨(coordinate (200 : Coord)).2, (coordinate_bounds (200 : Coord)).2⟩ = (200 : Coord) := by
  change pairIndex (9 : Fin 25) (20 : Fin 25) = (200 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_201 : pairIndex ⟨(coordinate (201 : Coord)).1, by have h := coordinate_bounds (201 : Coord); omega⟩ ⟨(coordinate (201 : Coord)).2, (coordinate_bounds (201 : Coord)).2⟩ = (201 : Coord) := by
  change pairIndex (9 : Fin 25) (21 : Fin 25) = (201 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_202 : pairIndex ⟨(coordinate (202 : Coord)).1, by have h := coordinate_bounds (202 : Coord); omega⟩ ⟨(coordinate (202 : Coord)).2, (coordinate_bounds (202 : Coord)).2⟩ = (202 : Coord) := by
  change pairIndex (9 : Fin 25) (22 : Fin 25) = (202 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_203 : pairIndex ⟨(coordinate (203 : Coord)).1, by have h := coordinate_bounds (203 : Coord); omega⟩ ⟨(coordinate (203 : Coord)).2, (coordinate_bounds (203 : Coord)).2⟩ = (203 : Coord) := by
  change pairIndex (9 : Fin 25) (23 : Fin 25) = (203 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_204 : pairIndex ⟨(coordinate (204 : Coord)).1, by have h := coordinate_bounds (204 : Coord); omega⟩ ⟨(coordinate (204 : Coord)).2, (coordinate_bounds (204 : Coord)).2⟩ = (204 : Coord) := by
  change pairIndex (9 : Fin 25) (24 : Fin 25) = (204 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_205 : pairIndex ⟨(coordinate (205 : Coord)).1, by have h := coordinate_bounds (205 : Coord); omega⟩ ⟨(coordinate (205 : Coord)).2, (coordinate_bounds (205 : Coord)).2⟩ = (205 : Coord) := by
  change pairIndex (10 : Fin 25) (10 : Fin 25) = (205 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_206 : pairIndex ⟨(coordinate (206 : Coord)).1, by have h := coordinate_bounds (206 : Coord); omega⟩ ⟨(coordinate (206 : Coord)).2, (coordinate_bounds (206 : Coord)).2⟩ = (206 : Coord) := by
  change pairIndex (10 : Fin 25) (11 : Fin 25) = (206 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_207 : pairIndex ⟨(coordinate (207 : Coord)).1, by have h := coordinate_bounds (207 : Coord); omega⟩ ⟨(coordinate (207 : Coord)).2, (coordinate_bounds (207 : Coord)).2⟩ = (207 : Coord) := by
  change pairIndex (10 : Fin 25) (12 : Fin 25) = (207 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_208 : pairIndex ⟨(coordinate (208 : Coord)).1, by have h := coordinate_bounds (208 : Coord); omega⟩ ⟨(coordinate (208 : Coord)).2, (coordinate_bounds (208 : Coord)).2⟩ = (208 : Coord) := by
  change pairIndex (10 : Fin 25) (13 : Fin 25) = (208 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_209 : pairIndex ⟨(coordinate (209 : Coord)).1, by have h := coordinate_bounds (209 : Coord); omega⟩ ⟨(coordinate (209 : Coord)).2, (coordinate_bounds (209 : Coord)).2⟩ = (209 : Coord) := by
  change pairIndex (10 : Fin 25) (14 : Fin 25) = (209 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_210 : pairIndex ⟨(coordinate (210 : Coord)).1, by have h := coordinate_bounds (210 : Coord); omega⟩ ⟨(coordinate (210 : Coord)).2, (coordinate_bounds (210 : Coord)).2⟩ = (210 : Coord) := by
  change pairIndex (10 : Fin 25) (15 : Fin 25) = (210 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_211 : pairIndex ⟨(coordinate (211 : Coord)).1, by have h := coordinate_bounds (211 : Coord); omega⟩ ⟨(coordinate (211 : Coord)).2, (coordinate_bounds (211 : Coord)).2⟩ = (211 : Coord) := by
  change pairIndex (10 : Fin 25) (16 : Fin 25) = (211 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_212 : pairIndex ⟨(coordinate (212 : Coord)).1, by have h := coordinate_bounds (212 : Coord); omega⟩ ⟨(coordinate (212 : Coord)).2, (coordinate_bounds (212 : Coord)).2⟩ = (212 : Coord) := by
  change pairIndex (10 : Fin 25) (17 : Fin 25) = (212 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_213 : pairIndex ⟨(coordinate (213 : Coord)).1, by have h := coordinate_bounds (213 : Coord); omega⟩ ⟨(coordinate (213 : Coord)).2, (coordinate_bounds (213 : Coord)).2⟩ = (213 : Coord) := by
  change pairIndex (10 : Fin 25) (18 : Fin 25) = (213 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_214 : pairIndex ⟨(coordinate (214 : Coord)).1, by have h := coordinate_bounds (214 : Coord); omega⟩ ⟨(coordinate (214 : Coord)).2, (coordinate_bounds (214 : Coord)).2⟩ = (214 : Coord) := by
  change pairIndex (10 : Fin 25) (19 : Fin 25) = (214 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_215 : pairIndex ⟨(coordinate (215 : Coord)).1, by have h := coordinate_bounds (215 : Coord); omega⟩ ⟨(coordinate (215 : Coord)).2, (coordinate_bounds (215 : Coord)).2⟩ = (215 : Coord) := by
  change pairIndex (10 : Fin 25) (20 : Fin 25) = (215 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_216 : pairIndex ⟨(coordinate (216 : Coord)).1, by have h := coordinate_bounds (216 : Coord); omega⟩ ⟨(coordinate (216 : Coord)).2, (coordinate_bounds (216 : Coord)).2⟩ = (216 : Coord) := by
  change pairIndex (10 : Fin 25) (21 : Fin 25) = (216 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_217 : pairIndex ⟨(coordinate (217 : Coord)).1, by have h := coordinate_bounds (217 : Coord); omega⟩ ⟨(coordinate (217 : Coord)).2, (coordinate_bounds (217 : Coord)).2⟩ = (217 : Coord) := by
  change pairIndex (10 : Fin 25) (22 : Fin 25) = (217 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_218 : pairIndex ⟨(coordinate (218 : Coord)).1, by have h := coordinate_bounds (218 : Coord); omega⟩ ⟨(coordinate (218 : Coord)).2, (coordinate_bounds (218 : Coord)).2⟩ = (218 : Coord) := by
  change pairIndex (10 : Fin 25) (23 : Fin 25) = (218 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_219 : pairIndex ⟨(coordinate (219 : Coord)).1, by have h := coordinate_bounds (219 : Coord); omega⟩ ⟨(coordinate (219 : Coord)).2, (coordinate_bounds (219 : Coord)).2⟩ = (219 : Coord) := by
  change pairIndex (10 : Fin 25) (24 : Fin 25) = (219 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_220 : pairIndex ⟨(coordinate (220 : Coord)).1, by have h := coordinate_bounds (220 : Coord); omega⟩ ⟨(coordinate (220 : Coord)).2, (coordinate_bounds (220 : Coord)).2⟩ = (220 : Coord) := by
  change pairIndex (11 : Fin 25) (11 : Fin 25) = (220 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_221 : pairIndex ⟨(coordinate (221 : Coord)).1, by have h := coordinate_bounds (221 : Coord); omega⟩ ⟨(coordinate (221 : Coord)).2, (coordinate_bounds (221 : Coord)).2⟩ = (221 : Coord) := by
  change pairIndex (11 : Fin 25) (12 : Fin 25) = (221 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_222 : pairIndex ⟨(coordinate (222 : Coord)).1, by have h := coordinate_bounds (222 : Coord); omega⟩ ⟨(coordinate (222 : Coord)).2, (coordinate_bounds (222 : Coord)).2⟩ = (222 : Coord) := by
  change pairIndex (11 : Fin 25) (13 : Fin 25) = (222 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_223 : pairIndex ⟨(coordinate (223 : Coord)).1, by have h := coordinate_bounds (223 : Coord); omega⟩ ⟨(coordinate (223 : Coord)).2, (coordinate_bounds (223 : Coord)).2⟩ = (223 : Coord) := by
  change pairIndex (11 : Fin 25) (14 : Fin 25) = (223 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_224 : pairIndex ⟨(coordinate (224 : Coord)).1, by have h := coordinate_bounds (224 : Coord); omega⟩ ⟨(coordinate (224 : Coord)).2, (coordinate_bounds (224 : Coord)).2⟩ = (224 : Coord) := by
  change pairIndex (11 : Fin 25) (15 : Fin 25) = (224 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_225 : pairIndex ⟨(coordinate (225 : Coord)).1, by have h := coordinate_bounds (225 : Coord); omega⟩ ⟨(coordinate (225 : Coord)).2, (coordinate_bounds (225 : Coord)).2⟩ = (225 : Coord) := by
  change pairIndex (11 : Fin 25) (16 : Fin 25) = (225 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_226 : pairIndex ⟨(coordinate (226 : Coord)).1, by have h := coordinate_bounds (226 : Coord); omega⟩ ⟨(coordinate (226 : Coord)).2, (coordinate_bounds (226 : Coord)).2⟩ = (226 : Coord) := by
  change pairIndex (11 : Fin 25) (17 : Fin 25) = (226 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_227 : pairIndex ⟨(coordinate (227 : Coord)).1, by have h := coordinate_bounds (227 : Coord); omega⟩ ⟨(coordinate (227 : Coord)).2, (coordinate_bounds (227 : Coord)).2⟩ = (227 : Coord) := by
  change pairIndex (11 : Fin 25) (18 : Fin 25) = (227 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_228 : pairIndex ⟨(coordinate (228 : Coord)).1, by have h := coordinate_bounds (228 : Coord); omega⟩ ⟨(coordinate (228 : Coord)).2, (coordinate_bounds (228 : Coord)).2⟩ = (228 : Coord) := by
  change pairIndex (11 : Fin 25) (19 : Fin 25) = (228 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_229 : pairIndex ⟨(coordinate (229 : Coord)).1, by have h := coordinate_bounds (229 : Coord); omega⟩ ⟨(coordinate (229 : Coord)).2, (coordinate_bounds (229 : Coord)).2⟩ = (229 : Coord) := by
  change pairIndex (11 : Fin 25) (20 : Fin 25) = (229 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_230 : pairIndex ⟨(coordinate (230 : Coord)).1, by have h := coordinate_bounds (230 : Coord); omega⟩ ⟨(coordinate (230 : Coord)).2, (coordinate_bounds (230 : Coord)).2⟩ = (230 : Coord) := by
  change pairIndex (11 : Fin 25) (21 : Fin 25) = (230 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_231 : pairIndex ⟨(coordinate (231 : Coord)).1, by have h := coordinate_bounds (231 : Coord); omega⟩ ⟨(coordinate (231 : Coord)).2, (coordinate_bounds (231 : Coord)).2⟩ = (231 : Coord) := by
  change pairIndex (11 : Fin 25) (22 : Fin 25) = (231 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_232 : pairIndex ⟨(coordinate (232 : Coord)).1, by have h := coordinate_bounds (232 : Coord); omega⟩ ⟨(coordinate (232 : Coord)).2, (coordinate_bounds (232 : Coord)).2⟩ = (232 : Coord) := by
  change pairIndex (11 : Fin 25) (23 : Fin 25) = (232 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_233 : pairIndex ⟨(coordinate (233 : Coord)).1, by have h := coordinate_bounds (233 : Coord); omega⟩ ⟨(coordinate (233 : Coord)).2, (coordinate_bounds (233 : Coord)).2⟩ = (233 : Coord) := by
  change pairIndex (11 : Fin 25) (24 : Fin 25) = (233 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_234 : pairIndex ⟨(coordinate (234 : Coord)).1, by have h := coordinate_bounds (234 : Coord); omega⟩ ⟨(coordinate (234 : Coord)).2, (coordinate_bounds (234 : Coord)).2⟩ = (234 : Coord) := by
  change pairIndex (12 : Fin 25) (12 : Fin 25) = (234 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_235 : pairIndex ⟨(coordinate (235 : Coord)).1, by have h := coordinate_bounds (235 : Coord); omega⟩ ⟨(coordinate (235 : Coord)).2, (coordinate_bounds (235 : Coord)).2⟩ = (235 : Coord) := by
  change pairIndex (12 : Fin 25) (13 : Fin 25) = (235 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_236 : pairIndex ⟨(coordinate (236 : Coord)).1, by have h := coordinate_bounds (236 : Coord); omega⟩ ⟨(coordinate (236 : Coord)).2, (coordinate_bounds (236 : Coord)).2⟩ = (236 : Coord) := by
  change pairIndex (12 : Fin 25) (14 : Fin 25) = (236 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_237 : pairIndex ⟨(coordinate (237 : Coord)).1, by have h := coordinate_bounds (237 : Coord); omega⟩ ⟨(coordinate (237 : Coord)).2, (coordinate_bounds (237 : Coord)).2⟩ = (237 : Coord) := by
  change pairIndex (12 : Fin 25) (15 : Fin 25) = (237 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_238 : pairIndex ⟨(coordinate (238 : Coord)).1, by have h := coordinate_bounds (238 : Coord); omega⟩ ⟨(coordinate (238 : Coord)).2, (coordinate_bounds (238 : Coord)).2⟩ = (238 : Coord) := by
  change pairIndex (12 : Fin 25) (16 : Fin 25) = (238 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_239 : pairIndex ⟨(coordinate (239 : Coord)).1, by have h := coordinate_bounds (239 : Coord); omega⟩ ⟨(coordinate (239 : Coord)).2, (coordinate_bounds (239 : Coord)).2⟩ = (239 : Coord) := by
  change pairIndex (12 : Fin 25) (17 : Fin 25) = (239 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_240 : pairIndex ⟨(coordinate (240 : Coord)).1, by have h := coordinate_bounds (240 : Coord); omega⟩ ⟨(coordinate (240 : Coord)).2, (coordinate_bounds (240 : Coord)).2⟩ = (240 : Coord) := by
  change pairIndex (12 : Fin 25) (18 : Fin 25) = (240 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_241 : pairIndex ⟨(coordinate (241 : Coord)).1, by have h := coordinate_bounds (241 : Coord); omega⟩ ⟨(coordinate (241 : Coord)).2, (coordinate_bounds (241 : Coord)).2⟩ = (241 : Coord) := by
  change pairIndex (12 : Fin 25) (19 : Fin 25) = (241 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_242 : pairIndex ⟨(coordinate (242 : Coord)).1, by have h := coordinate_bounds (242 : Coord); omega⟩ ⟨(coordinate (242 : Coord)).2, (coordinate_bounds (242 : Coord)).2⟩ = (242 : Coord) := by
  change pairIndex (12 : Fin 25) (20 : Fin 25) = (242 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_243 : pairIndex ⟨(coordinate (243 : Coord)).1, by have h := coordinate_bounds (243 : Coord); omega⟩ ⟨(coordinate (243 : Coord)).2, (coordinate_bounds (243 : Coord)).2⟩ = (243 : Coord) := by
  change pairIndex (12 : Fin 25) (21 : Fin 25) = (243 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_244 : pairIndex ⟨(coordinate (244 : Coord)).1, by have h := coordinate_bounds (244 : Coord); omega⟩ ⟨(coordinate (244 : Coord)).2, (coordinate_bounds (244 : Coord)).2⟩ = (244 : Coord) := by
  change pairIndex (12 : Fin 25) (22 : Fin 25) = (244 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_245 : pairIndex ⟨(coordinate (245 : Coord)).1, by have h := coordinate_bounds (245 : Coord); omega⟩ ⟨(coordinate (245 : Coord)).2, (coordinate_bounds (245 : Coord)).2⟩ = (245 : Coord) := by
  change pairIndex (12 : Fin 25) (23 : Fin 25) = (245 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_246 : pairIndex ⟨(coordinate (246 : Coord)).1, by have h := coordinate_bounds (246 : Coord); omega⟩ ⟨(coordinate (246 : Coord)).2, (coordinate_bounds (246 : Coord)).2⟩ = (246 : Coord) := by
  change pairIndex (12 : Fin 25) (24 : Fin 25) = (246 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_247 : pairIndex ⟨(coordinate (247 : Coord)).1, by have h := coordinate_bounds (247 : Coord); omega⟩ ⟨(coordinate (247 : Coord)).2, (coordinate_bounds (247 : Coord)).2⟩ = (247 : Coord) := by
  change pairIndex (13 : Fin 25) (13 : Fin 25) = (247 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_248 : pairIndex ⟨(coordinate (248 : Coord)).1, by have h := coordinate_bounds (248 : Coord); omega⟩ ⟨(coordinate (248 : Coord)).2, (coordinate_bounds (248 : Coord)).2⟩ = (248 : Coord) := by
  change pairIndex (13 : Fin 25) (14 : Fin 25) = (248 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_249 : pairIndex ⟨(coordinate (249 : Coord)).1, by have h := coordinate_bounds (249 : Coord); omega⟩ ⟨(coordinate (249 : Coord)).2, (coordinate_bounds (249 : Coord)).2⟩ = (249 : Coord) := by
  change pairIndex (13 : Fin 25) (15 : Fin 25) = (249 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_250 : pairIndex ⟨(coordinate (250 : Coord)).1, by have h := coordinate_bounds (250 : Coord); omega⟩ ⟨(coordinate (250 : Coord)).2, (coordinate_bounds (250 : Coord)).2⟩ = (250 : Coord) := by
  change pairIndex (13 : Fin 25) (16 : Fin 25) = (250 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_251 : pairIndex ⟨(coordinate (251 : Coord)).1, by have h := coordinate_bounds (251 : Coord); omega⟩ ⟨(coordinate (251 : Coord)).2, (coordinate_bounds (251 : Coord)).2⟩ = (251 : Coord) := by
  change pairIndex (13 : Fin 25) (17 : Fin 25) = (251 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_252 : pairIndex ⟨(coordinate (252 : Coord)).1, by have h := coordinate_bounds (252 : Coord); omega⟩ ⟨(coordinate (252 : Coord)).2, (coordinate_bounds (252 : Coord)).2⟩ = (252 : Coord) := by
  change pairIndex (13 : Fin 25) (18 : Fin 25) = (252 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_253 : pairIndex ⟨(coordinate (253 : Coord)).1, by have h := coordinate_bounds (253 : Coord); omega⟩ ⟨(coordinate (253 : Coord)).2, (coordinate_bounds (253 : Coord)).2⟩ = (253 : Coord) := by
  change pairIndex (13 : Fin 25) (19 : Fin 25) = (253 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_254 : pairIndex ⟨(coordinate (254 : Coord)).1, by have h := coordinate_bounds (254 : Coord); omega⟩ ⟨(coordinate (254 : Coord)).2, (coordinate_bounds (254 : Coord)).2⟩ = (254 : Coord) := by
  change pairIndex (13 : Fin 25) (20 : Fin 25) = (254 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_255 : pairIndex ⟨(coordinate (255 : Coord)).1, by have h := coordinate_bounds (255 : Coord); omega⟩ ⟨(coordinate (255 : Coord)).2, (coordinate_bounds (255 : Coord)).2⟩ = (255 : Coord) := by
  change pairIndex (13 : Fin 25) (21 : Fin 25) = (255 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_256 : pairIndex ⟨(coordinate (256 : Coord)).1, by have h := coordinate_bounds (256 : Coord); omega⟩ ⟨(coordinate (256 : Coord)).2, (coordinate_bounds (256 : Coord)).2⟩ = (256 : Coord) := by
  change pairIndex (13 : Fin 25) (22 : Fin 25) = (256 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_257 : pairIndex ⟨(coordinate (257 : Coord)).1, by have h := coordinate_bounds (257 : Coord); omega⟩ ⟨(coordinate (257 : Coord)).2, (coordinate_bounds (257 : Coord)).2⟩ = (257 : Coord) := by
  change pairIndex (13 : Fin 25) (23 : Fin 25) = (257 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_258 : pairIndex ⟨(coordinate (258 : Coord)).1, by have h := coordinate_bounds (258 : Coord); omega⟩ ⟨(coordinate (258 : Coord)).2, (coordinate_bounds (258 : Coord)).2⟩ = (258 : Coord) := by
  change pairIndex (13 : Fin 25) (24 : Fin 25) = (258 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_259 : pairIndex ⟨(coordinate (259 : Coord)).1, by have h := coordinate_bounds (259 : Coord); omega⟩ ⟨(coordinate (259 : Coord)).2, (coordinate_bounds (259 : Coord)).2⟩ = (259 : Coord) := by
  change pairIndex (14 : Fin 25) (14 : Fin 25) = (259 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_260 : pairIndex ⟨(coordinate (260 : Coord)).1, by have h := coordinate_bounds (260 : Coord); omega⟩ ⟨(coordinate (260 : Coord)).2, (coordinate_bounds (260 : Coord)).2⟩ = (260 : Coord) := by
  change pairIndex (14 : Fin 25) (15 : Fin 25) = (260 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_261 : pairIndex ⟨(coordinate (261 : Coord)).1, by have h := coordinate_bounds (261 : Coord); omega⟩ ⟨(coordinate (261 : Coord)).2, (coordinate_bounds (261 : Coord)).2⟩ = (261 : Coord) := by
  change pairIndex (14 : Fin 25) (16 : Fin 25) = (261 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_262 : pairIndex ⟨(coordinate (262 : Coord)).1, by have h := coordinate_bounds (262 : Coord); omega⟩ ⟨(coordinate (262 : Coord)).2, (coordinate_bounds (262 : Coord)).2⟩ = (262 : Coord) := by
  change pairIndex (14 : Fin 25) (17 : Fin 25) = (262 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_263 : pairIndex ⟨(coordinate (263 : Coord)).1, by have h := coordinate_bounds (263 : Coord); omega⟩ ⟨(coordinate (263 : Coord)).2, (coordinate_bounds (263 : Coord)).2⟩ = (263 : Coord) := by
  change pairIndex (14 : Fin 25) (18 : Fin 25) = (263 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_264 : pairIndex ⟨(coordinate (264 : Coord)).1, by have h := coordinate_bounds (264 : Coord); omega⟩ ⟨(coordinate (264 : Coord)).2, (coordinate_bounds (264 : Coord)).2⟩ = (264 : Coord) := by
  change pairIndex (14 : Fin 25) (19 : Fin 25) = (264 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_265 : pairIndex ⟨(coordinate (265 : Coord)).1, by have h := coordinate_bounds (265 : Coord); omega⟩ ⟨(coordinate (265 : Coord)).2, (coordinate_bounds (265 : Coord)).2⟩ = (265 : Coord) := by
  change pairIndex (14 : Fin 25) (20 : Fin 25) = (265 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_266 : pairIndex ⟨(coordinate (266 : Coord)).1, by have h := coordinate_bounds (266 : Coord); omega⟩ ⟨(coordinate (266 : Coord)).2, (coordinate_bounds (266 : Coord)).2⟩ = (266 : Coord) := by
  change pairIndex (14 : Fin 25) (21 : Fin 25) = (266 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_267 : pairIndex ⟨(coordinate (267 : Coord)).1, by have h := coordinate_bounds (267 : Coord); omega⟩ ⟨(coordinate (267 : Coord)).2, (coordinate_bounds (267 : Coord)).2⟩ = (267 : Coord) := by
  change pairIndex (14 : Fin 25) (22 : Fin 25) = (267 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_268 : pairIndex ⟨(coordinate (268 : Coord)).1, by have h := coordinate_bounds (268 : Coord); omega⟩ ⟨(coordinate (268 : Coord)).2, (coordinate_bounds (268 : Coord)).2⟩ = (268 : Coord) := by
  change pairIndex (14 : Fin 25) (23 : Fin 25) = (268 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_269 : pairIndex ⟨(coordinate (269 : Coord)).1, by have h := coordinate_bounds (269 : Coord); omega⟩ ⟨(coordinate (269 : Coord)).2, (coordinate_bounds (269 : Coord)).2⟩ = (269 : Coord) := by
  change pairIndex (14 : Fin 25) (24 : Fin 25) = (269 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_270 : pairIndex ⟨(coordinate (270 : Coord)).1, by have h := coordinate_bounds (270 : Coord); omega⟩ ⟨(coordinate (270 : Coord)).2, (coordinate_bounds (270 : Coord)).2⟩ = (270 : Coord) := by
  change pairIndex (15 : Fin 25) (15 : Fin 25) = (270 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_271 : pairIndex ⟨(coordinate (271 : Coord)).1, by have h := coordinate_bounds (271 : Coord); omega⟩ ⟨(coordinate (271 : Coord)).2, (coordinate_bounds (271 : Coord)).2⟩ = (271 : Coord) := by
  change pairIndex (15 : Fin 25) (16 : Fin 25) = (271 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_272 : pairIndex ⟨(coordinate (272 : Coord)).1, by have h := coordinate_bounds (272 : Coord); omega⟩ ⟨(coordinate (272 : Coord)).2, (coordinate_bounds (272 : Coord)).2⟩ = (272 : Coord) := by
  change pairIndex (15 : Fin 25) (17 : Fin 25) = (272 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_273 : pairIndex ⟨(coordinate (273 : Coord)).1, by have h := coordinate_bounds (273 : Coord); omega⟩ ⟨(coordinate (273 : Coord)).2, (coordinate_bounds (273 : Coord)).2⟩ = (273 : Coord) := by
  change pairIndex (15 : Fin 25) (18 : Fin 25) = (273 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_274 : pairIndex ⟨(coordinate (274 : Coord)).1, by have h := coordinate_bounds (274 : Coord); omega⟩ ⟨(coordinate (274 : Coord)).2, (coordinate_bounds (274 : Coord)).2⟩ = (274 : Coord) := by
  change pairIndex (15 : Fin 25) (19 : Fin 25) = (274 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_275 : pairIndex ⟨(coordinate (275 : Coord)).1, by have h := coordinate_bounds (275 : Coord); omega⟩ ⟨(coordinate (275 : Coord)).2, (coordinate_bounds (275 : Coord)).2⟩ = (275 : Coord) := by
  change pairIndex (15 : Fin 25) (20 : Fin 25) = (275 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_276 : pairIndex ⟨(coordinate (276 : Coord)).1, by have h := coordinate_bounds (276 : Coord); omega⟩ ⟨(coordinate (276 : Coord)).2, (coordinate_bounds (276 : Coord)).2⟩ = (276 : Coord) := by
  change pairIndex (15 : Fin 25) (21 : Fin 25) = (276 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_277 : pairIndex ⟨(coordinate (277 : Coord)).1, by have h := coordinate_bounds (277 : Coord); omega⟩ ⟨(coordinate (277 : Coord)).2, (coordinate_bounds (277 : Coord)).2⟩ = (277 : Coord) := by
  change pairIndex (15 : Fin 25) (22 : Fin 25) = (277 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_278 : pairIndex ⟨(coordinate (278 : Coord)).1, by have h := coordinate_bounds (278 : Coord); omega⟩ ⟨(coordinate (278 : Coord)).2, (coordinate_bounds (278 : Coord)).2⟩ = (278 : Coord) := by
  change pairIndex (15 : Fin 25) (23 : Fin 25) = (278 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_279 : pairIndex ⟨(coordinate (279 : Coord)).1, by have h := coordinate_bounds (279 : Coord); omega⟩ ⟨(coordinate (279 : Coord)).2, (coordinate_bounds (279 : Coord)).2⟩ = (279 : Coord) := by
  change pairIndex (15 : Fin 25) (24 : Fin 25) = (279 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_280 : pairIndex ⟨(coordinate (280 : Coord)).1, by have h := coordinate_bounds (280 : Coord); omega⟩ ⟨(coordinate (280 : Coord)).2, (coordinate_bounds (280 : Coord)).2⟩ = (280 : Coord) := by
  change pairIndex (16 : Fin 25) (16 : Fin 25) = (280 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_281 : pairIndex ⟨(coordinate (281 : Coord)).1, by have h := coordinate_bounds (281 : Coord); omega⟩ ⟨(coordinate (281 : Coord)).2, (coordinate_bounds (281 : Coord)).2⟩ = (281 : Coord) := by
  change pairIndex (16 : Fin 25) (17 : Fin 25) = (281 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_282 : pairIndex ⟨(coordinate (282 : Coord)).1, by have h := coordinate_bounds (282 : Coord); omega⟩ ⟨(coordinate (282 : Coord)).2, (coordinate_bounds (282 : Coord)).2⟩ = (282 : Coord) := by
  change pairIndex (16 : Fin 25) (18 : Fin 25) = (282 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_283 : pairIndex ⟨(coordinate (283 : Coord)).1, by have h := coordinate_bounds (283 : Coord); omega⟩ ⟨(coordinate (283 : Coord)).2, (coordinate_bounds (283 : Coord)).2⟩ = (283 : Coord) := by
  change pairIndex (16 : Fin 25) (19 : Fin 25) = (283 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_284 : pairIndex ⟨(coordinate (284 : Coord)).1, by have h := coordinate_bounds (284 : Coord); omega⟩ ⟨(coordinate (284 : Coord)).2, (coordinate_bounds (284 : Coord)).2⟩ = (284 : Coord) := by
  change pairIndex (16 : Fin 25) (20 : Fin 25) = (284 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_285 : pairIndex ⟨(coordinate (285 : Coord)).1, by have h := coordinate_bounds (285 : Coord); omega⟩ ⟨(coordinate (285 : Coord)).2, (coordinate_bounds (285 : Coord)).2⟩ = (285 : Coord) := by
  change pairIndex (16 : Fin 25) (21 : Fin 25) = (285 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_286 : pairIndex ⟨(coordinate (286 : Coord)).1, by have h := coordinate_bounds (286 : Coord); omega⟩ ⟨(coordinate (286 : Coord)).2, (coordinate_bounds (286 : Coord)).2⟩ = (286 : Coord) := by
  change pairIndex (16 : Fin 25) (22 : Fin 25) = (286 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_287 : pairIndex ⟨(coordinate (287 : Coord)).1, by have h := coordinate_bounds (287 : Coord); omega⟩ ⟨(coordinate (287 : Coord)).2, (coordinate_bounds (287 : Coord)).2⟩ = (287 : Coord) := by
  change pairIndex (16 : Fin 25) (23 : Fin 25) = (287 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_288 : pairIndex ⟨(coordinate (288 : Coord)).1, by have h := coordinate_bounds (288 : Coord); omega⟩ ⟨(coordinate (288 : Coord)).2, (coordinate_bounds (288 : Coord)).2⟩ = (288 : Coord) := by
  change pairIndex (16 : Fin 25) (24 : Fin 25) = (288 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_289 : pairIndex ⟨(coordinate (289 : Coord)).1, by have h := coordinate_bounds (289 : Coord); omega⟩ ⟨(coordinate (289 : Coord)).2, (coordinate_bounds (289 : Coord)).2⟩ = (289 : Coord) := by
  change pairIndex (17 : Fin 25) (17 : Fin 25) = (289 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_290 : pairIndex ⟨(coordinate (290 : Coord)).1, by have h := coordinate_bounds (290 : Coord); omega⟩ ⟨(coordinate (290 : Coord)).2, (coordinate_bounds (290 : Coord)).2⟩ = (290 : Coord) := by
  change pairIndex (17 : Fin 25) (18 : Fin 25) = (290 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_291 : pairIndex ⟨(coordinate (291 : Coord)).1, by have h := coordinate_bounds (291 : Coord); omega⟩ ⟨(coordinate (291 : Coord)).2, (coordinate_bounds (291 : Coord)).2⟩ = (291 : Coord) := by
  change pairIndex (17 : Fin 25) (19 : Fin 25) = (291 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_292 : pairIndex ⟨(coordinate (292 : Coord)).1, by have h := coordinate_bounds (292 : Coord); omega⟩ ⟨(coordinate (292 : Coord)).2, (coordinate_bounds (292 : Coord)).2⟩ = (292 : Coord) := by
  change pairIndex (17 : Fin 25) (20 : Fin 25) = (292 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_293 : pairIndex ⟨(coordinate (293 : Coord)).1, by have h := coordinate_bounds (293 : Coord); omega⟩ ⟨(coordinate (293 : Coord)).2, (coordinate_bounds (293 : Coord)).2⟩ = (293 : Coord) := by
  change pairIndex (17 : Fin 25) (21 : Fin 25) = (293 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_294 : pairIndex ⟨(coordinate (294 : Coord)).1, by have h := coordinate_bounds (294 : Coord); omega⟩ ⟨(coordinate (294 : Coord)).2, (coordinate_bounds (294 : Coord)).2⟩ = (294 : Coord) := by
  change pairIndex (17 : Fin 25) (22 : Fin 25) = (294 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_295 : pairIndex ⟨(coordinate (295 : Coord)).1, by have h := coordinate_bounds (295 : Coord); omega⟩ ⟨(coordinate (295 : Coord)).2, (coordinate_bounds (295 : Coord)).2⟩ = (295 : Coord) := by
  change pairIndex (17 : Fin 25) (23 : Fin 25) = (295 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_296 : pairIndex ⟨(coordinate (296 : Coord)).1, by have h := coordinate_bounds (296 : Coord); omega⟩ ⟨(coordinate (296 : Coord)).2, (coordinate_bounds (296 : Coord)).2⟩ = (296 : Coord) := by
  change pairIndex (17 : Fin 25) (24 : Fin 25) = (296 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_297 : pairIndex ⟨(coordinate (297 : Coord)).1, by have h := coordinate_bounds (297 : Coord); omega⟩ ⟨(coordinate (297 : Coord)).2, (coordinate_bounds (297 : Coord)).2⟩ = (297 : Coord) := by
  change pairIndex (18 : Fin 25) (18 : Fin 25) = (297 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_298 : pairIndex ⟨(coordinate (298 : Coord)).1, by have h := coordinate_bounds (298 : Coord); omega⟩ ⟨(coordinate (298 : Coord)).2, (coordinate_bounds (298 : Coord)).2⟩ = (298 : Coord) := by
  change pairIndex (18 : Fin 25) (19 : Fin 25) = (298 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_299 : pairIndex ⟨(coordinate (299 : Coord)).1, by have h := coordinate_bounds (299 : Coord); omega⟩ ⟨(coordinate (299 : Coord)).2, (coordinate_bounds (299 : Coord)).2⟩ = (299 : Coord) := by
  change pairIndex (18 : Fin 25) (20 : Fin 25) = (299 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_300 : pairIndex ⟨(coordinate (300 : Coord)).1, by have h := coordinate_bounds (300 : Coord); omega⟩ ⟨(coordinate (300 : Coord)).2, (coordinate_bounds (300 : Coord)).2⟩ = (300 : Coord) := by
  change pairIndex (18 : Fin 25) (21 : Fin 25) = (300 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_301 : pairIndex ⟨(coordinate (301 : Coord)).1, by have h := coordinate_bounds (301 : Coord); omega⟩ ⟨(coordinate (301 : Coord)).2, (coordinate_bounds (301 : Coord)).2⟩ = (301 : Coord) := by
  change pairIndex (18 : Fin 25) (22 : Fin 25) = (301 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_302 : pairIndex ⟨(coordinate (302 : Coord)).1, by have h := coordinate_bounds (302 : Coord); omega⟩ ⟨(coordinate (302 : Coord)).2, (coordinate_bounds (302 : Coord)).2⟩ = (302 : Coord) := by
  change pairIndex (18 : Fin 25) (23 : Fin 25) = (302 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_303 : pairIndex ⟨(coordinate (303 : Coord)).1, by have h := coordinate_bounds (303 : Coord); omega⟩ ⟨(coordinate (303 : Coord)).2, (coordinate_bounds (303 : Coord)).2⟩ = (303 : Coord) := by
  change pairIndex (18 : Fin 25) (24 : Fin 25) = (303 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_304 : pairIndex ⟨(coordinate (304 : Coord)).1, by have h := coordinate_bounds (304 : Coord); omega⟩ ⟨(coordinate (304 : Coord)).2, (coordinate_bounds (304 : Coord)).2⟩ = (304 : Coord) := by
  change pairIndex (19 : Fin 25) (19 : Fin 25) = (304 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_305 : pairIndex ⟨(coordinate (305 : Coord)).1, by have h := coordinate_bounds (305 : Coord); omega⟩ ⟨(coordinate (305 : Coord)).2, (coordinate_bounds (305 : Coord)).2⟩ = (305 : Coord) := by
  change pairIndex (19 : Fin 25) (20 : Fin 25) = (305 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_306 : pairIndex ⟨(coordinate (306 : Coord)).1, by have h := coordinate_bounds (306 : Coord); omega⟩ ⟨(coordinate (306 : Coord)).2, (coordinate_bounds (306 : Coord)).2⟩ = (306 : Coord) := by
  change pairIndex (19 : Fin 25) (21 : Fin 25) = (306 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_307 : pairIndex ⟨(coordinate (307 : Coord)).1, by have h := coordinate_bounds (307 : Coord); omega⟩ ⟨(coordinate (307 : Coord)).2, (coordinate_bounds (307 : Coord)).2⟩ = (307 : Coord) := by
  change pairIndex (19 : Fin 25) (22 : Fin 25) = (307 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_308 : pairIndex ⟨(coordinate (308 : Coord)).1, by have h := coordinate_bounds (308 : Coord); omega⟩ ⟨(coordinate (308 : Coord)).2, (coordinate_bounds (308 : Coord)).2⟩ = (308 : Coord) := by
  change pairIndex (19 : Fin 25) (23 : Fin 25) = (308 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_309 : pairIndex ⟨(coordinate (309 : Coord)).1, by have h := coordinate_bounds (309 : Coord); omega⟩ ⟨(coordinate (309 : Coord)).2, (coordinate_bounds (309 : Coord)).2⟩ = (309 : Coord) := by
  change pairIndex (19 : Fin 25) (24 : Fin 25) = (309 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_310 : pairIndex ⟨(coordinate (310 : Coord)).1, by have h := coordinate_bounds (310 : Coord); omega⟩ ⟨(coordinate (310 : Coord)).2, (coordinate_bounds (310 : Coord)).2⟩ = (310 : Coord) := by
  change pairIndex (20 : Fin 25) (20 : Fin 25) = (310 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_311 : pairIndex ⟨(coordinate (311 : Coord)).1, by have h := coordinate_bounds (311 : Coord); omega⟩ ⟨(coordinate (311 : Coord)).2, (coordinate_bounds (311 : Coord)).2⟩ = (311 : Coord) := by
  change pairIndex (20 : Fin 25) (21 : Fin 25) = (311 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_312 : pairIndex ⟨(coordinate (312 : Coord)).1, by have h := coordinate_bounds (312 : Coord); omega⟩ ⟨(coordinate (312 : Coord)).2, (coordinate_bounds (312 : Coord)).2⟩ = (312 : Coord) := by
  change pairIndex (20 : Fin 25) (22 : Fin 25) = (312 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_313 : pairIndex ⟨(coordinate (313 : Coord)).1, by have h := coordinate_bounds (313 : Coord); omega⟩ ⟨(coordinate (313 : Coord)).2, (coordinate_bounds (313 : Coord)).2⟩ = (313 : Coord) := by
  change pairIndex (20 : Fin 25) (23 : Fin 25) = (313 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_314 : pairIndex ⟨(coordinate (314 : Coord)).1, by have h := coordinate_bounds (314 : Coord); omega⟩ ⟨(coordinate (314 : Coord)).2, (coordinate_bounds (314 : Coord)).2⟩ = (314 : Coord) := by
  change pairIndex (20 : Fin 25) (24 : Fin 25) = (314 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_315 : pairIndex ⟨(coordinate (315 : Coord)).1, by have h := coordinate_bounds (315 : Coord); omega⟩ ⟨(coordinate (315 : Coord)).2, (coordinate_bounds (315 : Coord)).2⟩ = (315 : Coord) := by
  change pairIndex (21 : Fin 25) (21 : Fin 25) = (315 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_316 : pairIndex ⟨(coordinate (316 : Coord)).1, by have h := coordinate_bounds (316 : Coord); omega⟩ ⟨(coordinate (316 : Coord)).2, (coordinate_bounds (316 : Coord)).2⟩ = (316 : Coord) := by
  change pairIndex (21 : Fin 25) (22 : Fin 25) = (316 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_317 : pairIndex ⟨(coordinate (317 : Coord)).1, by have h := coordinate_bounds (317 : Coord); omega⟩ ⟨(coordinate (317 : Coord)).2, (coordinate_bounds (317 : Coord)).2⟩ = (317 : Coord) := by
  change pairIndex (21 : Fin 25) (23 : Fin 25) = (317 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_318 : pairIndex ⟨(coordinate (318 : Coord)).1, by have h := coordinate_bounds (318 : Coord); omega⟩ ⟨(coordinate (318 : Coord)).2, (coordinate_bounds (318 : Coord)).2⟩ = (318 : Coord) := by
  change pairIndex (21 : Fin 25) (24 : Fin 25) = (318 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_319 : pairIndex ⟨(coordinate (319 : Coord)).1, by have h := coordinate_bounds (319 : Coord); omega⟩ ⟨(coordinate (319 : Coord)).2, (coordinate_bounds (319 : Coord)).2⟩ = (319 : Coord) := by
  change pairIndex (22 : Fin 25) (22 : Fin 25) = (319 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_320 : pairIndex ⟨(coordinate (320 : Coord)).1, by have h := coordinate_bounds (320 : Coord); omega⟩ ⟨(coordinate (320 : Coord)).2, (coordinate_bounds (320 : Coord)).2⟩ = (320 : Coord) := by
  change pairIndex (22 : Fin 25) (23 : Fin 25) = (320 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_321 : pairIndex ⟨(coordinate (321 : Coord)).1, by have h := coordinate_bounds (321 : Coord); omega⟩ ⟨(coordinate (321 : Coord)).2, (coordinate_bounds (321 : Coord)).2⟩ = (321 : Coord) := by
  change pairIndex (22 : Fin 25) (24 : Fin 25) = (321 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_322 : pairIndex ⟨(coordinate (322 : Coord)).1, by have h := coordinate_bounds (322 : Coord); omega⟩ ⟨(coordinate (322 : Coord)).2, (coordinate_bounds (322 : Coord)).2⟩ = (322 : Coord) := by
  change pairIndex (23 : Fin 25) (23 : Fin 25) = (322 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_323 : pairIndex ⟨(coordinate (323 : Coord)).1, by have h := coordinate_bounds (323 : Coord); omega⟩ ⟨(coordinate (323 : Coord)).2, (coordinate_bounds (323 : Coord)).2⟩ = (323 : Coord) := by
  change pairIndex (23 : Fin 25) (24 : Fin 25) = (323 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]
theorem coordinate_pairIndex_324 : pairIndex ⟨(coordinate (324 : Coord)).1, by have h := coordinate_bounds (324 : Coord); omega⟩ ⟨(coordinate (324 : Coord)).2, (coordinate_bounds (324 : Coord)).2⟩ = (324 : Coord) := by
  change pairIndex (24 : Fin 25) (24 : Fin 25) = (324 : Coord)
  apply Fin.ext
  norm_num [pairIndex, Fin.coe_ofNat_eq_mod]

theorem coordinate_pairIndex_block_0 (c : Coord) (hlo : 0 ≤ c.val) (hhi : c.val < 10) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (0 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_0
  · have hc : c = (1 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_1
  · have hc : c = (2 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_2
  · have hc : c = (3 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_3
  · have hc : c = (4 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_4
  · have hc : c = (5 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_5
  · have hc : c = (6 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_6
  · have hc : c = (7 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_7
  · have hc : c = (8 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_8
  · have hc : c = (9 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_9
theorem coordinate_pairIndex_block_1 (c : Coord) (hlo : 10 ≤ c.val) (hhi : c.val < 20) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (10 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_10
  · have hc : c = (11 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_11
  · have hc : c = (12 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_12
  · have hc : c = (13 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_13
  · have hc : c = (14 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_14
  · have hc : c = (15 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_15
  · have hc : c = (16 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_16
  · have hc : c = (17 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_17
  · have hc : c = (18 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_18
  · have hc : c = (19 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_19
theorem coordinate_pairIndex_block_2 (c : Coord) (hlo : 20 ≤ c.val) (hhi : c.val < 30) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (20 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_20
  · have hc : c = (21 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_21
  · have hc : c = (22 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_22
  · have hc : c = (23 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_23
  · have hc : c = (24 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_24
  · have hc : c = (25 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_25
  · have hc : c = (26 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_26
  · have hc : c = (27 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_27
  · have hc : c = (28 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_28
  · have hc : c = (29 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_29
theorem coordinate_pairIndex_block_3 (c : Coord) (hlo : 30 ≤ c.val) (hhi : c.val < 40) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (30 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_30
  · have hc : c = (31 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_31
  · have hc : c = (32 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_32
  · have hc : c = (33 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_33
  · have hc : c = (34 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_34
  · have hc : c = (35 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_35
  · have hc : c = (36 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_36
  · have hc : c = (37 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_37
  · have hc : c = (38 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_38
  · have hc : c = (39 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_39
theorem coordinate_pairIndex_block_4 (c : Coord) (hlo : 40 ≤ c.val) (hhi : c.val < 50) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (40 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_40
  · have hc : c = (41 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_41
  · have hc : c = (42 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_42
  · have hc : c = (43 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_43
  · have hc : c = (44 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_44
  · have hc : c = (45 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_45
  · have hc : c = (46 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_46
  · have hc : c = (47 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_47
  · have hc : c = (48 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_48
  · have hc : c = (49 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_49
theorem coordinate_pairIndex_block_5 (c : Coord) (hlo : 50 ≤ c.val) (hhi : c.val < 60) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (50 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_50
  · have hc : c = (51 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_51
  · have hc : c = (52 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_52
  · have hc : c = (53 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_53
  · have hc : c = (54 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_54
  · have hc : c = (55 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_55
  · have hc : c = (56 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_56
  · have hc : c = (57 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_57
  · have hc : c = (58 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_58
  · have hc : c = (59 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_59
theorem coordinate_pairIndex_block_6 (c : Coord) (hlo : 60 ≤ c.val) (hhi : c.val < 70) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (60 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_60
  · have hc : c = (61 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_61
  · have hc : c = (62 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_62
  · have hc : c = (63 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_63
  · have hc : c = (64 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_64
  · have hc : c = (65 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_65
  · have hc : c = (66 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_66
  · have hc : c = (67 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_67
  · have hc : c = (68 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_68
  · have hc : c = (69 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_69
theorem coordinate_pairIndex_block_7 (c : Coord) (hlo : 70 ≤ c.val) (hhi : c.val < 80) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (70 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_70
  · have hc : c = (71 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_71
  · have hc : c = (72 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_72
  · have hc : c = (73 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_73
  · have hc : c = (74 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_74
  · have hc : c = (75 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_75
  · have hc : c = (76 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_76
  · have hc : c = (77 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_77
  · have hc : c = (78 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_78
  · have hc : c = (79 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_79
theorem coordinate_pairIndex_block_8 (c : Coord) (hlo : 80 ≤ c.val) (hhi : c.val < 90) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (80 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_80
  · have hc : c = (81 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_81
  · have hc : c = (82 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_82
  · have hc : c = (83 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_83
  · have hc : c = (84 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_84
  · have hc : c = (85 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_85
  · have hc : c = (86 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_86
  · have hc : c = (87 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_87
  · have hc : c = (88 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_88
  · have hc : c = (89 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_89
theorem coordinate_pairIndex_block_9 (c : Coord) (hlo : 90 ≤ c.val) (hhi : c.val < 100) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (90 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_90
  · have hc : c = (91 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_91
  · have hc : c = (92 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_92
  · have hc : c = (93 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_93
  · have hc : c = (94 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_94
  · have hc : c = (95 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_95
  · have hc : c = (96 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_96
  · have hc : c = (97 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_97
  · have hc : c = (98 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_98
  · have hc : c = (99 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_99
theorem coordinate_pairIndex_block_10 (c : Coord) (hlo : 100 ≤ c.val) (hhi : c.val < 110) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (100 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_100
  · have hc : c = (101 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_101
  · have hc : c = (102 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_102
  · have hc : c = (103 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_103
  · have hc : c = (104 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_104
  · have hc : c = (105 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_105
  · have hc : c = (106 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_106
  · have hc : c = (107 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_107
  · have hc : c = (108 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_108
  · have hc : c = (109 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_109
theorem coordinate_pairIndex_block_11 (c : Coord) (hlo : 110 ≤ c.val) (hhi : c.val < 120) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (110 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_110
  · have hc : c = (111 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_111
  · have hc : c = (112 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_112
  · have hc : c = (113 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_113
  · have hc : c = (114 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_114
  · have hc : c = (115 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_115
  · have hc : c = (116 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_116
  · have hc : c = (117 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_117
  · have hc : c = (118 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_118
  · have hc : c = (119 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_119
theorem coordinate_pairIndex_block_12 (c : Coord) (hlo : 120 ≤ c.val) (hhi : c.val < 130) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (120 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_120
  · have hc : c = (121 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_121
  · have hc : c = (122 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_122
  · have hc : c = (123 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_123
  · have hc : c = (124 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_124
  · have hc : c = (125 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_125
  · have hc : c = (126 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_126
  · have hc : c = (127 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_127
  · have hc : c = (128 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_128
  · have hc : c = (129 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_129
theorem coordinate_pairIndex_block_13 (c : Coord) (hlo : 130 ≤ c.val) (hhi : c.val < 140) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (130 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_130
  · have hc : c = (131 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_131
  · have hc : c = (132 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_132
  · have hc : c = (133 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_133
  · have hc : c = (134 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_134
  · have hc : c = (135 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_135
  · have hc : c = (136 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_136
  · have hc : c = (137 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_137
  · have hc : c = (138 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_138
  · have hc : c = (139 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_139
theorem coordinate_pairIndex_block_14 (c : Coord) (hlo : 140 ≤ c.val) (hhi : c.val < 150) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (140 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_140
  · have hc : c = (141 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_141
  · have hc : c = (142 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_142
  · have hc : c = (143 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_143
  · have hc : c = (144 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_144
  · have hc : c = (145 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_145
  · have hc : c = (146 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_146
  · have hc : c = (147 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_147
  · have hc : c = (148 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_148
  · have hc : c = (149 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_149
theorem coordinate_pairIndex_block_15 (c : Coord) (hlo : 150 ≤ c.val) (hhi : c.val < 160) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (150 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_150
  · have hc : c = (151 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_151
  · have hc : c = (152 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_152
  · have hc : c = (153 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_153
  · have hc : c = (154 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_154
  · have hc : c = (155 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_155
  · have hc : c = (156 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_156
  · have hc : c = (157 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_157
  · have hc : c = (158 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_158
  · have hc : c = (159 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_159
theorem coordinate_pairIndex_block_16 (c : Coord) (hlo : 160 ≤ c.val) (hhi : c.val < 170) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (160 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_160
  · have hc : c = (161 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_161
  · have hc : c = (162 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_162
  · have hc : c = (163 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_163
  · have hc : c = (164 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_164
  · have hc : c = (165 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_165
  · have hc : c = (166 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_166
  · have hc : c = (167 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_167
  · have hc : c = (168 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_168
  · have hc : c = (169 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_169
theorem coordinate_pairIndex_block_17 (c : Coord) (hlo : 170 ≤ c.val) (hhi : c.val < 180) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (170 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_170
  · have hc : c = (171 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_171
  · have hc : c = (172 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_172
  · have hc : c = (173 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_173
  · have hc : c = (174 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_174
  · have hc : c = (175 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_175
  · have hc : c = (176 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_176
  · have hc : c = (177 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_177
  · have hc : c = (178 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_178
  · have hc : c = (179 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_179
theorem coordinate_pairIndex_block_18 (c : Coord) (hlo : 180 ≤ c.val) (hhi : c.val < 190) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (180 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_180
  · have hc : c = (181 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_181
  · have hc : c = (182 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_182
  · have hc : c = (183 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_183
  · have hc : c = (184 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_184
  · have hc : c = (185 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_185
  · have hc : c = (186 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_186
  · have hc : c = (187 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_187
  · have hc : c = (188 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_188
  · have hc : c = (189 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_189
theorem coordinate_pairIndex_block_19 (c : Coord) (hlo : 190 ≤ c.val) (hhi : c.val < 200) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (190 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_190
  · have hc : c = (191 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_191
  · have hc : c = (192 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_192
  · have hc : c = (193 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_193
  · have hc : c = (194 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_194
  · have hc : c = (195 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_195
  · have hc : c = (196 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_196
  · have hc : c = (197 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_197
  · have hc : c = (198 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_198
  · have hc : c = (199 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_199
theorem coordinate_pairIndex_block_20 (c : Coord) (hlo : 200 ≤ c.val) (hhi : c.val < 210) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (200 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_200
  · have hc : c = (201 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_201
  · have hc : c = (202 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_202
  · have hc : c = (203 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_203
  · have hc : c = (204 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_204
  · have hc : c = (205 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_205
  · have hc : c = (206 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_206
  · have hc : c = (207 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_207
  · have hc : c = (208 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_208
  · have hc : c = (209 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_209
theorem coordinate_pairIndex_block_21 (c : Coord) (hlo : 210 ≤ c.val) (hhi : c.val < 220) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (210 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_210
  · have hc : c = (211 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_211
  · have hc : c = (212 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_212
  · have hc : c = (213 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_213
  · have hc : c = (214 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_214
  · have hc : c = (215 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_215
  · have hc : c = (216 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_216
  · have hc : c = (217 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_217
  · have hc : c = (218 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_218
  · have hc : c = (219 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_219
theorem coordinate_pairIndex_block_22 (c : Coord) (hlo : 220 ≤ c.val) (hhi : c.val < 230) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (220 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_220
  · have hc : c = (221 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_221
  · have hc : c = (222 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_222
  · have hc : c = (223 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_223
  · have hc : c = (224 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_224
  · have hc : c = (225 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_225
  · have hc : c = (226 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_226
  · have hc : c = (227 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_227
  · have hc : c = (228 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_228
  · have hc : c = (229 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_229
theorem coordinate_pairIndex_block_23 (c : Coord) (hlo : 230 ≤ c.val) (hhi : c.val < 240) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (230 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_230
  · have hc : c = (231 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_231
  · have hc : c = (232 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_232
  · have hc : c = (233 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_233
  · have hc : c = (234 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_234
  · have hc : c = (235 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_235
  · have hc : c = (236 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_236
  · have hc : c = (237 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_237
  · have hc : c = (238 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_238
  · have hc : c = (239 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_239
theorem coordinate_pairIndex_block_24 (c : Coord) (hlo : 240 ≤ c.val) (hhi : c.val < 250) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (240 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_240
  · have hc : c = (241 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_241
  · have hc : c = (242 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_242
  · have hc : c = (243 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_243
  · have hc : c = (244 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_244
  · have hc : c = (245 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_245
  · have hc : c = (246 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_246
  · have hc : c = (247 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_247
  · have hc : c = (248 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_248
  · have hc : c = (249 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_249
theorem coordinate_pairIndex_block_25 (c : Coord) (hlo : 250 ≤ c.val) (hhi : c.val < 260) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (250 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_250
  · have hc : c = (251 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_251
  · have hc : c = (252 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_252
  · have hc : c = (253 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_253
  · have hc : c = (254 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_254
  · have hc : c = (255 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_255
  · have hc : c = (256 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_256
  · have hc : c = (257 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_257
  · have hc : c = (258 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_258
  · have hc : c = (259 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_259
theorem coordinate_pairIndex_block_26 (c : Coord) (hlo : 260 ≤ c.val) (hhi : c.val < 270) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (260 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_260
  · have hc : c = (261 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_261
  · have hc : c = (262 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_262
  · have hc : c = (263 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_263
  · have hc : c = (264 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_264
  · have hc : c = (265 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_265
  · have hc : c = (266 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_266
  · have hc : c = (267 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_267
  · have hc : c = (268 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_268
  · have hc : c = (269 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_269
theorem coordinate_pairIndex_block_27 (c : Coord) (hlo : 270 ≤ c.val) (hhi : c.val < 280) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (270 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_270
  · have hc : c = (271 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_271
  · have hc : c = (272 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_272
  · have hc : c = (273 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_273
  · have hc : c = (274 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_274
  · have hc : c = (275 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_275
  · have hc : c = (276 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_276
  · have hc : c = (277 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_277
  · have hc : c = (278 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_278
  · have hc : c = (279 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_279
theorem coordinate_pairIndex_block_28 (c : Coord) (hlo : 280 ≤ c.val) (hhi : c.val < 290) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (280 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_280
  · have hc : c = (281 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_281
  · have hc : c = (282 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_282
  · have hc : c = (283 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_283
  · have hc : c = (284 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_284
  · have hc : c = (285 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_285
  · have hc : c = (286 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_286
  · have hc : c = (287 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_287
  · have hc : c = (288 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_288
  · have hc : c = (289 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_289
theorem coordinate_pairIndex_block_29 (c : Coord) (hlo : 290 ≤ c.val) (hhi : c.val < 300) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (290 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_290
  · have hc : c = (291 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_291
  · have hc : c = (292 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_292
  · have hc : c = (293 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_293
  · have hc : c = (294 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_294
  · have hc : c = (295 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_295
  · have hc : c = (296 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_296
  · have hc : c = (297 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_297
  · have hc : c = (298 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_298
  · have hc : c = (299 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_299
theorem coordinate_pairIndex_block_30 (c : Coord) (hlo : 300 ≤ c.val) (hhi : c.val < 310) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (300 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_300
  · have hc : c = (301 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_301
  · have hc : c = (302 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_302
  · have hc : c = (303 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_303
  · have hc : c = (304 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_304
  · have hc : c = (305 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_305
  · have hc : c = (306 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_306
  · have hc : c = (307 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_307
  · have hc : c = (308 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_308
  · have hc : c = (309 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_309
theorem coordinate_pairIndex_block_31 (c : Coord) (hlo : 310 ≤ c.val) (hhi : c.val < 320) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (310 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_310
  · have hc : c = (311 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_311
  · have hc : c = (312 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_312
  · have hc : c = (313 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_313
  · have hc : c = (314 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_314
  · have hc : c = (315 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_315
  · have hc : c = (316 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_316
  · have hc : c = (317 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_317
  · have hc : c = (318 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_318
  · have hc : c = (319 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_319
theorem coordinate_pairIndex_block_32 (c : Coord) (hlo : 320 ≤ c.val) (hhi : c.val < 325) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  interval_cases hval : c.val
  · have hc : c = (320 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_320
  · have hc : c = (321 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_321
  · have hc : c = (322 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_322
  · have hc : c = (323 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_323
  · have hc : c = (324 : Coord) := Fin.ext hval
    subst c
    exact coordinate_pairIndex_324

theorem coordinate_pairIndex (c : Coord) : pairIndex ⟨(coordinate c).1, by have h := coordinate_bounds c; omega⟩ ⟨(coordinate c).2, (coordinate_bounds c).2⟩ = c := by
  by_cases h0 : c.val < 10
  · exact coordinate_pairIndex_block_0 c (by omega) h0
  by_cases h1 : c.val < 20
  · exact coordinate_pairIndex_block_1 c (by omega) h1
  by_cases h2 : c.val < 30
  · exact coordinate_pairIndex_block_2 c (by omega) h2
  by_cases h3 : c.val < 40
  · exact coordinate_pairIndex_block_3 c (by omega) h3
  by_cases h4 : c.val < 50
  · exact coordinate_pairIndex_block_4 c (by omega) h4
  by_cases h5 : c.val < 60
  · exact coordinate_pairIndex_block_5 c (by omega) h5
  by_cases h6 : c.val < 70
  · exact coordinate_pairIndex_block_6 c (by omega) h6
  by_cases h7 : c.val < 80
  · exact coordinate_pairIndex_block_7 c (by omega) h7
  by_cases h8 : c.val < 90
  · exact coordinate_pairIndex_block_8 c (by omega) h8
  by_cases h9 : c.val < 100
  · exact coordinate_pairIndex_block_9 c (by omega) h9
  by_cases h10 : c.val < 110
  · exact coordinate_pairIndex_block_10 c (by omega) h10
  by_cases h11 : c.val < 120
  · exact coordinate_pairIndex_block_11 c (by omega) h11
  by_cases h12 : c.val < 130
  · exact coordinate_pairIndex_block_12 c (by omega) h12
  by_cases h13 : c.val < 140
  · exact coordinate_pairIndex_block_13 c (by omega) h13
  by_cases h14 : c.val < 150
  · exact coordinate_pairIndex_block_14 c (by omega) h14
  by_cases h15 : c.val < 160
  · exact coordinate_pairIndex_block_15 c (by omega) h15
  by_cases h16 : c.val < 170
  · exact coordinate_pairIndex_block_16 c (by omega) h16
  by_cases h17 : c.val < 180
  · exact coordinate_pairIndex_block_17 c (by omega) h17
  by_cases h18 : c.val < 190
  · exact coordinate_pairIndex_block_18 c (by omega) h18
  by_cases h19 : c.val < 200
  · exact coordinate_pairIndex_block_19 c (by omega) h19
  by_cases h20 : c.val < 210
  · exact coordinate_pairIndex_block_20 c (by omega) h20
  by_cases h21 : c.val < 220
  · exact coordinate_pairIndex_block_21 c (by omega) h21
  by_cases h22 : c.val < 230
  · exact coordinate_pairIndex_block_22 c (by omega) h22
  by_cases h23 : c.val < 240
  · exact coordinate_pairIndex_block_23 c (by omega) h23
  by_cases h24 : c.val < 250
  · exact coordinate_pairIndex_block_24 c (by omega) h24
  by_cases h25 : c.val < 260
  · exact coordinate_pairIndex_block_25 c (by omega) h25
  by_cases h26 : c.val < 270
  · exact coordinate_pairIndex_block_26 c (by omega) h26
  by_cases h27 : c.val < 280
  · exact coordinate_pairIndex_block_27 c (by omega) h27
  by_cases h28 : c.val < 290
  · exact coordinate_pairIndex_block_28 c (by omega) h28
  by_cases h29 : c.val < 300
  · exact coordinate_pairIndex_block_29 c (by omega) h29
  by_cases h30 : c.val < 310
  · exact coordinate_pairIndex_block_30 c (by omega) h30
  by_cases h31 : c.val < 320
  · exact coordinate_pairIndex_block_31 c (by omega) h31
  exact coordinate_pairIndex_block_32 c (by omega) c.isLt

end
end ICO.SupportCoordinates
