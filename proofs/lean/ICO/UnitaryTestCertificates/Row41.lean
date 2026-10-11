import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_41 : ∀ i : Fin 128,
    testRow 41 i.val = (2*(gaussianEntry 41 i.val).1, 2*(gaussianEntry 41 i.val).2) := by
  decide +kernel
theorem ann_zero_41 : ∀ b : Fin 4, annihilation 41 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_41 : 0 < qNorm (uData 41) ∧ 0 < qNorm (vData 41) := by
  decide +kernel
end ICO.UnitaryTestCertificates
