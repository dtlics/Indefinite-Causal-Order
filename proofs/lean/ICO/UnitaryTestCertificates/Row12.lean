import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_12 : ∀ i : Fin 128,
    testRow 12 i.val = (2*(gaussianEntry 12 i.val).1, 2*(gaussianEntry 12 i.val).2) := by
  decide +kernel
theorem ann_zero_12 : ∀ b : Fin 4, annihilation 12 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_12 : 0 < qNorm (uData 12) ∧ 0 < qNorm (vData 12) := by
  decide +kernel
end ICO.UnitaryTestCertificates
