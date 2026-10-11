import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_14 : ∀ i : Fin 128,
    testRow 14 i.val = (2*(gaussianEntry 14 i.val).1, 2*(gaussianEntry 14 i.val).2) := by
  decide +kernel
theorem ann_zero_14 : ∀ b : Fin 4, annihilation 14 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_14 : 0 < qNorm (uData 14) ∧ 0 < qNorm (vData 14) := by
  decide +kernel
end ICO.UnitaryTestCertificates
