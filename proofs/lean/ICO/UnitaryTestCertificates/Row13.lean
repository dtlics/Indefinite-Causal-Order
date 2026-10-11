import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_13 : ∀ i : Fin 128,
    testRow 13 i.val = (2*(gaussianEntry 13 i.val).1, 2*(gaussianEntry 13 i.val).2) := by
  decide +kernel
theorem ann_zero_13 : ∀ b : Fin 4, annihilation 13 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_13 : 0 < qNorm (uData 13) ∧ 0 < qNorm (vData 13) := by
  decide +kernel
end ICO.UnitaryTestCertificates
