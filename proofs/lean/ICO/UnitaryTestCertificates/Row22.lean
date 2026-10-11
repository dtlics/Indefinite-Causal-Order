import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_22 : ∀ i : Fin 128,
    testRow 22 i.val = (2*(gaussianEntry 22 i.val).1, 2*(gaussianEntry 22 i.val).2) := by
  decide +kernel
theorem ann_zero_22 : ∀ b : Fin 4, annihilation 22 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_22 : 0 < qNorm (uData 22) ∧ 0 < qNorm (vData 22) := by
  decide +kernel
end ICO.UnitaryTestCertificates
