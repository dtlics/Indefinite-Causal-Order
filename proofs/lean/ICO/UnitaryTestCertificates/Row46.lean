import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_46 : ∀ i : Fin 128,
    testRow 46 i.val = (2*(gaussianEntry 46 i.val).1, 2*(gaussianEntry 46 i.val).2) := by
  decide +kernel
theorem ann_zero_46 : ∀ b : Fin 4, annihilation 46 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_46 : 0 < qNorm (uData 46) ∧ 0 < qNorm (vData 46) := by
  decide +kernel
end ICO.UnitaryTestCertificates
