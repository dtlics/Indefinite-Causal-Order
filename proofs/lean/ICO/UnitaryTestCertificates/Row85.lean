import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_85 : ∀ i : Fin 128,
    testRow 85 i.val = (2*(gaussianEntry 85 i.val).1, 2*(gaussianEntry 85 i.val).2) := by
  decide +kernel
theorem ann_zero_85 : ∀ b : Fin 4, annihilation 85 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_85 : 0 < qNorm (uData 85) ∧ 0 < qNorm (vData 85) := by
  decide +kernel
end ICO.UnitaryTestCertificates
