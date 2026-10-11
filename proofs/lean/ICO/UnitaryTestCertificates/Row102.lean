import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_102 : ∀ i : Fin 128,
    testRow 102 i.val = (2*(gaussianEntry 102 i.val).1, 2*(gaussianEntry 102 i.val).2) := by
  decide +kernel
theorem ann_zero_102 : ∀ b : Fin 4, annihilation 102 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_102 : 0 < qNorm (uData 102) ∧ 0 < qNorm (vData 102) := by
  decide +kernel
end ICO.UnitaryTestCertificates
