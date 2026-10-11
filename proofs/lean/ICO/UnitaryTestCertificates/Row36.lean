import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_36 : ∀ i : Fin 128,
    testRow 36 i.val = (2*(gaussianEntry 36 i.val).1, 2*(gaussianEntry 36 i.val).2) := by
  decide +kernel
theorem ann_zero_36 : ∀ b : Fin 4, annihilation 36 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_36 : 0 < qNorm (uData 36) ∧ 0 < qNorm (vData 36) := by
  decide +kernel
end ICO.UnitaryTestCertificates
