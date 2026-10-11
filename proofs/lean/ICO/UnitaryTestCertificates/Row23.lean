import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_23 : ∀ i : Fin 128,
    testRow 23 i.val = (2*(gaussianEntry 23 i.val).1, 2*(gaussianEntry 23 i.val).2) := by
  decide +kernel
theorem ann_zero_23 : ∀ b : Fin 4, annihilation 23 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_23 : 0 < qNorm (uData 23) ∧ 0 < qNorm (vData 23) := by
  decide +kernel
end ICO.UnitaryTestCertificates
