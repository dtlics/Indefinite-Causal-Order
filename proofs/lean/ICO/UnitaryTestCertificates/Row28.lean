import ICO.UnitaryTestDefinitions
namespace ICO.UnitaryTestCertificates
open ICO.ExactTensorCertificates ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem test_row_28 : ∀ i : Fin 128,
    testRow 28 i.val = (2*(gaussianEntry 28 i.val).1, 2*(gaussianEntry 28 i.val).2) := by
  decide +kernel
theorem ann_zero_28 : ∀ b : Fin 4, annihilation 28 b.val = (0,0) := by
  decide +kernel
theorem norm_pos_28 : 0 < qNorm (uData 28) ∧ 0 < qNorm (vData 28) := by
  decide +kernel
end ICO.UnitaryTestCertificates
